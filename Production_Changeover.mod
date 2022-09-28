/*********************************************
 * OPL 22.1.0.0 Model
 * Author: kennethwang
 * Creation Date: Jul 31, 2022 at 11:16:00 PM
 *********************************************/

/* PARAMETERS */ 

{int} Products = ...;
{int} Factories = ...;
{int} Periods = ...;   // each time period is one week. 

int num_products = ...;
int num_factories = ...;
int num_periods = ...;

/* TUPLES */

tuple ProductProductFactoryData {
   float changeover_cost; // changeover_cost of 1 line from product p to product q at factory f
   
   int changeover_time; // number of periods to change over             						        ESTIMATE: 1-4 weeks
   
}
tuple ProductFactoryData { // data per each product p and factory f 

  
  float variable_cost; // variable cost per unit per product (ie. production cost)                   ESTIMATE: 200-400
  
  int single_line_capacity; // # of products a line can produce in one week per product               ESTIMATE: 3500-4000
  
  float area_requirement;  // area requirement per product in factory   								ESTIMATE: ???? 1000 - 1100 sq ft
  
  int starting_line_configuration; // number of lines producing this product at t=0                 ESTIMATE: 40-90 lines (per factory, all products)
		 
  int starting_product_inventory;  // # of product units already produced at factory f at t=0		ESTIMATE: ~0
  
}

tuple ProductTimeData {
  float shortage_cost; // cost of NOT meeting demand for 1 unit at period t, product p				ESTIMATE: 300-600
  
  float cumulative_demand; //cumulative demand for product through the period.  								ESTIMATE: 
  //              In other words, if customers demand 30 units in period 1, 
  // 		      20 units additional in period 2, then Demand = 30 in t=1, Demand = 50 in t=2, etc. 
}

ProductProductFactoryData productproductfactorydata[f in Factories][p in Products][q in Products] = ...; // this line initializes the tuple declared above
ProductFactoryData productfactorydata[f in Factories][p in Products] = ...; // this line initializes the tuple we declared above
ProductTimeData producttimedata[p in Products][t in Periods] = ...; // this line initializes the tuple we declared above

/* SINGLE VARIABLES */ 



float total_area[f in Factories] = ...; // the total area that each factory has. 
// This is used with ProductFactoryData.areaRequirement to constraint large lines.

int max_line_changes[f in Factories][t in Periods] = ...;  // total number of line changes per factory f in period t permitted. 
															// NOTE: This is an artificial constraint

/* ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
	Decision Variables  
*/

dvar int+ line_changes_initiated[p in Products][q in Products][f in Factories][t in -num_periods..num_periods] ; 
// y = Number of production lines changed from product p to product q at factory f that are initiated at the beginning of period t

dvar int+ units_produced[f in Factories][p in Products][t in Periods]; 
// x = # of product p produced at factory f in period t

//# Auxiliary Variables 

dvar int+ ongoing_line_switches[p in Products, f in Factories, t in Periods];
// z = # of ongoing line switches for product p in factory f at t

dvar int+ lines_assigned[p in Products][f in Factories][t in Periods]; 
// N = # of total lines assigned to product p in factory f in period t 

dvar int+ accumulated_inventory_units[p in Products, f in Factories, t in Periods];
// I = # of accumulated product inventory units per product p in factory f by period t 
// NOTE: I is an accumulated amount
// ex. if I[0][0][0] = 10, I[0][0][1] = 20 -> this implies that 10 additional units were produced from t=0 to t=1 

dvar int+ backorders[p in Products, t in Periods]; 
// B = # of backorders (across all factories) for product p in time period t 
// NOTE: This is simply the difference between the accumulated demand and the accumulated product inventory


/* OBJECTIVE FUNCTION */ 
minimize sum(t in Periods, f in Factories, p in Products, q in Products) productproductfactorydata[f][p][q].changeover_cost * line_changes_initiated[p][q][f][t] 
         + sum(p in Products, f in Factories, t in Periods) productfactorydata[f][p].variable_cost * units_produced[f][p][t]
         + sum(p in Products, t in Periods) producttimedata[p][t].shortage_cost *  backorders[p][t];
         // Objective Function: Minimize total changeover_cost and total variable production cost and total shortage cost (not meeting demand) 

/* CONSTRAINTS */ 
subject to {
  
  // *** ALL PRODUCTION RELATED CONSTRAINTS (ie. calculating line_changes_initiated, units_produced, ongoing_line_switches, lines_assigned) ***
  
  // 1. Number of lines assigned to p,f,t [calculating lines_assigned]
  		// 1a. initialization (period 1)
  forall (p in Products, f in Factories, t in Periods) lines_assigned[p][f][1] == productfactorydata[f][p].starting_line_configuration;
  		// 1b. for all other periods
  forall (p in Products, f in Factories, t in 2..num_periods) lines_assigned[p][f][t] == lines_assigned[p][f][t-1] + sum(q in Products) line_changes_initiated[q][p][f][t] - sum(q in Products) line_changes_initiated[p][q][f][t];
  
  
  // 2. Number of lines currently switching over [calculating ongoing_line_switches] 
  // 2a. Dummy periods from -num_periods to 0 are initialized to enable summation in 2b. 
  forall (p in Products, q in Products, f in Factories, t in -num_periods..0) line_changes_initiated[p][q][f][t] == 0;
  // 2b. summation
  forall (q in Products, f in Factories, t in Periods) ongoing_line_switches[q][f][t] == sum(p in Products) 
          (sum(theta in (1+t-productproductfactorydata[f][p][q].changeover_time)..num_periods) line_changes_initiated[p][q][f][theta]);

          
  // 3. Constraint to ensure units_produced per p,f,t are less than single_line_capacity * active lines 
  forall (p in Products, f in Factories, t in Periods)( units_produced[f][p][t] <= productfactorydata[f][p].single_line_capacity *
  (lines_assigned[p][f][t] - ongoing_line_switches[p][f][t])); 
  
  
  
  //  *** DEMAND RELATED CONSTRAINTS *** 
  
  // 4. Inventory Definition (I – cumulative inventory of each product since period t = 0)  
  		// 4a. Inventory initialization at t = 1
  forall (p in Products, f in Factories) accumulated_inventory_units[p][f][1] == productfactorydata[f][p].starting_product_inventory + units_produced[f][p][1];
  		// 4b. Cumulative Inventory (t > 1)
  forall (p in Products, f in Factories, t in 2..num_periods) accumulated_inventory_units[p][f][t] == accumulated_inventory_units[p][f][t-1] + units_produced[f][p][t];
  
  // 5. Backorders (cost of not meeting demand at a specific time)
  forall (p in Products, t in Periods) backorders[p][t] >= producttimedata[p][t].cumulative_demand - sum(f in Factories) accumulated_inventory_units[p][f][t];
  
  
  // *** MISC CONSTRAINTS ***
  // 6. No same product changeovers: for the same product-pair (p-p), ensure there are no changeovers. 
  forall (p in Products, f in Factories, t in Periods) line_changes_initiated[p,p,f,t] == 0;
  
  // 7. Physical area constraint: ensure lines_assigned * area_requirement <= total_area per factory, ie. area taken up by each line can physically fit in factory
  forall (f in Factories, t in Periods) sum(p in Products) (productfactorydata[f][p].area_requirement * lines_assigned[p][f][t]) <= total_area[f];
  
  // 8. Artificially limit the numer of line changes per factory. 
  forall (f in Factories, t in Periods) sum(q in Products) ongoing_line_switches[q,f,t] <= max_line_changes[f,t];
  
};









