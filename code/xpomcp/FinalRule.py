import z3

from Constraint import Constraint
from DummyVar import DummyVar

class FinalRule: 
    def __init__(self,rule_list,problem):
        self.rule_list = rule_list
        self.solver = z3.Optimize()
        self._set_attributes()
        self.problem = problem
        
    def _set_attributes(self): 
        self.variables = {}
        self.variable_sign = {}
        self.variable_state = {}
        self.variable_constraint_set = []
        self.constraints = []
        self.hard_constraint = []
        
        for rule in self.rule_list:
            self.variables |= rule.variables
            self.variable_sign |= rule.variable_sign
            self.variable_state |= rule.variable_state
            self.variable_constraint_set += rule.variable_constraint_set
            self.constraints.append(rule.constraints)
            self.hard_constraint += rule.hard_constraint
            
        for variable in self.variables:
                self.solver.add(self.variables[variable] >= 0.0)
                self.solver.add(self.variables[variable] <= 1.0)
            
        for hard_constraint in self.hard_constraint: 
            self.solver.add(hard_constraint)
    
    def add_constraint(self, *formula):
        for constraint in formula:
            self.solver.add(constraint)
            self.hard_constraint.append(constraint)

    def find_max_smt_in_rules(self): 
        print("Solving MAX-SMT problem")
        formula = None
        
        for run in range(len(self.problem.belief_in_runs)):
            for bel, belief in enumerate(self.problem.belief_in_runs[run]):
                for rule_num, rule in enumerate(self.constraints): 
                    # generate boolean var for soft constraints
                    soft = z3.Bool('b_{}_{}_{}'.format(run, bel,rule_num))
                    self.soft_constr.append(DummyVar(soft, run, bel,rule_num))
                    subrules = []
                    
                    for constraints_in_and in self.constraints: 
                        subrule = []
                        for i, constraint in enumerate(constraints_in_and): 
                            constraint.belief = belief[self.problem.states[constraint.state]]
                            subrule.append(eval(constraint.__str__(),{},self.variables))
                            
                        subrules.append(z3.And(subrule))
                    formula = z3.Or(subrules)
                    
                    if self.problem.actions_in_runs[run][bel] not in self.actions: 
                        formula = z3.Not(formula)
                    
                    self.solver.add(z3.Or(soft, formula)) 
        
            


    
        