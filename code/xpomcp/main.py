from RuleTemplate import RuleTemplate
from AtomicRule import AtomicRule
from Velocity_Regulation_Problem import Velocity_Regulation_Problem
from Tiger_Problem import Tiger_Problem

import sys
import z3
import pdb

if __name__ == "__main__":
    # parse input files
    xes_log = []
    if len(sys.argv) >= 2:
        for i in range(1,len(sys.argv)): 
            xes_log.append(str(sys.argv[i]))
    else:
        raise FileNotFoundError("Please, provide the trace directory")
    
    max_traces = None
    if len(sys.argv) == 3: 
        max_traces = int(sys.argv[2])
    
    problem = Tiger_Problem(xes_log=xes_log[0],num_traces_to_analyze = max_traces)

    rule1 = AtomicRule(actions = ["open left"], problem = problem)
    x1 = rule1.declareVariable('x1')
    rule1.addConstraint(x1 >= 1)
    #rule.solve()
    
    rule2 = AtomicRule(actions = ["open right"], problem = problem)
    x2 = rule2.declareVariable('x2')
    rule2.addConstraint(x2 >= 0)
    #rule.solve()
    
    rule3 = AtomicRule(actions = ["listen"], problem = problem)
    x3 = rule3.declareVariable('x3')
    x4 = rule3.declareVariable('x4')
    rule3.addConstraint(x3 <= 0, x4 <= 1)
    
    final_rule = RuleTemplate([rule1,rule2,rule3], problem = problem,threshold = 0.10)
    final_rule.add_constraint(x3 == x4, x1 == x2,x1 >= 0.90)
    final_rule.solve()
    
    # problem = Velocity_Regulation_Problem(xes_log=xes_log[0])

    # rule = AtomicRule(actions = [2], problem = problem)
    
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    
    # rule.addConstraint(x1 >= 0)
    # rule.addConstraint(x2 <= 2)
    # rule.addHardConstraint(x1 >= 0.90)
    
    # rule.solve()
