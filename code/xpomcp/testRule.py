from Rule import Rule
from Problem import Problem
import sys
import z3
import pdb

if __name__ == "__main__":
    # parse input files
    if len(sys.argv) == 2:
        xes_log = str(sys.argv[1])
    else:
        raise FileNotFoundError("Please, provide the trace directory")
        xes_log = None
    
    problem = Problem(xes_log=xes_log,states=[0,1,2], actions=[0,1,2])

    rule = Rule(actions = [0], problem = problem)
    
    x1 = rule.declareVariable('x1')
    x2 = rule.declareVariable('x2')
    x3 = rule.declareVariable('x3')
    x4 = rule.declareVariable('x4')
    
    rule.addConstraint(x1 >= 2)
    rule.addConstraint(x2 >= 1, x3 >= 2)
    rule.addConstraint(x4 <= 0)
    
    # rule = Rule(actions = [2], problem = problem)
    
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    
    # rule.addConstraint(x2 <= 2, x1 >= 0)
    
    rule.solve()
    
    # rule = Rule(actions = [0,1], problem = problem)
    
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    # x3 = rule.declareVariable('x3')
    # x4 = rule.declareVariable('x4')
    
    # rule.addConstraint(x1 >= 2)
    # rule.addConstraint(x2 >= 1, x3 >= 2)
    # rule.addConstraint(x4 <= 0)
    
    # # x1 = rule.declareVariable('x1')
    # # x2 = rule.declareVariable('x2')
    
    # # rule.addConstraint(x2 <= 2, x1 >= 0)

   
