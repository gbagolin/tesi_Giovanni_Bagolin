from Rule import Rule
from Velocity_Regulation_Problem import Velocity_Regulation_Problem
from Tiger_Problem import Tiger_Problem

import sys
import z3
import pdb

if __name__ == "__main__":
    # parse input files
    if len(sys.argv) == 2:
        xes_log = str(sys.argv[1])
    else:
        raise FileNotFoundError("Please, provide the trace directory")
    
    problem = Tiger_Problem(xes_log=xes_log,states=["tiger left", "tiger right"], actions=["listen", "open left", "open right"])

    rule = Rule(actions = ["open left"], problem = problem)
    x1 = rule.declareVariable('x1')
    rule.addConstraint(x1 >= 1)
    rule.solve()
    
    # rule = Rule(actions = ["open right"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # rule.addConstraint(x1 >= 0)
    # rule.solve()
    
    # rule = Rule(actions = ["listen"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    # rule.addConstraint(x1 <= 0,x2 <= 1)
    # rule.solve()
    
    # problem = Velocity_Regulation_Problem(xes_log=xes_log,states=[0,1,2], actions=[0,1,2])

    # rule = Rule(actions = [0], problem = problem)
    
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    # x3 = rule.declareVariable('x3')
    # x4 = rule.declareVariable('x4')
    
    # rule.addConstraint(x1 >= 2)
    # rule.addConstraint(x4 <= 0)
    # rule.addConstraint(x2 >= 1, x3 >= 2)
    # rule.addHardConstraint(x1 >= 0.70)
    
    # rule.solve()
   
