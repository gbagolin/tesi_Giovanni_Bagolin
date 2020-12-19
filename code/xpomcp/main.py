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
    
    rule = Rule(actions = ["open right"], problem = problem)
    
    x1 = rule.declareVariable('x1')
    
    rule.addConstraint(x1 >= 0)
    
    rule.solve()
    
   
