from ActionRule import ActionRule
from FinalRule import FinalRule
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
    
    problem = Tiger_Problem(xes_log=xes_log[0],states=["tiger left", "tiger right"], actions=["listen", "open left", "open right"])

    rule = ActionRule(actions = ["open left"], problem = problem)
    x1 = rule.declareVariable('x1')
    x4 = rule.declareVariable('x4')
    rule.addConstraint(x1 >= 1)
    rule.addConstraint(x4 <= 0)
    #rule.solve()
    
    # rule = Rule(actions = ["open right"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # rule.addConstraint(x1 >= 0)
    # rule.solve()
    
    rule2 = ActionRule(actions = ["listen"], problem = problem)
    x2 = rule2.declareVariable('x2')
    x3 = rule2.declareVariable('x3')
    rule2.addConstraint(x2 <= 0,x3 <= 1)
    
    final_rule = FinalRule([rule,rule2],problem = problem)
    final_rule.add_constraint(x2 == x3)
    
    
    
    print(final_rule.variables)
    print(final_rule.constraints)
    # for constranint_list in final_rule.constraints: 
    #     for constraint in constranint_list: 
    #         print(constraint)
            
    print(final_rule.hard_constraint)
    
    # rule.solve()
    
    # problem = Velocity_Regulation_Problem(xes_log=xes_log[0],states=[0,1,2], actions=[0,1,2])

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
    
