from Rule import Rule
from Problem import Problem
import sys

if __name__ == "__main__":
    # parse input files
    if len(sys.argv) == 2:
        xes_log = str(sys.argv[1])
    else:
        xes_log = None
    
    problem = Problem(xes_log=xes_log)
    rule = Rule(problem = problem)
    x1 = rule.declareVariable('x1')
    x2 = rule.declareVariable('x2')

    rule.addConstraint(x1 < 2)
    rule.findMaxSmtInRule()


#rule.findMaxSmtInRule()
