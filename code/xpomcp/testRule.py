from Rule import Rule
from Problem import Problem

rule = Rule()
problem = Problem(beliefs = 1)

x = rule.declareVariable('x')
y = rule.declareVariable('y')

constraint1 = rule.addConstraint(x < problem.beliefs)
constraint2 = rule.addConstraint(y > 2)

rule.addFormula(constraint1,constraint2)
print(rule.formula)

rule.findMaxSmtInRule()
