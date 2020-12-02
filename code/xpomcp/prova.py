import z3
import re

x = z3.Real('x')
beliefs = [10,20,30]
formula = z3.And(x > 0, x < 1)

pattern = "\d+"
strFormula = ""

for constraint in formula.children(): 
    strConstraint = str(constraint)
    print(strConstraint)
    state = re.findall(pattern,strConstraint)
    strFormula += strConstraint.replace(state[0],str(beliefs[int(state[0])]))
    strFormula += ', '

strFormula = strFormula[:len(strFormula) - 2]

formula = z3.And(eval(strFormula))
z3.solve(formula)


