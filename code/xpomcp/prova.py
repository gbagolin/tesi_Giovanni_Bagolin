import z3
import re

x1 = z3.Real('x1')
x2 = z3.Real('x2')
x3 = z3.Real('x3')

beliefs = [10,20,30]
formula = x1 > 0

pattern1 = "[^\w][0-9]+"
str_formula = ""

if formula.decl().kind() != z3.Z3_OP_AND:
    str_constraint = str(formula)
    old_state = int(re.findall(pattern1,str_constraint)[0])
    new_state = beliefs[old_state]
    pos = re.search(pattern1,str_constraint)
        #pos.start() + 1 takes care of the non integer character before
    str_formula += str_constraint[:pos.start() + 1] + str(new_state) + str_constraint[pos.end():]
    str_formula += ', '
    str_formula = str_formula[:len(str_formula) - 1]

else: 
    for constraint in formula.children(): 
        str_constraint = str(constraint)
        old_state = int(re.findall(pattern1,str_constraint)[0])
        new_state = beliefs[old_state]
        pos = re.search(pattern1,str_constraint)
        #pos.start() + 1 takes care of the non integer character before
        str_formula += str_constraint[:pos.start() + 1] + str(new_state) + str_constraint[pos.end():]
        str_formula += ', '


    str_formula = str_formula[:len(str_formula) - 2]

print(str_formula)
formula = z3.And(eval(str_formula))
z3.solve(formula)


