import z3
import re

x = z3.Real('x')
beliefs = [10,20,30]
formula = z3.Or(x > 0, x < 1)
print(type(formula))
formula = str(formula)
print(formula)

pattern = "\d+"
states = re.findall(pattern, formula) 
print(states)

for state in states: 
    belief = str(beliefs[int(state)])

    print("Bel: {}".format(belief))
    print("State: {}".format(state))

    formula = formula.replace(state, belief)
    print(formula)

print(formula)


