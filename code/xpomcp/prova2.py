import z3

x = z3.Real('x')

constraints = []
constraints.append(x < 2)

for c in constraints: 
    if c.decl().kind() == z3.Z3_OP_AND:
        for variable in c.children():
            print(variable.decl().name())
            for var in variable.children():
                if z3.is_const(var) and var.decl().kind() == z3.Z3_OP_UNINTERPRETED: 
                    print(var)
    else: 
        operator = c.decl().name()
        for variable in c.children():
            if z3.is_const(variable) and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED: 
                print(variable,operator)



