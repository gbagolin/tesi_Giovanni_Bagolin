import z3

class Rule:

    def __init__(self,id=None,action=None,formula = None):
        self.id = id
        self.action = action
        self.formula = formula
        self.solver = z3.Optimize()
    
    
    def declareVariable(self,variableName): 
        '''
        Return a z3 variable, which stands for a free variable, with probability constraint.
        '''
        x = z3.Real(variableName)
        self.solver.add(0.0 < x)
        self.solver.add(x <= 1.0)
        return x
    
    def addConstraint(self,*args):
        '''
        Create a z3 formula representing a constraint given a formula. 
        '''
        return z3.And(args)



         
