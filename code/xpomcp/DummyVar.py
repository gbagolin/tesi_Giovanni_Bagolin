class DummyVar:
    """
    Class that represent a dummy variable introduced by the MAX-SMT step.
    It contains the literal (a Boolean variable) that identify the dummy
    variable inside the SMT problem and the the information related to wich
    rule, run and step is codified by the variable.
    """
    def __init__(self, literal, rule, run, step):
        self.literal = literal
        self.rule = rule
        self.run = run
        self.step = step