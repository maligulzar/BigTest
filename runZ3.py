from z3 import *
s = Solver()
s.from_file(sys.argv[1])
s.check()
a = len(sys.argv)
m = s.model()
print m.eval(String('line'))
print m.eval(String('line1'))
print m.eval(String('line2'))
