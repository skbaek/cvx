import sys
from cvxopt import matrix, solvers

def to_floats(s):
   "Converts string into list of floats"
   return list(map(lambda x : float(x), s.split()));

c = matrix(to_floats(sys.argv[1]))
A = matrix(list(map(lambda x : to_floats(x), sys.argv[2].splitlines())))
b = matrix(to_floats(sys.argv[3]))

solvers.options['show_progress'] = False
sol = solvers.lp(c,A,b)

print(sol['x'])