"""Check the sharp lower bound for the stated uniform-cap descent cost model."""
from sympy import Rational, diff, factor, simplify, sqrt, symbols

l, alpha = symbols("l alpha", positive=True)
y = l*(2-l)
cube = Rational(3, 2)*(2+alpha)*(2+y/alpha)**2/(l*(2-l)**3)
assert factor(diff(cube, l)/(y+4*alpha*l-2*alpha)
              - 3*(alpha+2)*(2*alpha+y)/(alpha**2*l**2*(2-l)**4)) == 0
assert factor(diff(cube, alpha)/(2*alpha**2-(alpha+4)*y)
              - Rational(3, 2)*(2*alpha+y)/(alpha**3*l*(2-l)**3)) == 0
root = 3-sqrt(7)
minimum = (20+14*sqrt(7))/3
assert simplify(cube.subs({l: root, alpha: 1})-minimum) == 0

# For A*b+B/b², equality occurs at b³=2B/A.
A = 2/(2-root)+root
B = 2/(3*root*(2-root))
b = (2*B/A)**Rational(1, 3)
delta = 3*root*b
h = (1+1/(3*root*b**3))/(2-root)
loss = 1/(b*delta)+delta*h/3
assert simplify((2*h-1)*b-loss) == 0
assert simplify((b+delta/3+loss)**3-minimum) == 0
print(f"sharp scalar-budget coefficient {float(minimum**Rational(1, 3)):.10f}")
