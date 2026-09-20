"""Exact symbolic reconnaissance; not a substitute for Lean certificates.

Run from any cwd with Python + SymPy. No numerical search is used as completeness.
"""

import sympy as sp

a, k, X = sp.symbols("a k X")
minimal = X**3 - 2 * X**2 - X + 1


def reduce(expr):
    return sp.rem(sp.expand(expr), minimal, X)


def rotate(expr):
    return reduce(expr.subs(X, X**2 - 2 * X))


theta = X - 3
rho = reduce(-X**3)
direction = reduce(theta**2 * rho)
b, c = sp.symbols("b c")
source_root = a + b * X + c * X**2
gap = reduce(rotate(source_root) - source_root)
solution = sp.solve(sp.Poly(gap - k * direction, X).all_coeffs(), (b, c))
print("rho (alpha basis):", rho)
print("theta^2 * rho:", direction)
print("gap equation solution:", solution)
root_on_line = source_root.subs(solution)
root_seventh = reduce(root_on_line**7)
plane_defect = sp.factor(root_seventh.coeff(X, 1) - root_seventh.coeff(X, 2))
print("source root on calibration line:", root_on_line)
print("seventh-power source-plane defect:", plane_defect)
print("inhomogeneous factorization at k=1:", sp.factor(plane_defect.subs(k, 1)))
print("exact rational roots at k=1:", sp.polys.polytools.ground_roots(plane_defect.subs(k, 1), a))

# Reconstruct the source direction from theta^35 * thetaSevenUnit^12 = 7^12/theta.
source_direction = reduce(theta**2 + 7 * theta + 14)
print("source direction (-7/theta):", source_direction)
assert reduce(theta * source_direction) == -7
assert source_direction.coeff(X, 1) == source_direction.coeff(X, 2)
