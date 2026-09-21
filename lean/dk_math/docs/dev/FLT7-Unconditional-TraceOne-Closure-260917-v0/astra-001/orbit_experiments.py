"""Exact R17 orbit diagnostics. No floating point and no FLT existence claim.

Run from lean/dk_math with python3 docs/dev/.../astra-001/orbit_experiments.py.
Coordinates use 1, alpha, alpha^2 and alpha^3 = 2*alpha^2 + alpha - 1.
"""
from itertools import product
import sympy as sp


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def scale(n, x):
    return tuple(n * a for a in x)


def sub(x, y):
    return add(x, scale(-1, y))


def mul(x, y):
    a, b, c = x
    d, e, f = y
    return (a*d-b*f-c*e-2*c*f, a*e+b*d+b*f+c*e+c*f,
            a*f+b*e+c*d+2*b*f+2*c*e+5*c*f)


ONE = (1, 0, 0)
THETA = (-3, 1, 0)
ALPHA = (0, 1, 0)
ADD_ONE_INV = (2, -3, 1)
AXIS_UNIT_INV = (-1, 0, 1)


def power(x, n, modulus=None):
    z = ONE
    while n:
        if n & 1:
            z = mul(z, x)
        x = mul(x, x)
        if modulus:
            z = tuple(a % modulus for a in z)
            x = tuple(a % modulus for a in x)
        n //= 2
    return z


def sigma(x):
    a, b, c = x
    return (a + 2*c, -2*b - 3*c, b + c)


def norm(x):
    a, b, c = x
    return (a**3+2*a*a*b+6*a*a*c-a*b*b+a*b*c+5*a*c*c
            -b**3-2*b*b*c+b*c*c+c**3)


def theta_coords(x):
    a, b, c = x
    return (a+3*b+9*c, b+6*c, c)


def log(x):
    a, b, c = theta_coords(x)
    inv = pow(int(a) % 7, -1, 7)
    xx, yy = b*inv % 7, c*inv % 7
    return (xx, (yy-4*xx*xx) % 7)


def depth(x):
    """Exact theta division in the integral model, including all three coordinates."""
    assert x != (0, 0, 0)
    n = 0
    while theta_coords(x)[0] % 7 == 0:
        a, b, c = x
        k = (a+3*b+9*c)//7
        x = (b+3*c-2*k, c-k, -k)
        n += 1
    return n


def strip_theta(x, n):
    for _ in range(n):
        a, b, c = x
        assert (a+3*b+9*c) % 7 == 0
        k = (a+3*b+9*c)//7
        x = (b+3*c-2*k, c-k, -k)
    return x


def seventh_quotient(x, y):
    h = (0, 0, 0)
    for j in range(7):
        h = add(h, mul(power(x, 6-j), power(y, j)))
    return h


def main():
    assert mul(add(ONE, ALPHA), ADD_ONE_INV) == ONE
    assert mul(sub(ALPHA, scale(2, ONE)), AXIS_UNIT_INV) == ONE
    u = scale(-1, power(AXIS_UNIT_INV, 2))
    assert mul(power(THETA, 3), u) == (7, 0, 0)
    eps = mul(mul(ALPHA, ADD_ONE_INV), power(u, 5))
    eps1, eps2 = sigma(eps), sigma(sigma(eps))
    print('U, norm(U), log(U):', u, norm(u), log(u))
    print('epsilon01, norm(epsilon01):', eps, norm(eps))
    print('three edge classes:', log(eps), log(eps1), log(eps2))
    assert mul(mul(eps, eps1), eps2) == ONE
    print('epsilon01 * epsilon12 * epsilon20 = 1: checked')
    m = sp.Matrix([[4, 0], [1, 2]])
    assert (m**3-sp.eye(2)).applyfunc(lambda x: x % 7).is_zero_matrix
    assert (sp.eye(2)+m+m**2).applyfunc(lambda x: x % 7).is_zero_matrix
    count = 0
    for x in product(range(7), repeat=3):
        if theta_coords(x)[0] % 7:
            a, b = log(x)
            assert log(sigma(x)) == (4*a % 7, (a+2*b) % 7)
            count += 1
    print('rotation log check on all local units modulo (7):', count)
    a, b, c = sp.symbols('a b c')
    ngap = sp.factor(norm(sub(sigma((a, b, c)), (a, b, c))))
    print('norm(sigma(rho)-rho), rho=(a,b,c):', ngap)
    theta_input = (a-3*b+9*c, b-6*c, c)
    theta_rotated = tuple(sp.expand(v) for v in theta_coords(sigma(theta_input)))
    assert theta_rotated == (a-7*c, 4*b-21*c, b-5*c)
    print('symbolic rotation of theta coordinates (a,b,c):', theta_rotated)
    # All raw source orbit identities hold without any seventh-root assumption.
    for aa in (1, 2, 7):
        t = mul(mul(power(THETA, 35), power(u, 12)), (aa**14,0,0))
        s = sub((123,0,0), t)
        w = mul(mul(power(THETA,5),u),(aa**2,0,0))
        edges = [sub(sigma(s),s), sub(sigma(sigma(s)),sigma(s)),
                 sub(s,sigma(sigma(s)))]
        for edge, ee, ww in zip(edges,[eps,eps1,eps2],[w,sigma(w),sigma(sigma(w))]):
            assert edge == mul(ee,power(ww,7))
        assert add(add(*edges[:2]),edges[2]) == (0,0,0)
        assert norm(edges[0]) == 7**35 * aa**42
    print('source-only three-edge/telescope/norm diagnostics: checked A=1,2,7')
    # Trace zero and the predicted gap-core unit class are jointly consistent.
    d0 = scale(7**10, sub(sigma((0,1,1)), (0,1,1)))
    eta0 = strip_theta(d0,32)
    assert norm(eta0) == 1 and log(eta0) == (2,4)
    assert mul(power(THETA,32),eta0) == d0
    assert add(add(d0,sigma(d0)),sigma(sigma(d0))) == (0,0,0)
    twists = [eta0]
    for _ in range(2):
        twists.append(mul(power(add(ONE,ALPHA),32),sigma(twists[-1])))
    assert [log(e) for e in twists] == [(2,4),(2,2),(2,5)]
    print('trace-zero depth-32 unit-core witness:', eta0, 'class:', log(eta0))
    print('theta-stripped gap-core classes (twisted rotations):', [log(e) for e in twists])
    # A local witness with L-R=7^6, but no integer B or FLT counterexample.
    # Solve rho^7=S modulo 7^N by successive lifts starting rho=1.
    precision = 14
    target = sub((1+7**6,0,0), mul(power(THETA,35),power(u,12)))
    rho = ONE
    for k in range(2, precision):
        modulus = 7**(k+1)
        err = tuple((t-v) % modulus for t,v in zip(target,power(rho,7,modulus)))
        assert all(e % (7**k) == 0 for e in err)
        digit = tuple(e//(7**k) for e in err)
        rho = add(rho,scale(7**(k-1),digit))
        assert all((v-t) % modulus == 0 for v,t in zip(power(rho,7,modulus),target))
    d = sub(sigma(rho),rho)
    h = seventh_quotient(sigma(rho),rho)
    assert depth(d) == 32 and depth(h) == 3
    print('local witness modulo 7^14:', rho)
    print('local witness v_theta(gap), v_theta(H7):', depth(d),depth(h))
    print('Scope: finite modular witness only; no global B^7 or successor state.')


if __name__ == '__main__':
    main()
