#!/usr/bin/env python3

# Search counterexamples to HenselLiftStepLinearizedSolveTarget
# for F(t)=sum_{i=0}^{p-1} t^i over Z/(q^(n+1)).

from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19]


def F(r, p, mod):
    s = 0
    t = 1
    for _ in range(p):
        s = (s + t) % mod
        t = (t * r) % mod
    return s


def dF(r, p, mod):
    s = 0
    t = 1
    for i in range(p):
        if i == 0:
            continue
        s = (s + i * t) % mod
        t = (t * r) % mod
    return s


def search(limit=30):
    cex = []
    for p in PRIMES:
        for q in PRIMES:
            if q == p:
                continue
            for n in range(1, 5):
                modn = q**n
                modnp1 = q ** (n + 1)
                qn = q**n
                # roots modulo q^n
                roots = [r for r in range(modn) if F(r, p, modn) == 0]
                for rn in roots:
                    # all lifts rn + k q^n
                    for k in range(q):
                        r1 = (rn + k * qn) % modnp1
                        rhs = (-F(r1, p, modnp1)) % modnp1
                        A = (dF(r1, p, modnp1) * qn) % modnp1
                        # linear solve A*c = rhs mod modnp1
                        solvable = rhs % gcd(A, modnp1) == 0
                        if not solvable:
                            cex.append((p, q, n, rn, r1, A, rhs))
                            if len(cex) >= limit:
                                return cex
    return cex


if __name__ == "__main__":
    cex = search()
    if not cex:
        print("No counterexample found in tested range.")
    else:
        print("Counterexamples:")
        for t in cex:
            print(t)
