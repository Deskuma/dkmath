#!/usr/bin/env python3
from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19]


def F(r, p, mod):
    s = 0
    t = 1
    for _ in range(p):
        s = (s + t) % mod
        t = (t * r) % mod
    return s


def B(r, p, mod):
    s = 0
    t = 1
    for i in range(p):
        if i == 0:
            # r^(i-1) treated as r^0 by Nat subtraction convention in Lean? Actually (0-1)=0 nat => r^0
            s = (s + 0 * 1) % mod
        else:
            # t currently r^i? easier compute pow directly
            s = (s + (i * pow(r, i - 1, mod))) % mod
    return s


cex = []
for p in PRIMES:
    for q in PRIMES:
        if q == p:
            continue
        for n in range(1, 5):
            modn = q**n
            modnp1 = q ** (n + 1)
            roots = [r for r in range(modn) if F(r, p, modn) == 0]
            for rn in roots:
                for k in range(q):
                    r1 = (rn + k * modn) % modnp1
                    b = B(r1, p, modnp1)
                    if gcd(b, modnp1) != 1:
                        cex.append((p, q, n, rn, r1, b, modnp1, gcd(b, modnp1)))
                        if len(cex) >= 20:
                            break
                if len(cex) >= 20:
                    break
            if len(cex) >= 20:
                break
        if len(cex) >= 20:
            break
    if len(cex) >= 20:
        break

if cex:
    print("Counterexamples found:")
    for t in cex:
        print(t)
else:
    print("No counterexample found in tested range.")
