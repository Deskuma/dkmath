#!/usr/bin/env python3
from math import gcd

QS = [2, 3, 5, 7]
PS = list(range(2, 21))


def F(r, p, mod):
    s = 0
    t = 1
    for _ in range(p):
        s = (s + t) % mod
        t = (t * r) % mod
    return s


def B(r, p, mod):
    s = 0
    for i in range(p):
        e = i - 1 if i > 0 else 0
        s = (s + i * pow(r, e, mod)) % mod
    return s


for p in PS:
    for q in QS:
        if q == p:
            continue
        for n in range(1, 4):
            modn = q**n
            modnp1 = q ** (n + 1)
            roots = [r for r in range(modn) if F(r, p, modn) == 0]
            for rn in roots:
                for k in range(q):
                    r1 = (rn + k * modn) % modnp1
                    b = B(r1, p, modnp1)
                    if gcd(b, modnp1) != 1:
                        print("cex", p, q, n, rn, r1, b, modnp1, gcd(b, modnp1))
                        raise SystemExit
print("no cex in range")
