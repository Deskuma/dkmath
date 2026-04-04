#!/usr/bin/env python3


def F(x, p, mod):
    s = 0
    t = 1
    for _ in range(p):
        s = (s + t) % mod
        t = (t * x) % mod
    return s


primes = [2, 3, 5, 7, 11, 13, 17, 19]
cex = []
for p in primes:
    for q in primes:
        if q == p:
            continue
        for n in range(1, 5):
            mod_n = q**n
            mod_np1 = q ** (n + 1)
            for rn in range(mod_n):
                if F(rn, p, mod_n) != 0:
                    continue
                ok = False
                for k in range(q):
                    rlift = (rn + k * mod_n) % mod_np1
                    if F(rlift, p, mod_np1) == 0:
                        ok = True
                        break
                if not ok:
                    cex.append((p, q, n, rn))
                    if len(cex) >= 20:
                        break
            if len(cex) >= 20:
                break
        if len(cex) >= 20:
            break
    if len(cex) >= 20:
        break

if cex:
    print("Counterexamples for q != p:")
    for t in cex:
        print(t)
else:
    print("No counterexample found for q != p in tested range.")
