#!/usr/bin/env python3
"""
Search counterexamples for the current HenselLiftStepZeroLiftTarget shape:
Given p,q,n and Rn mod q^n with F(Rn)=0 (mod q^n),
check if there exists Rlift mod q^(n+1) lifting Rn with F(Rlift)=0 (mod q^(n+1)).

F(T)=sum_{i=0}^{p-1} T^i
"""


def F(x, p, mod):
    s = 0
    t = 1
    for _ in range(p):
        s = (s + t) % mod
        t = (t * x) % mod
    return s


def find_counterexamples(max_p=13, max_q=13, max_n=4):
    out = []
    primes = [2, 3, 5, 7, 11, 13]
    for p in primes:
        if p > max_p:
            continue
        for q in primes:
            if q > max_q:
                continue
            for n in range(1, max_n + 1):
                mod_n = q**n
                mod_np1 = q ** (n + 1)
                for rn in range(mod_n):
                    if F(rn, p, mod_n) != 0:
                        continue
                    found = False
                    # lifts are rn + k*q^n
                    step = mod_n
                    for k in range(q):
                        rlift = (rn + k * step) % mod_np1
                        if F(rlift, p, mod_np1) == 0:
                            found = True
                            break
                    if not found:
                        out.append((p, q, n, rn))
                        if len(out) >= 20:
                            return out
    return out


if __name__ == "__main__":
    cex = find_counterexamples()
    if not cex:
        print("No counterexample found in search range.")
    else:
        print("Counterexamples found:")
        for p, q, n, rn in cex:
            print(f"p={p}, q={q}, n={n}, Rn={rn}")
