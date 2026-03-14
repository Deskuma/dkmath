#!/usr/bin/env python3
from math import comb


def Z_lhs(x, u, d):
    # (x+u)^d - x * sum_{k=0}^{d-1} C(d,k+1) u^{d-1-k} x^k
    s = 0
    for k in range(0, max(0, d)):
        s += comb(d, k + 1) * (u ** (d - 1 - k)) * (x**k)
    return (x + u) ** d - x * s


def Z_rhs(u, d):
    return u**d


def check_ranges(max_d=8, val_range=range(-3, 4)):
    failures = []
    for d in range(0, max_d + 1):
        for x in val_range:
            for u in val_range:
                lhs = Z_lhs(x, u, d)
                rhs = Z_rhs(u, d)
                if lhs != rhs:
                    failures.append((d, x, u, lhs, rhs))
    return failures


def main():
    failures = check_ranges()
    if not failures:
        print("All tests passed: Z_d identity holds for tested integer ranges.")
    else:
        print(f"Found {len(failures)} failures:")
        for f in failures[:20]:
            d, x, u, lhs, rhs = f
            print(f"d={d}, x={x}, u={u}: lhs={lhs}, rhs={rhs}")


if __name__ == "__main__":
    main()
