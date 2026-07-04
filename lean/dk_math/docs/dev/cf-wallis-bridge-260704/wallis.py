# Wallis–Cosmic Petal Bridge

from fractions import Fraction
from math import comb, prod, pi, sqrt
import math
import numpy as np
import matplotlib.pyplot as plt


def central_ratio(m: int) -> Fraction:
    """R_{2m} = 2^(2m) / C(2m,m)."""
    return Fraction(2 ** (2 * m), comb(2 * m, m))


def central_product(m: int) -> Fraction:
    """A_m = prod_{j=1}^m 2j/(2j-1)."""
    return prod(Fraction(2 * j, 2 * j - 1) for j in range(1, m + 1))


def mirror_product(m: int) -> Fraction:
    """B_m = prod_{j=1}^m 2j/(2j+1)."""
    return prod(Fraction(2 * j, 2 * j + 1) for j in range(1, m + 1))


def wallis_partial(m: int) -> Fraction:
    """W_m = prod_{j=1}^m (2j)^2 / ((2j-1)(2j+1))."""
    return prod(Fraction((2 * j) ** 2, (2 * j - 1) * (2 * j + 1)) for j in range(1, m + 1))


def cosmic_partial(m: int) -> Fraction:
    """C_m = prod_{j=1}^m (N_j+1)/N_j, P_j=2j-1, N_j=P_j(P_j+2)."""
    result = Fraction(1, 1)
    for j in range(1, m + 1):
        P = 2 * j - 1
        N = P * (P + 2)
        result *= Fraction(N + 1, N)
    return result


def local_cosmic_factor(j: int) -> Fraction:
    P = 2 * j - 1
    N = P * (P + 2)
    return Fraction(N + 1, N)


# 1. Exact finite verification
max_exact = 30
print("1. Exact finite verification")
print("Checking exact Fraction equalities:")
print("  R_{2m} = prod 2j/(2j-1)")
print("  R_{2m} * mirror = Wallis partial = Cosmic partial")
print()

all_ok = True
for m in range(1, max_exact + 1):
    R = central_ratio(m)
    A = central_product(m)
    B = mirror_product(m)
    W = wallis_partial(m)
    C = cosmic_partial(m)

    ok = (R == A) and (R * B == W) and (W == C)
    all_ok = all_ok and ok

print(f"All exact checks for m=1..{max_exact}: {all_ok}")
print()

print(f"{'m':>3} {'R_{2m}':>18} {'Mirror':>18} {'Wallis/Cosmic':>20} {'float(W)':>14} {'pi/2-W':>14}")
print("-" * 95)
for m in list(range(1, 11)) + [20, 30]:
    R = central_ratio(m)
    B = mirror_product(m)
    W = wallis_partial(m)
    print(
        f"{m:3d} "
        f"{str(R):>18} "
        f"{str(B):>18} "
        f"{str(W):>20} "
        f"{float(W):14.10f} "
        f"{(pi/2 - float(W)):14.10f}"
    )

print()
print("2. Local factor verification")
print(f"{'j':>3} {'P=2j-1':>8} {'N=P(P+2)':>12} {'Wallis factor':>18} {'Cosmic factor':>18}")
print("-" * 72)
for j in range(1, 11):
    P = 2 * j - 1
    N = P * (P + 2)
    Wj = Fraction((2*j)**2, (2*j-1)*(2*j+1))
    Cj = local_cosmic_factor(j)
    print(f"{j:3d} {P:8d} {N:12d} {str(Wj):>18} {str(Cj):>18}")

# 3. Numerical arrays for graphs
m_values = np.arange(1, 501)
R_values = np.array([float(central_ratio(int(m))) for m in m_values])
A_values = np.array([float(central_product(int(m))) for m in m_values])
B_values = np.array([float(mirror_product(int(m))) for m in m_values])
W_values = np.array([float(wallis_partial(int(m))) for m in m_values])
C_values = np.array([float(cosmic_partial(int(m))) for m in m_values])

# Asymptotic for R_{2m}: sqrt(pi*m)
R_asymp = np.sqrt(np.pi * m_values)

# Cosmic boundary correspondence:
# R_{2m}/sqrt(pi) ~ sqrt(m).  If N=m-1, then P+1=sqrt(N+1)=sqrt(m).
R_boundary = R_values / np.sqrt(np.pi)
cosmic_boundary = np.sqrt(m_values)

# 4. Plot: R_{2m} and sqrt(pi*m)
plt.figure(figsize=(10, 5))
plt.plot(m_values, R_values, label=r"$R_{2m}=2^{2m}/\binom{2m}{m}$")
plt.plot(m_values, R_asymp, label=r"$\sqrt{\pi m}$")
plt.title("Central ratio and Stirling/Wallis asymptotic")
plt.xlabel("m")
plt.ylabel("value")
plt.grid(True)
plt.legend()
plt.show()

# 5. Plot: normalized R / sqrt(pi) and cosmic boundary sqrt(m)
plt.figure(figsize=(10, 5))
plt.plot(m_values, R_boundary, label=r"$R_{2m}/\sqrt{\pi}$")
plt.plot(m_values, cosmic_boundary, label=r"$\sqrt{m}$")
plt.title("Central ratio as cosmic boundary coordinate")
plt.xlabel("m")
plt.ylabel("boundary coordinate")
plt.grid(True)
plt.legend()
plt.show()

# 6. Plot: Wallis/Cosmic partial tends to pi/2
plt.figure(figsize=(10, 5))
plt.plot(m_values, W_values, label=r"$\prod_{j=1}^{m}\frac{(2j)^2}{(2j-1)(2j+1)}$")
plt.axhline(pi / 2, label=r"$\pi/2$")
plt.title("Wallis partial equals cosmic gap product")
plt.xlabel("m")
plt.ylabel("partial product")
plt.grid(True)
plt.legend()
plt.show()

# 7. Plot: error decay
errors = (pi / 2) - W_values
plt.figure(figsize=(10, 5))
plt.plot(m_values, errors, label=r"$\pi/2-W_m$")
plt.title("Error decay of Wallis/Cosmic partial product")
plt.xlabel("m")
plt.ylabel("error")
plt.yscale("log")
plt.grid(True)
plt.legend()
plt.show()

# 8. Plot: exact equality residuals in float
residual_WC = np.abs(W_values - C_values)
residual_RA = np.abs(R_values - A_values)

plt.figure(figsize=(10, 5))
plt.plot(m_values, residual_RA, label=r"$|R_{2m}-A_m|$")
plt.plot(m_values, residual_WC, label=r"$|W_m-C_m|$")
plt.title("Floating residuals of exact identities")
plt.xlabel("m")
plt.ylabel("absolute residual")
plt.yscale("symlog", linthresh=1e-20)
plt.grid(True)
plt.legend()
plt.show()

print()
print("3. Last numerical samples")
print(f"{'m':>5} {'R_2m':>14} {'sqrt(pi*m)':>14} {'R/sqrt(pi)/sqrt(m)':>22} {'W_m':>14} {'pi/2-W_m':>14}")
print("-" * 92)
for m in [10, 20, 50, 100, 200, 500]:
    R = float(central_ratio(m))
    W = float(wallis_partial(m))
    rel_boundary = (R / sqrt(pi)) / sqrt(m)
    print(
        f"{m:5d} "
        f"{R:14.10f} "
        f"{sqrt(pi*m):14.10f} "
        f"{rel_boundary:22.12f} "
        f"{W:14.10f} "
        f"{(pi/2 - W):14.10f}"
    )