from __future__ import annotations

from dataclasses import dataclass
from math import comb
from typing import Optional, Tuple


def int_nth_root_floor(n: int, d: int) -> int:
    """
    floor(n^(1/d)) for n >= 0, d >= 1 using integer binary search.
    """
    if d <= 0:
        raise ValueError("d must be >= 1")
    if n < 0:
        raise ValueError("n must be >= 0")
    if n in (0, 1) or d == 1:
        return n

    # Upper bound: 2^(ceil(bitlen/d)) is a safe-ish starting bound.
    bl = n.bit_length()
    hi = 1 << ((bl + d - 1) // d)
    lo = 0
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        p = mid**d
        if p <= n:
            lo = mid
        else:
            hi = mid
    return lo


def int_nth_root_nearest(n: int, d: int) -> int:
    """
    nearest integer to n^(1/d) for n >= 0, d >= 1 (ties go down).
    """
    a = int_nth_root_floor(n, d)
    # compare (a+1)^d - n vs n - a^d
    low = a**d
    high = (a + 1) ** d
    if (high - n) < (n - low):
        return a + 1
    return a


def body(d: int, x: int, u: int) -> int:
    """
    Body_d(x;u) = (u+x)^d - u^d
               = sum_{j=1..d} binom(d,j) u^(d-j) x^j
    Implemented in stable integer form (no subtraction of close huge ints).
    """
    if d < 0:
        raise ValueError("d must be >= 0")
    if d == 0:
        return 0
    # Horner-like evaluation in x:
    # sum_{j=1..d} binom(d,j) u^(d-j) x^j
    # = x * sum_{k=0..d-1} binom(d,k+1) u^(d-1-k) x^k
    acc = 0
    # build polynomial in x: P(x) = sum_{k=0..d-1} binom(d,k+1) u^(d-1-k) x^k
    # evaluate P with Horner from highest k down to 0
    for k in range(d - 1, -1, -1):
        coeff = comb(d, k + 1) * (u ** (d - 1 - k))
        acc = acc * x + coeff
    return x * acc


def delta_step(d: int, a: int) -> int:
    """
    δ_d(a) = (a+1)^d - a^d = Body_d(1; a)
    This is the 'next base gap' used by normalization.
    """
    return body(d, 1, a)


@dataclass(frozen=True)
class HyperIntegerV2:
    """
    HyperIntegerV2: exact integer-only representation of a value as A^d + Δ.

    Fields:
      d: dimension/exponent (d >= 1)
      A: base (integer)
      Δ: residual (integer)

    Value:
      val = A^d + Δ
    """

    d: int
    A: int
    D: int  # Δ

    # -----------------------------
    # Construction helpers
    # -----------------------------

    @staticmethod
    def from_int(d: int, n: int, normalize: bool = True) -> "HyperIntegerV2":
        """
        Create HIv2 from an integer n by choosing A ~= n^(1/d) and Δ = n - A^d.
        Uses nearest root (by magnitude) for better compactness, then optional normalize.
        """
        if d < 1:
            raise ValueError("d must be >= 1")

        if n == 0:
            hi = HyperIntegerV2(d=d, A=0, D=0)
            return hi if not normalize else hi.normalize()

        sign = 1
        m = n
        if n < 0:
            m = -n
            sign = -1

        # Choose base by nearest root of |n|.
        a0 = int_nth_root_nearest(m, d)
        # For negative n and even d, A^d is always nonnegative.
        # We'll still represent negative values via residual D.
        base_val = a0**d
        D = sign * m - base_val
        hi = HyperIntegerV2(d=d, A=a0, D=D)
        return hi if not normalize else hi.normalize()

    def val(self) -> int:
        return (self.A**self.d) + self.D

    # -----------------------------
    # Dimension completion mechanism (normalize)
    # -----------------------------

    def normalize(self, max_iters: int = 10_000) -> "HyperIntegerV2":
        """
        Adjust A so that residual D becomes "small" relative to local base gaps.
        This implements the d-dimensional completion mechanism.

        Strategy:
          - repeatedly absorb +/- delta_step(d, A) into A until D is within a local band.

        Notes on negative A:
          - This method works for any integer A (including negative values); it always
            preserves the invariant val == A**d + D.
          - For negative A, in particular when d is even, delta_step(d, A) and
            delta_step(d, A - 1) can be negative. The update rules in the loop still
            apply, but the effect is that normalization tends to move A toward
            non-negative values while shrinking |D| into the local "nearest base"
            band defined by roughly half of the forward/backward steps.
          - HyperIntegerV2.from_int(...) always constructs instances with A >= 0.
            Callers that manually build HyperIntegerV2 with a negative A should be
            aware that calling normalize() may change the sign of A even though the
            represented value (A**d + D) remains unchanged.
        """
        d, A, D = self.d, self.A, self.D
        if d < 1:
            raise ValueError("d must be >= 1")

        # Quick exits
        if D == 0:
            return self

        it = 0
        while it < max_iters:
            it += 1
            # local step forward and backward
            step_f = delta_step(d, A)  # (A+1)^d - A^d
            step_b = delta_step(d, A - 1)  # A^d - (A-1)^d

            # target band: keep D within about half-step (as "nearest base" normal form)
            # Use asymmetric halves to avoid oscillation; ties lean toward smaller |D|.
            if D >= 0:
                if D > step_f // 2:
                    # move A upward
                    D -= step_f
                    A += 1
                    continue
            else:
                if -D > step_b // 2:
                    # move A downward
                    D += step_b
                    A -= 1
                    continue

            # Already within band
            break

        if it >= max_iters:
            raise RuntimeError(
                "normalize: exceeded max_iters (possible logic issue or extreme values)"
            )

        return HyperIntegerV2(d=d, A=A, D=D)

    # -----------------------------
    # Operations
    # -----------------------------

    def add(self, other: "HyperIntegerV2", normalize: bool = True) -> "HyperIntegerV2":
        if self.d != other.d:
            raise ValueError("dimension mismatch")
        n = self.val() + other.val()
        return HyperIntegerV2.from_int(self.d, n, normalize=normalize)

    def sub(self, other: "HyperIntegerV2", normalize: bool = True) -> "HyperIntegerV2":
        if self.d != other.d:
            raise ValueError("dimension mismatch")
        n = self.val() - other.val()
        return HyperIntegerV2.from_int(self.d, n, normalize=normalize)

    def mul(self, other: "HyperIntegerV2", normalize: bool = True) -> "HyperIntegerV2":
        if self.d != other.d:
            raise ValueError("dimension mismatch")
        n = self.val() * other.val()
        return HyperIntegerV2.from_int(self.d, n, normalize=normalize)

    def neg(self) -> "HyperIntegerV2":
        return HyperIntegerV2.from_int(self.d, -self.val(), normalize=False)

    # -----------------------------
    # Identity-driven update: shift base by x using Body
    # -----------------------------

    def shift_base(self, x: int, normalize: bool = True) -> "HyperIntegerV2":
        """
        Apply base shift: interpret as moving A -> A + x while preserving exact value.

        We want new (A',D') such that:
          A'^d + D' = A^d + D

        Choose A' = A + x
          Then D' = (A^d + D) - (A + x)^d
                 = D - ((A + x)^d - A^d)
                 = D - Body_d(x; A)

        This uses the identity channel directly and avoids huge subtraction patterns.
        """
        d, A, D = self.d, self.A, self.D
        inc = body(d, x, A)  # (A+x)^d - A^d
        A2 = A + x
        D2 = D - inc
        hi = HyperIntegerV2(d=d, A=A2, D=D2)
        return hi if not normalize else hi.normalize()

    # -----------------------------
    # Debug / decomposition helpers
    # -----------------------------

    def decompose_body_coeffs(self, u: Optional[int] = None) -> Tuple[int, ...]:
        """
        Return coefficients of P(x) where Body_d(x;u) = sum_{j=1..d} c_j x^j
        with c_j = binom(d,j) u^(d-j).
        Useful if you later want Δ to be 'layered' by degree.
        """
        d = self.d
        if u is None:
            u = self.A
        coeffs = []
        for j in range(1, d + 1):
            coeffs.append(comb(d, j) * (u ** (d - j)))
        return tuple(coeffs)


# -----------------------------
# Minimal sanity tests
# -----------------------------
if __name__ == "__main__":
    # Basic correctness: val is preserved through normalize
    a = HyperIntegerV2(d=3, A=10, D=123456789)
    b = a.normalize()
    assert a.val() == b.val()

    # from_int round-trip
    n = 10**30 + 12345
    h = HyperIntegerV2.from_int(d=3, n=n)
    assert h.val() == n

    # add/mul/sub
    h1 = HyperIntegerV2.from_int(4, 10**20 + 7)
    h2 = HyperIntegerV2.from_int(4, 10**19 + 9)
    assert h1.add(h2).val() == (h1.val() + h2.val())
    assert h1.mul(h2).val() == (h1.val() * h2.val())
    assert h1.sub(h2).val() == (h1.val() - h2.val())

    # shift_base preserves value
    h3 = HyperIntegerV2.from_int(5, 10**25 + 123456)
    h4 = h3.shift_base(17)
    assert h3.val() == h4.val()

    # neg preserves value relationship
    h5 = HyperIntegerV2.from_int(3, 10**15 + 42)
    h5_neg = h5.neg()
    assert h5_neg.val() == -h5.val()

    print("OK: HyperIntegerV2 core sanity tests passed.")
