/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Anchor
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.NumberTheory.UniqueFactorizationGN

#print "file: DkMath.Petal.BezoutBridge"

/-!
# Petal Bezout Bridge

This file gives Petal-facing names for the Bezout/gcd reading of the Cosmic
`GN` factorization.

The mathematical core is already present in the lower layers:

* `PrimitiveBeam` moves primitive prime factors from
  `a^d - b^d = (a - b) * GN d (a - b) b` to the `GN` side.
* `UniqueFactorizationGN` controls the gcd between the visible boundary and the
  residual `GN` kernel.

This bridge does not introduce a new Bezout theorem.  Instead it records the
interpretation needed by the Petal/Zsigmondy route:

```text
body difference = boundary * residual kernel
primitive witness avoids boundary
therefore the witness is observed on GN
```

The ideal-theoretic Bezout layer should remain a later, more general bridge.
This file is deliberately a thin Petal-facing surface.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.PrimitiveBeam

/--
Cosmic factor split in Petal boundary/kernel language.

This is the `body = boundary * GN` reading of
`(x + u)^d - u^d`.
-/
theorem cosmicBody_eq_boundary_mul_GN
    {d x u : ℕ} (hd : 0 < d) (hx : 0 < x) :
    (x + u) ^ d - u ^ d = x * GN d x u := by
  have hu_lt : u < x + u := by
    simpa [Nat.add_comm] using Nat.lt_add_of_pos_right (n := u) hx
  simpa [Nat.add_sub_cancel] using
    DkMath.NumberTheory.GcdNext.pow_sub_pow_factor_cosmic_N
      (a := x + u) (b := u) (d := d) hd hu_lt

/--
Primitive witnesses on the body difference are observed on the residual `GN`
kernel.

This is the Petal-facing Bezout/gcd reading: the primitive witness avoids the
visible boundary, so divisibility of `boundary * GN` forces the witness onto
`GN`.
-/
theorem primitivePrimeFactor_dvd_GN_of_cosmicBoundary
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    q ∣ GN d (a - b) b :=
  primitive_prime_dvd_GN
    (q := q) (a := a) (b := b) (d := d) hq hd hd1 hab_lt

/--
Body-coordinate version of `primitivePrimeFactor_dvd_GN_of_cosmicBoundary`.

If the body is written as `(x + u)^d - u^d`, then the primitive witness lies on
`GN d x u`.
-/
theorem primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary
    {q x u d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d) (hd1 : 1 < d) :
    q ∣ GN d x u :=
  primitive_prime_dvd_GN_body
    (q := q) (x := x) (u := u) (d := d) hq hd hd1

/--
Non-exceptional primes cannot sit in the gcd between the visible boundary and
the residual `GN` kernel.

This is the Bezout-style separation used by the Petal route: under coprimality
of `x` and `u`, any prime common to `x` and `GN d x u` must be exceptional for
the exponent `d`.
-/
theorem prime_not_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    ¬ q ∣ Nat.gcd x (GN d x u) :=
  DkMath.NumberTheory.prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
    (d := d) (x := x) (u := u) (q := q)
    hd1 hx hcop hqP hq_ndvd_d

/--
Valuation form of the boundary/GN Bezout separation.

For non-exceptional primes, the `q`-adic height of `gcd(boundary, GN)` is zero.
-/
theorem padicValNat_boundary_GN_gcd_eq_zero_of_coprime_of_not_dvd_exp
    {d x u q : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) :
    padicValNat q (Nat.gcd x (GN d x u)) = 0 :=
  DkMath.NumberTheory.padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp
    (d := d) (x := x) (u := u) (q := q)
    hd1 hx hcop hqP hq_ndvd_d

/--
Prime-power form of the boundary/GN Bezout separation.

If `q` is non-exceptional for `d`, no positive power of `q` can divide the
common boundary/GN gcd.
-/
theorem not_primePow_dvd_boundary_GN_gcd_of_coprime_of_not_dvd_exp
    {d x u q k : ℕ}
    (hd1 : 1 ≤ d) (hx : 0 < x) (hcop : Nat.Coprime x u)
    (hqP : Nat.Prime q) (hq_ndvd_d : ¬ q ∣ d) (hk : 0 < k) :
    ¬ q ^ k ∣ Nat.gcd x (GN d x u) :=
  DkMath.NumberTheory.not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp
    (d := d) (x := x) (u := u) (q := q) (k := k)
    hd1 hx hcop hqP hq_ndvd_d hk

/--
Primitive witnesses can be packaged as anchored GN carriers.

This is the Anchor-facing endpoint of the Bezout reading: after the primitive
prime has moved from the body difference to `GN`, the prime itself is a positive
anchor carrier on the GN surface.
-/
theorem anchoredGNCarrier_of_primitivePrimeFactor
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    AnchoredGNCarrier q d (a - b) b q := by
  refine ⟨?_, ?_⟩
  · exact hasPositiveAnchorPrime_self_of_prime hq.1
  · exact primitivePrimeFactor_dvd_GN_of_cosmicBoundary hq hd hd1 hab_lt

/--
Body-coordinate anchored GN carrier constructor.
-/
theorem anchoredGNCarrier_of_bodyPrimitivePrimeFactor
    {q x u d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q (x + u) u d)
    (hd : 0 < d) (hd1 : 1 < d) :
    AnchoredGNCarrier q d x u q := by
  refine ⟨?_, ?_⟩
  · exact hasPositiveAnchorPrime_self_of_prime hq.1
  · exact primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary hq hd hd1

end Petal
end DkMath
