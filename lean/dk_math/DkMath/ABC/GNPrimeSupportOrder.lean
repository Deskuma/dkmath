/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNSupportReturn
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.ABC.GNPrimeSupportOrder"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Multiplicative order of a non-exceptional GN support prime

At a prime exponent `p`, every prime `q` in the non-exceptional support of
`GN p T.a T.b` sees the ratio `T.c / T.b` as a nontrivial `p`th root of
unity modulo `q`.  Hence that ratio has exact multiplicative order `p`, so
`p ∣ q - 1` and `q % p = 1`.

This is a deterministic local order packet.  It does not assert existence,
abundance, or a uniform size bound for non-exceptional support primes.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
A non-exceptional GN support prime at prime exponent carries a unit of exact
multiplicative order equal to the exponent.

The witness is the residue-class ratio `T.c / T.b` in `(ZMod q)ˣ`.
-/
theorem Triple.exists_gnRatioUnit_orderOf_eq_prime
    (T : Triple) {p q : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hq : q ∈ GNNonExceptionalSupport p T.a T.b) :
    ∃ r : (ZMod q)ˣ, orderOf r = p := by
  classical
  have hfresh := T.nonExceptionalSupport_fresh hp.one_le ha hq
  have hqPrime : Nat.Prime q := hfresh.1
  have hqGN : q ∣ GN p T.a T.b := hfresh.2.1
  have hqa : ¬ q ∣ T.a := hfresh.2.2.1
  have hqb : ¬ q ∣ T.b := hfresh.2.2.2.1
  have hqc : ¬ q ∣ T.c := hfresh.2.2.2.2.1
  letI : Fact q.Prime := ⟨hqPrime⟩
  have hbZ : (T.b : ZMod q) ≠ 0 := by
    intro hb0
    exact hqb ((ZMod.natCast_eq_zero_iff T.b q).mp hb0)
  have hcZ : (T.c : ZMod q) ≠ 0 := by
    intro hc0
    exact hqc ((ZMod.natCast_eq_zero_iff T.c q).mp hc0)
  let ub : (ZMod q)ˣ := Units.mk0 (T.b : ZMod q) hbZ
  let uc : (ZMod q)ˣ := Units.mk0 (T.c : ZMod q) hcZ
  let r : (ZMod q)ˣ := uc * ub⁻¹
  have hGNZ : ((GN p T.a T.b : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (GN p T.a T.b) q).mpr hqGN
  have hpow : (T.c : ZMod q) ^ p = (T.b : ZMod q) ^ p := by
    have hcast := congrArg (fun n : ℕ => (n : ZMod q))
      (T.gnPowerLift_sum p)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hcast
    rw [hGNZ, mul_zero, zero_add] at hcast
    exact hcast.symm
  have hrPow : r ^ p = 1 := by
    have hunitPow : uc ^ p = ub ^ p := by
      apply Units.ext
      simpa [uc, ub] using hpow
    simp [r, mul_pow, hunitPow]
  have hrNeOne : r ≠ 1 := by
    intro hrOne
    have hratio :
        (T.c : ZMod q) * (T.b : ZMod q)⁻¹ = 1 := by
      have hcoe := congrArg
        (fun u : (ZMod q)ˣ => (u : ZMod q)) hrOne
      simpa [r, uc, ub] using hcoe
    have hcb : (T.c : ZMod q) = (T.b : ZMod q) := by
      calc
        (T.c : ZMod q) =
            (T.c : ZMod q) * (T.b : ZMod q)⁻¹ *
              (T.b : ZMod q) := by simp [hbZ]
        _ = 1 * (T.b : ZMod q) := by rw [hratio]
        _ = (T.b : ZMod q) := one_mul _
    have hsumZ :
        (T.a : ZMod q) + (T.b : ZMod q) = (T.c : ZMod q) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod q)) T.hsum
      simpa only [Nat.cast_add] using hcast
    rw [hcb] at hsumZ
    have haZ : (T.a : ZMod q) = 0 := by
      apply add_right_cancel (b := (T.b : ZMod q))
      simpa only [zero_add] using hsumZ
    exact hqa ((ZMod.natCast_eq_zero_iff T.a q).mp haZ)
  refine ⟨r, ?_⟩
  have horderDvd : orderOf r ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hrPow
  rcases (Nat.dvd_prime hp).mp horderDvd with horderOne | horderPrime
  · exact False.elim (hrNeOne (orderOf_eq_one_iff.mp horderOne))
  · exact horderPrime

/--
Every non-exceptional GN support prime at prime exponent is congruent to one
modulo the exponent, in divisibility form.
-/
theorem Triple.prime_dvd_sub_one_of_mem_GNNonExceptionalSupport
    (T : Triple) {p q : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hq : q ∈ GNNonExceptionalSupport p T.a T.b) :
    p ∣ q - 1 := by
  have hfresh := T.nonExceptionalSupport_fresh hp.one_le ha hq
  letI : Fact q.Prime := ⟨hfresh.1⟩
  obtain ⟨r, hr⟩ :=
    T.exists_gnRatioUnit_orderOf_eq_prime hp ha hq
  rw [← hr]
  exact ZMod.orderOf_units_dvd_card_sub_one r

/--
Every non-exceptional GN support prime at prime exponent has remainder one
modulo the exponent.
-/
theorem Triple.mod_eq_one_of_mem_GNNonExceptionalSupport
    (T : Triple) {p q : ℕ}
    (hp : Nat.Prime p)
    (ha : 0 < T.a)
    (hq : q ∈ GNNonExceptionalSupport p T.a T.b) :
    q % p = 1 := by
  have hqPrime :=
    (T.nonExceptionalSupport_fresh hp.one_le ha hq).1
  have hdiv :=
    T.prime_dvd_sub_one_of_mem_GNNonExceptionalSupport hp ha hq
  have hsubMod : (q - 1) % p = 0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  calc
    q % p = ((q - 1) + 1) % p := by
      rw [Nat.sub_add_cancel hqPrime.one_le]
    _ = (((q - 1) % p) + (1 % p)) % p := by
      rw [Nat.add_mod]
    _ = 1 := by simp [hsubMod, Nat.mod_eq_of_lt hp.one_lt]

end DkMath.ABC
