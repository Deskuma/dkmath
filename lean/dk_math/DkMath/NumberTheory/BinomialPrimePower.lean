/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.BinomialPrime
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity

#print "file: DkMath.NumberTheory.BinomialPrimePower"

namespace DkMath
namespace NumberTheory

/-!
## Prime-power rows in Pascal's triangle

Prime rows are the first visible layer of binomial divisibility.  Prime-power
rows keep the same support prime across the whole inner row; the exponent of
that support is measured by the usual `padicValNat`/factorization layer.
-/

/--
A prime-power row whose base prime is visible across every inner binomial
coefficient.
-/
def PrimePowerRowSupport (p n : ℕ) : Prop :=
  p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p

/--
All inner coefficients in row `d` have exactly the same `p`-adic height `h`.

This is a stricter beam filter than mere divisibility: not only does `p`
divide every inner coefficient, the visible `p`-support has uniform height.
-/
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h

/--
Every inner coefficient of row `p^n` is divisible by `p`.

This is the support-level `p^n` filter.  It deliberately records only the first
divisibility layer; exact exponents are handled by the `padicValNat` lemmas
below.
-/
theorem prime_power_allInnerChooseDivisible
    {p n : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible (p ^ n) p := by
  intro k hk0 hkp
  exact hp.dvd_choose_pow hk0.ne' (ne_of_lt hkp)

/--
Prime-power rows carry their base prime through every inner coefficient.
-/
theorem prime_power_innerRowSupportPrime
    {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  ⟨hp, prime_power_allInnerChooseDivisible hp⟩

/--
Positive prime-power rows birth their base support prime from the row index.
-/
theorem prime_power_rowBirthPrime
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    RowBirthPrime (p ^ n) p := by
  refine ⟨prime_power_innerRowSupportPrime hp, ?_⟩
  refine ⟨p ^ (n - 1), ?_⟩
  have hs : (n - 1).succ = n := by omega
  rw [Nat.mul_comm, ← Nat.pow_succ, hs]

/--
Package the support observation and the positive exponent together.
-/
theorem prime_power_rowSupport
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    PrimePowerRowSupport p n :=
  ⟨hp, hn, prime_power_innerRowSupportPrime hp⟩

/--
Kummer's prime-power binomial valuation in `padicValNat` form.

Mathlib proves this first as a `Nat.factorization` identity; this lemma exposes
the same statement through the ABC valuation API used elsewhere in DkMath.
-/
theorem padicValNat_choose_prime_pow
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k := by
  have hfac := Nat.factorization_choose_prime_pow hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
Kummer's prime-power binomial valuation in additive form.

This is often the most convenient formulation for filters: the support carried
by the coefficient plus the support already present in the index is exactly the
row exponent.
-/
theorem padicValNat_choose_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n := by
  have hfac := Nat.factorization_choose_prime_pow_add_factorization hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
Prime-power row filter.

If the requested layer `r` plus the `p`-support already present in the index
fits inside the row exponent `n`, then the binomial coefficient carries `p^r`.
-/
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k := by
  have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
  have hvchoose :
      padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k :=
    padicValNat_choose_prime_pow hp hkn hk0
  have hr_le : r ≤ padicValNat p (Nat.choose (p ^ n) k) := by
    rw [hvchoose]
    omega
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne r).mp hr_le

/--
Prime rows have uniform beam height `1` at their own prime.
-/
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 := by
  intro k hk0 hkp
  have hkp_le : k ≤ p := hkp.le
  have hk_ne : k ≠ 0 := hk0.ne'
  have hpk : ¬ p ∣ k := by
    intro hdiv
    have hple : p ≤ k := Nat.le_of_dvd hk0 hdiv
    omega
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk_ne).mpr hpk
  have hkp_pow : k ≤ p ^ 1 := by simpa using hkp_le
  simpa [hvk] using
    (padicValNat_choose_prime_pow (p := p) (n := 1) (k := k) hp hkp_pow hk_ne)

/--
If the inner index is a `p`-unit, the row `p^n` coefficient carries the full
`p^n` divisibility.
-/
theorem prime_power_dvd_choose_of_not_dvd_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0).mpr hpk
  exact prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 (by omega)

section samples

example {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  prime_power_innerRowSupportPrime hp

example {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k :=
  prime_power_dvd_choose_of_not_dvd_index hp hkn hk0 hpk

example {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k :=
  prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 hr

example {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 :=
  prime_uniformBeamHeight_self hp

end samples

end NumberTheory
end DkMath
