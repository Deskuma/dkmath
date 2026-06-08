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
If the inner index is a `p`-unit, the row `p^n` coefficient carries the full
`p^n` divisibility.
-/
theorem prime_power_dvd_choose_of_not_dvd_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0).mpr hpk
  have hvchoose :
      padicValNat p (Nat.choose (p ^ n) k) = n := by
    rw [padicValNat_choose_prime_pow hp hkn hk0, hvk, Nat.sub_zero]
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne n).mp (by omega)

section samples

example {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  prime_power_innerRowSupportPrime hp

example {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k :=
  prime_power_dvd_choose_of_not_dvd_index hp hkn hk0 hpk

end samples

end NumberTheory
end DkMath
