/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Prime-power argument adapted from S_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable,
blob 361e2b2a3f20b849206fe0142b58063452ace691.
Modified: independent rational-number API, exact local criterion and finite exceptional prime sets.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.Lib.NumberTheory.RationalPrimeDenominator"

/-!
# 有理数の局所整性と、既約分母の素数支持

[DkMath.Lib] 既約性が分子と分母の同時の素因数を排除するため、
q進位数が非負であることはqが分母を割らないことと同値になる。零の分母は1なので零も含める。
有限例外集合の外で局所整なら分母の全素因数は例外集合に入る。
例外が素数p一つなら、同じ実際の分母はpの冪となる。
-/
namespace DkMath.Lib.NumberTheory.RationalPrimeDenominator

/-- [DkMath.Lib] 分母を割る素数は、既約な同じ分子を割らない。 -/
theorem not_dvd_num_of_dvd_den (r : ℚ) {q : ℕ} (hq : q.Prime) (hd : q ∣ r.den) :
    ¬ (q : ℤ) ∣ r.num := by
  intro hn
  have hab : q ∣ r.num.natAbs := Int.natCast_dvd.mp hn
  exact hq.not_dvd_one (r.reduced.gcd_eq_one ▸ Nat.dvd_gcd hab hd)

/-- [DkMath.Lib] 分母を割る素数での有理位数は厳密に負。 -/
theorem padicValRat_neg_of_dvd_den (r : ℚ) {q : ℕ} (hq : q.Prime) (hd : q ∣ r.den) :
    padicValRat q r < 0 := by
  let : Fact q.Prime := ⟨hq⟩
  have hn : padicValInt q r.num = 0 := padicValInt.eq_zero_of_not_dvd (not_dvd_num_of_dvd_den r hq hd)
  have hv : 0 < padicValNat q r.den := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh := (padicValNat.eq_zero_iff).mp hz
    rcases hh with h | h | h
    · exact hq.ne_one h
    · exact r.den_ne_zero h
    · exact h hd
  rw [padicValRat_def, hn]
  omega

/-- [DkMath.Lib] 有理局所整性と同じ既約分母の素数非可除性の正確な同値。 -/
theorem padicValRat_nonneg_iff (r : ℚ) {q : ℕ} (hq : q.Prime) :
    0 ≤ padicValRat q r ↔ ¬ q ∣ r.den := by
  refine ⟨fun h hd => (not_le.mpr (padicValRat_neg_of_dvd_den r hq hd)) h, ?_⟩
  intro hd
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero, sub_zero]
  exact Nat.cast_nonneg _

/-- [DkMath.Lib] 有限例外集合の外で局所整なら、分母の全素因数は例外集合に入る。 -/
theorem primeFactors_subset_iff (r : ℚ) (S : Finset ℕ) :
    r.den.primeFactors ⊆ S ↔ ∀ q : ℕ, q.Prime → q ∉ S → 0 ≤ padicValRat q r := by
  constructor
  · intro h q hq hqS
    apply (padicValRat_nonneg_iff r hq).mpr
    intro hd
    exact hqS (h ((Nat.mem_primeFactors).mpr ⟨hq, hd, r.den_ne_zero⟩))
  · intro h q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    by_contra hn
    exact ((padicValRat_nonneg_iff r hp).mp (h q hp hn)) (Nat.dvd_of_mem_primeFactors hq)

/-- [DkMath.Lib] 一つの素数p以外で整なら、同じ分母はp冪である。
指数は同じ分母のfactorizationから取り出す。 -/
theorem exists_den_eq_pow (r : ℚ) (p : ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≠ p → 0 ≤ padicValRat q r) : ∃ e : ℕ, r.den = p ^ e := by
  refine ⟨r.den.factorization p, Nat.eq_pow_of_factorization_eq_single r.den_ne_zero ?_⟩
  rw [Finsupp.eq_single_iff]
  refine ⟨fun q hq => ?_, rfl⟩
  by_contra hqp
  have hm : q ∈ r.den.primeFactors := by rwa [← Nat.support_factorization]
  have hp := Nat.prime_of_mem_primeFactors hm
  exact ((padicValRat_nonneg_iff r hp).mp (h q hp (by simpa only [Finset.mem_singleton] using hqp))) (Nat.dvd_of_mem_primeFactors hm)

/-- [DkMath.Lib] 素数pについて、分母p冪とp以外での局所整性は同値。 -/
theorem exists_den_eq_pow_iff (r : ℚ) {p : ℕ} (hp : p.Prime) :
    (∃ e : ℕ, r.den = p ^ e) ↔ ∀ q : ℕ, q.Prime → q ≠ p → 0 ≤ padicValRat q r := by
  refine ⟨?_, exists_den_eq_pow r p⟩
  rintro ⟨e, he⟩ q hq hqp
  apply (padicValRat_nonneg_iff r hq).mpr
  intro hd
  rw [he] at hd
  exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))

end DkMath.Lib.NumberTheory.RationalPrimeDenominator
