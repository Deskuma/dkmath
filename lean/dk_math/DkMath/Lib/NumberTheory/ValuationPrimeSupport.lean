/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Integer factorization argument adapted from
S_ValuationSubring_valuation_intCast_eq_pow_padicValInt.lean,
blob ebcc3734f530bf46253e247834ad3209035932d5.
Modified: DkMath namespace, Bezout unit proof, explicit valuation address and residue bridge.
-/

import DkMath.Lib.NumberTheory.ValuationInertia
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.CharP.Basic

#print "file: DkMath.Lib.NumberTheory.ValuationPrimeSupport"

/-!
# NOTE-031-002A: 整数の素数支持を実際の付値環へ輸送する

qが付値環Aの非単元なら、qと互いに素な整数はAの単元となる。
Bezout等式をAへ写して証明する。整数z≠0をqの冪とqを割らない因子に分けると、
Aの値群を正規化せずにv(z)=v(q)^padicValInt(q,z)を得る。
v(q)を固定の実数や整数に同一視しないため、代数閉包上の任意の延長付値に使える。
剰余体の標数qも、q.Primeと住所の条件から実際に供給する。
-/
namespace DkMath.Lib.NumberTheory.ValuationPrimeSupport
open ValuationInertia
variable {K : Type*} [Field K]

/-- q上の付値環では、qを割らない整数の乗法的付値は1となる。Bezout等式を使う。 -/
theorem valuation_intCast_eq_one_of_not_dvd (A : ValuationSubring K) {q : ℕ}
    (hq : q.Prime) (hA : A.valuation (q : K) < 1) {z : ℤ}
    (hqz : ¬ (q : ℤ) ∣ z) : A.valuation (z : K) = 1 := by
  have hc : IsCoprime (q : ℤ) z :=
    (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hqz
  obtain ⟨u, v, huv⟩ := hc.map (Int.castRingHom A)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at huv
  have hqu : ¬ IsUnit (q : A) := by
    intro h
    exact hA.ne ((A.valuation_eq_one_iff _).mp h)
  have hsum : IsUnit (u * (q : A) + v * (z : A)) := by
    rw [huv]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
  · exact (hqu (isUnit_of_mul_isUnit_right h)).elim
  · exact (A.valuation_eq_one_iff _).mp (isUnit_of_mul_isUnit_right h)

/-- q上の付値環の剰余体は標数qである。単に標数を外部インスタンスに仮定しない。 -/
theorem charP_residueField (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : LiesOverPrime A q) : CharP (IsLocalRing.ResidueField A) q := by
  apply (CharP.charP_iff_prime_eq_zero hq).mpr
  rw [← map_natCast (IsLocalRing.residue A)]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  exact hA

/-- qで割れる整数の付値は、q上の付値環では厳密に1より小さい。
零も含む。判別式の非零性は幾何学の側で別に保持する。 -/
theorem valuation_intCast_lt_one_of_dvd (A : ValuationSubring K) {q : ℕ}
    (hA : A.valuation (q : K) < 1) {z : ℤ} (hz : (q : ℤ) ∣ z) :
    A.valuation (z : K) < 1 := by
  obtain ⟨k, rfl⟩ := hz
  rw [Int.cast_mul, Int.cast_natCast, map_mul]
  exact (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).mpr (intCast_mem A k))).trans_lt hA

/-- 非零整数zの付値を、qの付値と通常の整数q進付値から厳密に復元する。
z=0でのpadicValIntの零デフォルトを使わないため、非零条件を保持する。 -/
theorem valuation_intCast_eq_pow_padicValInt (A : ValuationSubring K) {q : ℕ}
    (hq : q.Prime) (hA : A.valuation (q : K) < 1) {z : ℤ} (hz : z ≠ 0) :
    A.valuation (z : K) = A.valuation (q : K) ^ padicValInt q z := by
  have : Fact q.Prime := ⟨hq⟩
  set v : ℕ := padicValNat q z.natAbs with hv
  have hn0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hdvd : q ^ v ∣ z.natAbs := pow_padicValNat_dvd
  obtain ⟨c, hc⟩ := hdvd
  have hqc : ¬ (q : ℤ) ∣ (c : ℤ) := by
    intro h
    have h' : q ∣ c := Int.natCast_dvd_natCast.mp h
    obtain ⟨d, rfl⟩ := h'
    have : q ^ (v + 1) ∣ z.natAbs := ⟨d, by rw [hc]; ring⟩
    exact pow_succ_padicValNat_not_dvd hn0 this
  have hcval : A.valuation ((c : ℤ) : K) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A hq hA hqc
  have habs : A.valuation (z : K) = A.valuation ((z.natAbs : ℤ) : K) := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg]
  have hpv : padicValInt q z = v := rfl
  rw [habs, hpv, Int.cast_natCast, hc, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow,
    show ((c : ℕ) : K) = ((c : ℤ) : K) by norm_cast, hcval, mul_one]

/-- 整数のq進付値がnで割れるとき、実際の付値もn乗の形になる。
この等式は値群内の等式であり、慣性作用の自明性そのものではない。 -/
theorem valuation_intCast_eq_pow_of_dvd (A : ValuationSubring K) {q : ℕ}
    (hq : q.Prime) (hA : A.valuation (q : K) < 1) {z : ℤ} (hz : z ≠ 0)
    {n : ℕ} (hn : n ∣ padicValInt q z) :
    A.valuation (z : K) = (A.valuation (q : K) ^ (padicValInt q z / n)) ^ n := by
  rw [valuation_intCast_eq_pow_padicValInt A hq hA hz, ← pow_mul, Nat.div_mul_cancel hn]

/-- 実際の慣性元は付値環の各元を剰余体で固定するので、変化量は非単元となる。
この合同は差が零であることを意味しない。点への適用には還元の単射性がさらに必要である。 -/
theorem inertia_apply_sub_mem_nonunits (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]
    (σ : K ≃ₐ[F] K) (hσ : σ ∈ inertiaSubgroupIn A F) {a : K} (ha : a ∈ A) :
    σ a - a ∈ A.nonunits := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
  let x : A := ⟨a, ha⟩
  have hfix := congrArg (fun e => e (IsLocalRing.residue A x)) (MonoidHom.mem_ker.mp hτ)
  change τ • IsLocalRing.residue A x = IsLocalRing.residue A x at hfix
  rw [← IsLocalRing.ResidueField.residue_smul] at hfix
  change ((τ • x - x : A) : K) ∈ A.nonunits
  apply ValuationSubring.coe_mem_nonunits_iff.mpr
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  rw [map_sub, hfix, sub_self]

/-- 2が単元で、単元zの平方を固定する慣性元はzも固定する。
平方の二つの根±zを剰余合同で区別する。2が非単元の場合はこの符号の議論を適用しない。 -/
theorem inertia_fixed_of_unit_square (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]
    (h2 : A.valuation (2 : K) = 1) (σ : K ≃ₐ[F] K) (hσ : σ ∈ inertiaSubgroupIn A F)
    {z : K} (hz : A.valuation z = 1) (hsq : σ (z * z) = z * z) : σ z = z := by
  have hmul : σ z * σ z = z * z := by rwa [map_mul] at hsq
  rcases mul_self_eq_mul_self_iff.mp hmul with h | h
  · exact h
  · have hint : z ∈ A := (A.valuation_le_one_iff _).mp hz.le
    have hsmall := (ValuationSubring.mem_nonunits_iff A).mp
      (inertia_apply_sub_mem_nonunits A F σ hσ hint)
    have hd : σ z - z = -(2 * z) := by rw [h]; ring
    rw [hd, Valuation.map_neg, map_mul, h2, hz, one_mul] at hsmall
    exact (lt_irrefl _ hsmall).elim

end DkMath.Lib.NumberTheory.ValuationPrimeSupport
