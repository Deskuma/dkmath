/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport

#print "file: DkMath.Lib.NumberTheory.WeierstrassDenominatorSupport"

/-!
# 同じ有理モデルの局所整性と、構成済み共通分母の支持

[DkMath.Lib] 係数がqで整であることと、前段の同じ共通分母dをqが割らないことを同値にする。
p以外で整であることはdがp冪であることと同値。モデルや整数化を取り替えない。
さらに任意のq上の延長付値環で、局所整性からv(d)=1を内部供給し、
既存の同じ整数モデルのΔ,c₄の付値保存へ接続する。
ここは有理モデル一般の判定であり、既存kernelModelの係数の整性自体を仮定なしで供給しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
open WeierstrassCurve RationalPrimeDenominator ValuationRationalPrimeSupport ValuationPrimeSupport

/-- [DkMath.Lib] 同じ有理曲線の五つの係数がqで局所整であるという条件。 -/
def CoeffIntegralAt (W : WeierstrassCurve ℚ) (q : ℕ) : Prop :=
  0 ≤ padicValRat q W.a₁ ∧ 0 ≤ padicValRat q W.a₂ ∧ 0 ≤ padicValRat q W.a₃ ∧
    0 ≤ padicValRat q W.a₄ ∧ 0 ≤ padicValRat q W.a₆

/-- [DkMath.Lib] 五係数の局所整性は、同じ共通分母の素数非可除性と同値。 -/
theorem coeffIntegralAt_iff_not_dvd (W : WeierstrassCurve ℚ) {q : ℕ} (hq : q.Prime) :
    CoeffIntegralAt W q ↔ ¬ q ∣ commonDenominator W := by
  simp only [CoeffIntegralAt, padicValRat_nonneg_iff _ hq, commonDenominator, hq.dvd_mul, not_or]
  tauto

/-- [DkMath.Lib] p以外で五係数が整であることと、同じ共通分母がp冪であることの同値。 -/
theorem exists_commonDenominator_pow_iff (W : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) :
    (∃ e : ℕ, commonDenominator W = p ^ e) ↔
      ∀ q : ℕ, q.Prime → q ≠ p → CoeffIntegralAt W q := by
  constructor
  · rintro ⟨e, he⟩ q hq hqp
    apply (coeffIntegralAt_iff_not_dvd W hq).mpr
    intro hd
    rw [he] at hd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
  · intro h
    obtain ⟨e₁, h₁⟩ := exists_den_eq_pow W.a₁ p (fun q hq hqp => (h q hq hqp).1)
    obtain ⟨e₂, h₂⟩ := exists_den_eq_pow W.a₂ p (fun q hq hqp => (h q hq hqp).2.1)
    obtain ⟨e₃, h₃⟩ := exists_den_eq_pow W.a₃ p (fun q hq hqp => (h q hq hqp).2.2.1)
    obtain ⟨e₄, h₄⟩ := exists_den_eq_pow W.a₄ p (fun q hq hqp => (h q hq hqp).2.2.2.1)
    obtain ⟨e₆, h₆⟩ := exists_den_eq_pow W.a₆ p (fun q hq hqp => (h q hq hqp).2.2.2.2)
    refine ⟨e₁ + e₂ + e₃ + e₄ + e₆, ?_⟩
    simp only [commonDenominator, h₁, h₂, h₃, h₄, h₆, ← pow_add]

/-- [DkMath.Lib] 同じ係数の局所整性を、任意の延長付値環内の係数所属へ戻す。 -/
theorem coeffIntegralAt_iff_mem {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve ℚ) (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) :
    CoeffIntegralAt W q ↔ (W.a₁ : K) ∈ A ∧ (W.a₂ : K) ∈ A ∧ (W.a₃ : K) ∈ A ∧
      (W.a₄ : K) ∈ A ∧ (W.a₆ : K) ∈ A := by
  simp only [CoeffIntegralAt, ratCast_mem_iff_padicValRat_nonneg A hq hA]

/-- [DkMath.Lib] 五係数がqで整なら、同じ整数化の倍率dはq上の任意の延長付値で単元。 -/
theorem commonDenominator_value_one {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve ℚ) (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) (hW : CoeffIntegralAt W q) :
    A.valuation (commonDenominator W : K) = 1 := by
  simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq hA (z := (commonDenominator W : ℤ))
    (by exact_mod_cast (coeffIntegralAt_iff_not_dvd W hq).mp hW)

/-- [DkMath.Lib] 局所整性から単元倍率を内部供給し、同じ整数化前後のΔ,c₄の付値を保つ。 -/
theorem integerModel_invariants_of_coeffIntegralAt {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve ℚ) (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : A.valuation (q : K) < 1) (hW : CoeffIntegralAt W q) :
    A.valuation ((integerModel W).Δ : K) = A.valuation (W.Δ : K) ∧
      A.valuation ((integerModel W).c₄ : K) = A.valuation (W.c₄ : K) := by
  have hd := commonDenominator_value_one W A hq hA hW
  have hΔ := congrArg (Rat.castHom K) (integerModel_discriminant W)
  have hc := congrArg (Rat.castHom K) (integerModel_c4 W)
  simp only [map_mul, map_pow, map_natCast, map_intCast] at hΔ hc
  constructor
  · rw [hΔ, map_mul, map_pow, hd, one_pow, one_mul]
    rfl
  · rw [hc, map_mul, map_pow, hd, one_pow, one_mul]
    rfl

end DkMath.Lib.NumberTheory.WeierstrassRationalIntegralModel
