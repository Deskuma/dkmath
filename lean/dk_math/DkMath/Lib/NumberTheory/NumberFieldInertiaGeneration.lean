/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_NumberField_subgroup_eq_top_of_forall_inertia_le.lean.
Upstream blob: 9a2a7d73e9687c61b7dfeacc102b4c0e60a84af3
Modified for DkMath: expose the unramified fixed-field argument, use current
ramification-index APIs, and separate finite Galois arithmetic from absolute inertia lifting.
-/

import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.RamificationInertia.Unramified

#print "file: DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration"

/-!
# NOTE-031-001A: 有限ガロア拡大では有限素点の慣性群が全群を生成する

K/ℚを有限ガロア拡大、Hを全ての有限素点の慣性群を含む部分群とする。
固定体F=Kᴴの各素点はℤ上不分岐となる。分岐指数は塔で乗法的で、
慣性群の位数が分岐指数に等しいため、慣性群⊆Hはe(K/ℚ)=e(K/F)を意味する。
従ってe(F/ℚ)=1である。Minkowskiに基づくMathlibの分岐素点存在定理から[F:ℚ]=1、
有限ガロア対応の位数公式からH=Gal(K/ℚ)を得る。Hの正規性は仮定しない。

これは有限拡大上の実際の整数環の慣性群についての定理である。
代数閉包の付値環における慣性元の持ち上げや、絶対ガロア群の開部分群の大域化は
次の031-001Bに残す。この段階だけでFrey表現のhcasesを供給したとはしない。
-/
namespace DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

attribute [local instance] Ideal.Quotient.field in
/-- 全慣性群を含むHの固定体では、全ての有限素点がℤ上不分岐となる。
上の素点Pの存在、分岐指数の非零性、塔の乗法性を明示してe(F/ℚ)=1へ戻す。 -/
theorem fixedField_unramifiedAt_int_of_inertia_le (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ P : Ideal (𝓞 K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H)
    (p : Ideal (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ K))) [p.IsMaximal] :
    Algebra.IsUnramifiedAt ℤ p := by
  classical
  let F : IntermediateField ℚ K := FixedPoints.intermediateField H
  have : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
    (NumberField.RingOfIntegers.not_isField F)
  obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]; exact bot_le)
  have : P.LiesOver p := ⟨hPp.symm⟩
  have : (p.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ p
  have : P.LiesOver (p.under ℤ) := Ideal.LiesOver.trans P p (p.under ℤ)
  have h𝔭0 : p.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot hp0
  have : Finite (ℤ ⧸ p.under ℤ) := Ring.HasFiniteQuotients.finiteQuotient h𝔭0
  have : Finite (𝓞 F ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp0
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K) (p.under ℤ) P
  have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := H) p P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p.under ℤ) P (K ≃ₐ[ℚ] K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p.under ℤ) (q := P) h𝔭0] at c1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P H,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp0] at c2
  have c3 : Nat.card (P.inertia H) = Nat.card (P.inertia (K ≃ₐ[ℚ] K)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hH P hPmax)).toEquiv
  have hne : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hp0
  have he : (p.under ℤ).ramificationIdx' p = 1 := by
    have hh : (p.under ℤ).ramificationIdx' P = p.ramificationIdx' P := by rw [← c1, ← c2, c3]
    rw [Ideal.ramificationIdx'_algebra_tower' (p.under ℤ) p P] at hh
    exact (mul_eq_right₀ hne).mp hh
  exact Ideal.ramificationIdx_eq_one_iff.mp
    ((Ideal.ramificationIdx'_eq_ramificationIdx (p.under ℤ) p h𝔭0).symm.trans he)

/-- 全有限素点の慣性群を含むHの固定体は次数1となる。
Minkowskiの帰結である「非自明数体には分岐素点がある」をMathlibから実際に使う。 -/
theorem fixedField_finrank_eq_one_of_inertia_le (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ P : Ideal (𝓞 K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) :
    Module.finrank ℚ (FixedPoints.intermediateField H : IntermediateField ℚ K) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hram⟩ := NumberField.exists_not_isUnramifiedAt_int
    (K := (FixedPoints.intermediateField H : IntermediateField ℚ K)) (𝒪 := 𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ K)) hne
  exact hram (@fixedField_unramifiedAt_int_of_inertia_le K _ _ _ H hH p hp)

/-- 有限ガロア拡大K/ℚで、全有限素点の慣性群を含む部分群は全群である。
有限性の下で位数を比較する。絶対ガロア群の部分群へ有限性を暗黙に拡張しない。 -/
theorem subgroup_eq_top_of_inertia_le (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ P : Ideal (𝓞 K), P.IsMaximal → P.inertia (K ≃ₐ[ℚ] K) ≤ H) : H = ⊤ := by
  let F : IntermediateField ℚ K := FixedPoints.intermediateField H
  have hF : Module.finrank ℚ F = 1 := fixedField_finrank_eq_one_of_inertia_le H hH
  rw [← Subgroup.card_eq_iff_eq_top, IsGaloisGroup.card_eq_finrank H F K,
    IsGaloisGroup.card_eq_finrank (K ≃ₐ[ℚ] K) ℚ K, ← Module.finrank_mul_finrank ℚ F K, hF, one_mul]


/-- 実際の全有限素点の慣性群の上限は全ガロア群である。
表現の局所から大域への輸送に使う生成条件を、外部仮定ではなく算術から供給する。 -/
theorem iSup_inertia_eq_top :
    (⨆ P : {P : Ideal (𝓞 K) // P.IsMaximal}, P.val.inertia (K ≃ₐ[ℚ] K)) = ⊤ :=
  subgroup_eq_top_of_inertia_le _ (fun P hP =>
    le_iSup (fun Q : {P : Ideal (𝓞 K) // P.IsMaximal} => Q.val.inertia (K ≃ₐ[ℚ] K)) ⟨P, hP⟩)

end DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration
