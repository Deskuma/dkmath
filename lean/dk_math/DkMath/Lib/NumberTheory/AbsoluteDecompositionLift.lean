/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem, P2M/Sol/S_NumberField_exists_lift_mem_inertia_integralClosure.lean.
Upstream blob: 8bcd2f8014a5e5a4d662d04860376e53c208bbea
Modified for DkMath: named arithmetic interfaces, textbook explanations,
separate absolute-decomposition layers, and current Mathlib APIs.
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Profinite
import DkMath.Lib.NumberTheory.ValuationInertiaLift
#print "file: DkMath.Lib.NumberTheory.AbsoluteDecompositionLift"

/-!
# 有限分解群から同じ有限体を保つ絶対分解群への持ち上げ

整数閉包の素点の推移性で任意の延長を補正する。慣性の場合と異なり、
剰余体作用は打ち消さない。その素点を中心とする付値環の分数表示から、
素点の安定化が付値環の安定化を与えることも証明する。

局所完備化の次数や局所冪の存在は、この持ち上げだけからは主張しない。
-/

namespace DkMath.Lib.NumberTheory.AbsoluteDecompositionLift
open scoped NumberField Pointwise
open ValuationInertia ValuationInertiaLift.FractionRepresentation
set_option autoImplicit false
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝔅" => integralClosure ℤ (AlgebraicClosure ℚ)

/-- 指定された有限素点を安定化する元を、整数閉包の素点の安定化群へ持ち上げる。
有限体への制限と、同じ有理素数の所属をともに保つ。 -/
theorem exists_lift_mem_integral_decomposition
    (L : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] {q : ℕ} (hqQ : (q : 𝓞 L) ∈ Q)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q) :
    ∃ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ 𝔔 : Ideal 𝔅, 𝔔.IsMaximal ∧ (q : 𝔅) ∈ 𝔔 ∧ σ • 𝔔 = 𝔔 := by
  classical
  have hnormQ : Normal ℚ ℚ̄ := by
    have h : @Normal ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have halgQ : Algebra.IsAlgebraic ℚ ℚ̄ := by
    have h : @Algebra.IsAlgebraic ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hsepQ : Algebra.IsSeparable ℚ ℚ̄ := by
    have h : @Algebra.IsSeparable ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have : Algebra.IsAlgebraic L ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  have : Algebra.IsIntegral L ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  have : Normal L ℚ̄ := Normal.tower_top_of_normal ℚ L ℚ̄
  have : Algebra.IsSeparable L ℚ̄ := Algebra.isSeparable_tower_top_of_isSeparable ℚ L ℚ̄
  have : IsGalois L ℚ̄ := ⟨⟩
  have hstabτ : τ • Q = Q := hτ
  let actG : MulSemiringAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) 𝔅 := inferInstance
  let actGI : DistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := Ideal.pointwiseDistribMulAction
  let mulActGI : MulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribMulAction.toMulAction
  let dsmulGI : DistribSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribMulAction.toDistribSMul
  let smulzGI : SMulZeroClass (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribSMul.toSMulZeroClass
  let smulGI : SMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := SMulZeroClass.toSMul
  let f : 𝓞 L →+* 𝔅 := (algebraMap (𝓞 L) ℚ̄).codRestrict (integralClosure ℤ ℚ̄) fun x =>
    (map_isIntegral_int (algebraMap (𝓞 L) ℚ̄) (Algebra.IsIntegral.isIntegral x))
  let algOB : Algebra (𝓞 L) 𝔅 := f.toAlgebra
  have hf_coe : ∀ x : 𝓞 L, ((algebraMap (𝓞 L) 𝔅 x : 𝔅) : ℚ̄) = algebraMap L ℚ̄ (x : L) :=
    fun x => rfl
  have : IsScalarTower (𝓞 L) 𝔅 ℚ̄ := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hf_inj : Function.Injective (algebraMap (𝓞 L) 𝔅) := by
    intro x y hxy
    have h := congrArg (fun z : 𝔅 => (z : ℚ̄)) hxy
    simp only [hf_coe] at h
    exact NumberField.RingOfIntegers.coe_injective ((algebraMap L ℚ̄).injective h)
  have hres : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : 𝓞 L),
      σ • algebraMap (𝓞 L) 𝔅 x = algebraMap (𝓞 L) 𝔅 ((AlgEquiv.restrictNormalHom L σ) • x) := by
    intro σ x
    apply Subtype.ext
    change σ (algebraMap L ℚ̄ (x : L)) = algebraMap L ℚ̄ ((σ.restrictNormal L) (x : L))
    exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm
  let rsh : (ℚ̄ ≃ₐ[L] ℚ̄) →* (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
    { toFun := fun g => g.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrsh_apply : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (x : ℚ̄), rsh g x = g x := fun _ _ => rfl
  have hresL : ∀ g : ℚ̄ ≃ₐ[L] ℚ̄, AlgEquiv.restrictNormalHom L (rsh g) = 1 := by
    intro g
    refine AlgEquiv.ext fun x => (algebraMap L ℚ̄).injective ?_
    change algebraMap L ℚ̄ (((rsh g).restrictNormal L) x) = algebraMap L ℚ̄ x
    rw [AlgEquiv.restrictNormal_commutes, hrsh_apply]
    exact g.commutes x
  let actL : MulSemiringAction (ℚ̄ ≃ₐ[L] ℚ̄) 𝔅 := MulSemiringAction.compHom 𝔅 rsh
  let actLI : DistribMulAction (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := Ideal.pointwiseDistribMulAction
  let mulActLI : MulAction (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribMulAction.toMulAction
  let dsmulLI : DistribSMul (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribMulAction.toDistribSMul
  let smulzLI : SMulZeroClass (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribSMul.toSMulZeroClass
  let smulLI : SMul (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := SMulZeroClass.toSMul
  have hrs : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (b : 𝔅), g • b = rsh g • b := fun _ _ => rfl
  have hrsI : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (J : Ideal 𝔅), g • J = rsh g • J := by
    intro g J
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, hrs]
  have : SMulCommClass (ℚ̄ ≃ₐ[L] ℚ̄) (𝓞 L) 𝔅 := ⟨fun g a b => by
    apply Subtype.ext
    change g ((algebraMap L ℚ̄ (a : L)) * (b : ℚ̄)) = algebraMap L ℚ̄ (a : L) * g (b : ℚ̄)
    rw [map_mul, AlgEquiv.commutes]⟩
  let : TopologicalSpace 𝔅 := ⊥
  have : DiscreteTopology 𝔅 := ⟨rfl⟩
  have : ContinuousSMul (ℚ̄ ≃ₐ[L] ℚ̄) 𝔅 := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    have : FiniteDimensional L (IntermediateField.adjoin L {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin L {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self L (b : ℚ̄))
  have : Algebra.IsInvariant (𝓞 L) 𝔅 (ℚ̄ ≃ₐ[L] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap L ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : 𝔅 => (z : ℚ̄)) (hb g)
    obtain ⟨y, hy⟩ := hb'
    have hyint : IsIntegral ℤ y := by
      obtain ⟨p, hp, hp0⟩ := (b.2 : IsIntegral ℤ (b : ℚ̄))
      refine ⟨p, hp, (algebraMap L ℚ̄).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hy]
      convert hp0 using 2
      rfl
    refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
    exact hy⟩
  have : Algebra.IsIntegral (𝓞 L) 𝔅 :=
    Algebra.IsInvariant.isIntegral_of_profinite (G := ℚ̄ ≃ₐ[L] ℚ̄)
  -- 整数性からQの上の素点を取り、剰余環への制限を比較する。
  obtain ⟨𝔔, h𝔔max, h𝔔Q⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝔅) Q (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := hf_inj (by rw [hx, map_zero])
    rw [hx0]
    exact Q.zero_mem)
  have h𝔔prime : 𝔔.IsPrime := h𝔔max.isPrime
  have h𝔔lies : 𝔔.LiesOver Q := ⟨h𝔔Q.symm⟩
  have hmemQ : ∀ x : 𝓞 L, algebraMap (𝓞 L) 𝔅 x ∈ 𝔔 ↔ x ∈ Q := fun x => by
    change x ∈ Ideal.under (𝓞 L) 𝔔 ↔ x ∈ Q
    rw [h𝔔Q]
  -- 任意の延長を、同じ下の素点を持つ素点の推移性で安定化群へ調整する。
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) ℚ̄ τ
  have hunder : Ideal.under (𝓞 L) (σ₀ • 𝔔 : Ideal 𝔅) = Ideal.under (𝓞 L) 𝔔 := by
    ext x
    rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hres,
      hmemQ, hmemQ, map_inv, hσ₀]
    conv_rhs => rw [← hstabτ]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := 𝓞 L) (G := ℚ̄ ≃ₐ[L] ℚ̄) (σ₀ • 𝔔 : Ideal 𝔅) 𝔔 hunder
  have hσ₁𝔔 : (rsh g * σ₀) • 𝔔 = 𝔔 := by rw [mul_smul, ← hrsI, ← hg]
  have hσ₁L : AlgEquiv.restrictNormalHom L (rsh g * σ₀) = τ := by
    rw [map_mul, hresL, one_mul, hσ₀]
  refine ⟨rsh g * σ₀, hσ₁L, 𝔔, h𝔔max, ?_, hσ₁𝔔⟩
  have h : algebraMap (𝓞 L) 𝔅 (q : 𝓞 L) ∈ 𝔔 := (hmemQ _).mpr hqQ
  simpa only [map_natCast] using h

/-- 整数閉包の同じ素点の安定化から、その中心を持つ付値環の安定化へ。
非単元でない分母の分数表示を使い、σ と σ⁻¹ の双方の包含を示す。 -/
theorem exists_valuation_decomposition_of_integral_stabilizer
    (𝔔 : Ideal 𝔅) [𝔔.IsMaximal] {q : ℕ} (hq : q.Prime) (hq𝔔 : (q : 𝔅) ∈ 𝔔)
    (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (hσ : σ • 𝔔 = 𝔔) :
    ∃ A : ValuationSubring ℚ̄, LiesOverPrime A q ∧ σ ∈ A.decompositionSubgroup ℚ := by
  classical
  obtain ⟨A, hOA, h𝔔A⟩ := Ideal.image_subset_nonunits_valuationSubring
    (A := (integralClosure ℤ ℚ̄).toSubring) 𝔔 (Ideal.IsMaximal.ne_top ‹_›)
  have hmemA : ∀ b : 𝔅, (b : ℚ̄) ∈ A := fun b => hOA b.2
  have h𝔔nu : ∀ c ∈ 𝔔, (c : ℚ̄) ∈ A.nonunits := fun c hc => h𝔔A ⟨c, hc, rfl⟩
  have hA : LiesOverPrime A q := h𝔔nu _ hq𝔔
  let φ : 𝔅 →+* A := (integralClosure ℤ ℚ̄).val.toRingHom.codRestrict A.toSubring hmemA
  let J : Ideal 𝔅 := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hmemJ : ∀ b, b ∈ J ↔ (b : ℚ̄) ∈ A.nonunits := by
    intro b
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hJ : J = 𝔔 := by
    refine (Ideal.IsMaximal.eq_of_le ‹𝔔.IsMaximal› ?_ ?_).symm
    · exact (Ideal.IsPrime.comap φ).ne_top
    · intro c hc
      exact (hmemJ c).mpr (h𝔔nu c hc)
  have hcenter : ∀ b : 𝔅, (b : ℚ̄) ∈ A.nonunits ↔ b ∈ 𝔔 := fun b => by rw [← hmemJ, hJ]
  have key : ∀ ρ : ℚ̄ ≃ₐ[ℚ] ℚ̄, ρ • 𝔔 = 𝔔 → ∀ a ∈ A, ρ a ∈ A := by
    intro ρ hρ a ha
    obtain ⟨x, s, hs, hax⟩ := exists_integral_fraction A hq hA a ha
    have hs𝔔 : s ∉ 𝔔 := fun h => hs ((hcenter s).mpr h)
    have hρs𝔔 : ρ • s ∉ 𝔔 := by
      intro h
      apply hs𝔔
      rw [← hρ, Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h
      simpa only [inv_smul_smul] using h
    have hρsval : A.valuation (ρ (s : ℚ̄)) = 1 := by
      apply le_antisymm ((A.valuation_le_one_iff _).mpr (hmemA (ρ • s)))
      apply not_lt.mp
      intro h
      apply hρs𝔔
      apply (hcenter (ρ • s)).mp
      exact (ValuationSubring.mem_nonunits_iff _).mpr h
    have hρs0 : ρ (s : ℚ̄) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hρsval
      exact zero_ne_one hρsval
    have hρa : ρ a = ρ (x : ℚ̄) / ρ (s : ℚ̄) := by
      rw [eq_div_iff hρs0, ← map_mul, hax]
    rw [← A.valuation_le_one_iff, hρa, map_div₀, hρsval, div_one]
    exact (A.valuation_le_one_iff _).mpr (hmemA (ρ • x))
  have hσinv : σ⁻¹ • 𝔔 = 𝔔 := by
    calc
      σ⁻¹ • 𝔔 = σ⁻¹ • (σ • 𝔔) := congrArg (fun J => σ⁻¹ • J) hσ.symm
      _ = 𝔔 := inv_smul_smul σ 𝔔
  refine ⟨A, hA, ?_⟩
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext a
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro ha
    have h := key σ hσ _ ha
    simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using h
  · exact key σ⁻¹ hσinv a

/-- 実際の有限分解群の元を、同じ有理素数上の絶対分解群へ持ち上げる。
慣性所属や局所次数を入力に要求しない。 -/
theorem exists_lift_mem_valuation_decomposition
    (L : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] {q : ℕ} (hq : q.Prime) (hqQ : (q : 𝓞 L) ∈ Q)
    (τ : L ≃ₐ[ℚ] L) (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q) :
    ∃ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ A : ValuationSubring ℚ̄, LiesOverPrime A q ∧ σ ∈ A.decompositionSubgroup ℚ := by
  obtain ⟨σ, hστ, 𝔔, hmax, hq𝔔, hσ⟩ :=
    exists_lift_mem_integral_decomposition L Q hqQ τ hτ
  have := hmax
  obtain ⟨A, hA, hσA⟩ := exists_valuation_decomposition_of_integral_stabilizer 𝔔 hq hq𝔔 σ hσ
  exact ⟨σ, hστ, A, hA, hσA⟩

end DkMath.Lib.NumberTheory.AbsoluteDecompositionLift
