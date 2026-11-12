/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem, P2M/Sol/S_NumberField_exists_lift_mem_inertia_integralClosure.lean.
Upstream blob: 8bcd2f8014a5e5a4d662d04860376e53c208bbea
Modified for DkMath: named arithmetic interfaces, textbook explanations,
separate absolute-inertia layers, and current Mathlib APIs.
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Profinite
#print "file: DkMath.Lib.NumberTheory.IntegralClosureInertiaLift"

/-!
# NOTE-031-001B: 有限慣性元を代数閉包の整数閉包へ持ち上げる

有限正規中間体Lの素点Qで慣性に属するτを取る。まずτを絶対ガロア元σ₀へ延長する。
整数閉包の上の素点をL上の自己同型で調整し、σ₀をその素点の安定化群へ移す。
その剰余体作用はLの剰余体を固定する。profinite不変式論の剰余体作用の全射性で
この残る作用を打ち消すと、元のτを保ったまま剰余体作用が恒等となる。

結論は整数閉包の各bについてσb−bが同じ極大イデアルに属するという実際の合同である。
付値環全体の慣性群への接続は次の章で行う。持ち上げの存在を仮定に置かない。
-/
namespace DkMath.Lib.NumberTheory.IntegralClosureInertiaLift

open scoped NumberField Pointwise

set_option autoImplicit false

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝔅" => integralClosure ℤ (AlgebraicClosure ℚ)

/-- 有限正規中間体の実際の慣性元は、整数閉包のある極大イデアルを法として
全整数元を固定する絶対ガロア元へ持ち上がる。指定されたqの所属も同じ素点に保つ。 -/
theorem exists_lift_mem_inertia_integralClosure
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsMaximal] {q : ℕ}
    (hqQ : (q : NumberField.RingOfIntegers L) ∈ Q) (τ : L ≃ₐ[ℚ] L)
    (hτ : τ ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)), 𝔔.IsMaximal ∧
        (q : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ 𝔔 ∧
        ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), ∃ c ∈ 𝔔,
          (c : AlgebraicClosure ℚ) = σ b - b := by
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
  have hτ' : ∀ x : 𝓞 L, τ • x - x ∈ Q := fun x => (AddSubgroup.mem_inertia.mp hτ) x
  have hstabτ : τ • Q = Q := Ideal.inertia_le_stabilizer Q hτ
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
  have hσ₁stab : rsh g * σ₀ ∈ MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) 𝔔 := hσ₁𝔔
  let φ₀ : (𝔅 ⧸ 𝔔) ≃ₐ[ℤ ⧸ 𝔔.under ℤ] (𝔅 ⧸ 𝔔) :=
    Ideal.Quotient.stabilizerHom 𝔔 (𝔔.under ℤ) (ℚ̄ ≃ₐ[ℚ] ℚ̄) ⟨rsh g * σ₀, hσ₁stab⟩
  have hφ₀ : ∀ b : 𝔅, φ₀ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  have hστQ : ∀ x : 𝓞 L, Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • algebraMap (𝓞 L) 𝔅 x) =
      Ideal.Quotient.mk 𝔔 (algebraMap (𝓞 L) 𝔅 x) := by
    intro x
    rw [Ideal.Quotient.eq, hres, hσ₁L, ← map_sub, hmemQ]
    exact hτ' x
  let φ : (𝔅 ⧸ 𝔔) ≃ₐ[𝓞 L ⧸ Q] (𝔅 ⧸ 𝔔) :=
    AlgEquiv.ofRingEquiv (f := (φ₀ : (𝔅 ⧸ 𝔔) ≃+* (𝔅 ⧸ 𝔔))) (by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      exact hστQ x)
  have hφ : ∀ b : 𝔅, φ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  -- 剰余体作用を持ち上げ、その逆元で補正する。Lへの制限は変わらない。
  obtain ⟨t, ht⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := ℚ̄ ≃ₐ[L] ℚ̄) Q 𝔔 φ
  have ht' : ∀ b : 𝔅, Ideal.Quotient.mk 𝔔 ((t : ℚ̄ ≃ₐ[L] ℚ̄) • b) =
      Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) := by
    intro b
    have h := congrArg (fun e => e (Ideal.Quotient.mk 𝔔 b)) ht
    simp only [Ideal.Quotient.stabilizerHom_apply, hφ] at h
    exact h
  refine ⟨(rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀), ?_, 𝔔, h𝔔max, ?_, ?_⟩
  · rw [map_mul, map_inv, hresL, inv_one, one_mul, hσ₁L]
  · have h : algebraMap (𝓞 L) 𝔅 (q : 𝓞 L) ∈ 𝔔 := (hmemQ _).mpr hqQ
    simpa only [map_natCast] using h
  · intro b
    refine ⟨((rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀)) • b - b, ?_, rfl⟩
    have h1 : (rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b ∈ 𝔔 := by
      rw [← Ideal.Quotient.eq]
      exact (ht' b).symm
    have h2 : ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄) •
        ((rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b) ∈ 𝔔 := by
      have hmem := (Ideal.smul_mem_pointwise_smul_iff
        (a := ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄))).mpr h1
      rwa [MulAction.mem_stabilizer_iff.mp (t⁻¹).2] at hmem
    have h3 : ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄) •
        ((rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b) =
        ((rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀)) • b - b := by
      rw [Subgroup.coe_inv, smul_sub, inv_smul_smul, hrs, map_inv]
      simp only [mul_smul]
    rw [← h3]
    exact h2

end DkMath.Lib.NumberTheory.IntegralClosureInertiaLift
