/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalOrigin

#print "file: DkMath.FLT.FreyRelativeGlobalObstructionCertificate"

/-! # 分解群輸送でも残る、元の局所非零類と大域零類の係数境界
局所 F 非零性と大域 Q coboundary の零性を、同じ点について同時に証明する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

variable {T} {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害点では、局所 F 類は非零だが大域 Q 類は零。 -/
theorem NarrowAbsorptionObstruction.relative_global_class_boundary
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over x) ≠ 0 ∧
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x) = 0 := by
  constructor
  · rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    exact (h.fixed_H1_nonzero hp5).2
  · exact T.fullGlobalClass_zero _

/-- 分解群で点を輸送しても、同じ連続 F cocycle の非零性は失われない。 -/
theorem NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (σ : A.decompositionSubgroup ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    ∃ η : inertiaSubgroupIn A ℚ,
      T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
        (ResidualCyclicStage.globalTranslateTorsion σ.val x) η ≠ 0 := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
  let η : inertiaSubgroupIn A ℚ := ⟨σ.val * τ₀ * σ.val⁻¹,
    decomposition_conj_mem_inertia A σ.val τ₀ σ.property h.inertia⟩
  refine ⟨η, ?_⟩
  intro hz
  have he := T.continuousCocycle_decomposition_conjugate A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over σ η x
  have hconj : σ.val⁻¹ * η.val * σ.val = τ₀ := by dsimp [η]; group
  have harg : (⟨σ.val⁻¹ * η.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val η.val σ.property η.property⟩ :
      inertiaSubgroupIn A ℚ) = ⟨τ, h.inertia⟩ := Subtype.ext hconj
  rw [harg, hz] at he
  have hzero : T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over x
      ⟨τ, h.inertia⟩ = 0 := by
    apply T.fixedDecompositionAction_injective A σ
    simpa only [map_zero] using he.symm
  have hc := h.fixed_character_nontrivial hp5
  apply hc
  rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over] at hzero
  exact congrArg Multiplicative.ofAdd hzero

/-- 輸送後の局所 F 類も非零である一方、同じ点の大域 Q 類は零である。 -/
theorem NarrowAbsorptionObstruction.decomposition_translate_class_boundary
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (σ : A.decompositionSubgroup ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let x' := ResidualCyclicStage.globalTranslateTorsion σ.val x
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over x') ≠ 0 ∧
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x') = 0 := by
  constructor
  · rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    apply TrivialCharacterH1.class_ne_zero
    obtain ⟨η, hη⟩ := h.decomposition_translate_continuous_nonzero hp5 σ
    refine ⟨η, ?_⟩
    intro he
    apply hη
    rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    exact congrArg Multiplicative.toAdd he
  · exact T.fullGlobalClass_zero _
end
end DkMath.FLT.Frey.Source

