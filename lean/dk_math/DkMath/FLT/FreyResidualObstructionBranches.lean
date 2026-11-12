/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualObstructionMinusBranch

#print "file: DkMath.FLT.FreyResidualObstructionBranches"

/-! # 実際の残余 p 捩れ像の下での共鳴枝判定
残余 p 捩れ代表の存在と大域 cofixed 性を保持する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ残余 p 捩れ像の下では、D 固定性は q≡1 の枝とちょうど一致する。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_plus_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔ (q : ZMod p) = 1 := by
  constructor
  · intro hD
    rcases h.resonance with hplus | hminus
    · exact hplus
    · exact (h.not_decomposition_fixed_of_residual_minus hp5 hcofixed hres hminus φ hφ hD).elim
  · exact fun hplus => h.decomposition_fixed_of_residual_plus hp5 hcofixed hres hplus φ hφ

/-- 正の共鳴枝と同じ p 捩れ像から、元の連続代表を持つ非零 D 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_residual_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hq1 : (q : ZMod p) = 1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
          (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    (h.decomposition_fixed_of_residual_plus hp5 hcofixed hres hq1 φ hφ)

end
end DkMath.FLT.Frey.Source
