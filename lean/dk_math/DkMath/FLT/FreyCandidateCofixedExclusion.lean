/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction

#print "file: DkMath.FLT.FreyCandidateCofixedExclusion"

/-!
# Cofixed 候補だけの算術入力で足りる hno

全直線の吸収入力を Cofixed 候補に限定する。滑らかな生成元による十分条件も公開するが、
配置を実装したとは主張しない。無条件の一般 hno は依然として別工程。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hζ hp5 hclass in
/-- 狭い吸収を全直線でなく Cofixed 候補だけに要求する hno。
Cofixed から安定性が従うので、強い結論では安定性を重複要求しない。 -/
theorem residual_no_cofixed_of_candidate_absorption
    (hbadCandidate : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L' = 1 ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', hc⟩
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L' hline' hζ hp5 hclass (hbadCandidate L' hline' hc) hc

include hζ hp5 hclass in
/-- 既存 hno と同じ形への接続。候補以外の直線の吸収を要求しない。 -/
theorem residual_hno_of_candidate_absorption
    (hbadCandidate : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L' = 1 ∧
      S.IsGaloisStable L' ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', _, hc⟩
  exact S.residual_no_cofixed_of_candidate_absorption hζ hp5 hclass hbadCandidate ⟨L', hline', hc⟩

include hζ hp5 hclass in
/-- 候補段の座標生成元の滑らかな配置が供給されれば、狭い吸収は内部証明できる。
この配置条件そのものは未証明の算術入力として明示する。 -/
theorem residual_no_cofixed_of_candidate_smooth_generators
    (hplacement : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n),
      ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        EllipticGoodReductionSeparation.HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L' = 1 ∧ IsCofixedOn S.residualRepresentation L' := by
  apply S.residual_no_cofixed_of_candidate_absorption hζ hp5 hclass
  intro L' hl hc n T q hq hqp hq5 hs hr A hA τ hτ y hy
  have hsm := (T.le_iff_generator_mem (S.valuationSmoothSubgroup A)).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr (hplacement L' hl hc n T q hq hqp hq5 hs hr A hA))
  exact T.preimage_absorbs_of_smooth hp5 hq hqp (Or.inr hs) A hA hsm τ hτ hy

end
end DkMath.FLT.Frey.Source
