/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaCharacters
import DkMath.FLT.FreyTateResonantWitness

#print "file: DkMath.FLT.FreyConditionalCofixedExclusion"

/-!
# 実際の局所ユニポテンスで条件付き Cofixed 排除を閉じる

前回の高位失敗証人を排除し、hclass と全段の狭い hbad のもとで矛盾を得る。
同じ hclass と Cofixed のもとでは狭い hbad 自体の失敗段も存在する。
一般 hno に対する算術入力の無条件供給は別問題である。
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
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)

include hline hζ hp5 hclass hbad in
/-- 既存の類群消滅と全段の狭い吸収を保持した、同じ直線の Cofixed 排除。
新しいユニポテンス・高位吸収・慣性自明性 provider は要求しない。 -/
theorem residual_not_cofixed_of_class_vanishing_and_resonant_absorption :
    ¬ IsCofixedOn S.residualRepresentation L := by
  intro hcofixed
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, hd⟩ :=
    S.residualSecond_nontrivial_resonant_inertia L hline hcofixed hζ hp5 hclass hbad
  exact hd (S.residualTateSecondCharacter_inertia_eq_one L hline hcofixed hζ hp5 hclass hbad
    hq hqp (Or.inr hs) A hA τ hτ)

include hline hζ hp5 hclass in
/-- Cofixed な同じ直線では、類群消滅を保持すると、従来の狭い hbad 自体が失敗する段がある。 -/
theorem residual_exists_narrow_absorption_failure
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n), ¬ S.ResonantAbsorptionAt T.carrier := by
  classical
  by_contra h
  push Not at h
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L hline hζ hp5 hclass h hcofixed

include hline hζ hp5 hclass in
/-- 同じ hclass と Cofixed のもとでは、狭い条件の領域内に実際の失敗点が存在する。
全段 hbad をこの定理の入力には要求しない。 -/
theorem residual_exists_narrow_absorption_counterexample
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n),
      ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
        ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p • y ∈ T.carrier ∧
        pointAction S.rationalCurve τ y - y ∉ T.carrier := by
  classical
  obtain ⟨n, T, hf⟩ := S.residual_exists_narrow_absorption_failure L hline hζ hp5 hclass hcofixed
  refine ⟨n, T, ?_⟩
  unfold ResonantAbsorptionAt at hf
  push Not at hf
  exact hf

include hζ hp5 hclass in
/-- 既存の hno 入口と同じ安定直線の不存在。残る入力は類群消滅と全直線・全段の狭い吸収。 -/
theorem residual_hno_of_class_vanishing_and_resonant_absorption
    (hbadAll : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L' = 1 ∧
      S.IsGaloisStable L' ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', _, hc⟩
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L' hline' hζ hp5 hclass (hbadAll L' hline') hc

end
end DkMath.FLT.Frey.Source
