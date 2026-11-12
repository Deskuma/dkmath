/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNarrowFailureGeometry
import DkMath.FLT.FreyConditionalCofixedExclusion

#print "file: DkMath.FLT.FreyCofixedArithmeticObstruction"

/-!
# 類群消滅と Cofixed から生じる狭い吸収の幾何学的障害

失敗点は p 倍逆像の領域内。差点は滑らかで慣性固定、元の段生成元は非滑らか。
この配置の排除を証明したとは扱わない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre EllipticTangentDirections ValuationInertia
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 狭い吸収の失敗を、同じ段・点・差点・生成元の幾何と一緒に保持する論理的証明書。
数値的な証人計算アルゴリズムではなく、実際の対象に対する存在証明の出力である。 -/
structure NarrowAbsorptionObstruction (L : Submodule (ZMod p) S.ResidualSpace)
    {n : ℕ} (T : S.ResidualCyclicStage L n) (q : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (τ : Field.absoluteGaloisGroup ℚ) (y : Points S.rationalCurve) : Prop where
  prime : q.Prime
  ne_torsion_prime : q ≠ p
  five_le : 5 ≤ q
  support : (q : ℤ) ∣ S.a * S.b * S.c
  resonance : (q : ZMod p) = 1 ∨ (q : ZMod p) = -1
  lies_over : LiesOverPrime A q
  inertia : τ ∈ inertiaSubgroupIn A ℚ
  preimage : p • y ∈ T.carrier
  escapes : pointAction S.rationalCurve τ y - y ∉ T.carrier
  killed : p ^ (n + 1 + 1) • y = 0
  difference_killed : p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0
  difference_smooth : HasSmoothReduction (S.valuationModel A) (pointAction S.rationalCurve τ y - y)
  difference_fixed : ∀ σ ∈ inertiaSubgroupIn A ℚ, pointAction S.rationalCurve σ
    (pointAction S.rationalCurve τ y - y) = pointAction S.rationalCurve τ y - y
  difference_p_mem : p • (pointAction S.rationalCurve τ y - y) ∈ T.carrier
  difference_ne_zero : pointAction S.rationalCurve τ y - y ≠ 0
  generator_not_smooth : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val
  generator_depth : ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
    Nonempty (TangentDirections C) ∧ ∃ x z : AlgebraicClosure ℚ,
    ∃ h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x z,
      (T.coordinates 1).val = WeierstrassCurve.Affine.Point.some x z h ∧ A.valuation (x - C.x) < 1
end DkMath.FLT.Frey.Source

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

include hline hζ hp5 hclass in
/-- hclass と同じ Cofixed 候補から、実際の狭い失敗点の幾何学的証明書を得る。
全段 hbad や生成元の配置を入力しない。 -/
theorem residual_exists_narrow_geometric_obstruction
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), S.NarrowAbsorptionObstruction L T q A τ y := by
  obtain ⟨n, T, q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail⟩ :=
    S.residual_exists_narrow_absorption_counterexample L hline hζ hp5 hclass hcofixed
  obtain ⟨hk, hd, hsm, hfix, hpmem, hne⟩ :=
    T.narrow_failure_profile hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail
  refine ⟨n, T, q, A, τ, y, ⟨hq, hqp, hq5, hs, hr, hA, hτ, hy, hfail,
    hk, hd, hsm, hfix, hpmem, hne, ?_, ?_⟩⟩
  · exact T.generator_not_smooth_of_narrow_failure hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail
  · exact T.exists_generator_depth_of_narrow_failure hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail

end
end DkMath.FLT.Frey.Source
