/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateBasis

#print "file: DkMathTest.FLT.FreyTateBasis"

namespace FreyTateBasisTest
open DkMath.FLT.Frey DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
noncomputable section
open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "v" => Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad)
local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad
local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad
local notation "hb" => S.residualTatePair_base_span L hline hcofixed hζ hp5 hclass hbad

/-- 任意の全 Tate 点列は、二つの座標への往復で同じ点列へ戻る。 -/
example (x : Tate p (Points S.rationalCurve)) : eqv ((eqv).symm x) = x := (eqv).apply_symm_apply x

/-- 元の生成元と第二点列は異なる座標を持つ。 -/
example : (eqv).symm v = (1, 0) ∧ (eqv).symm w = (0, 1) := by
  constructor
  · exact (eqv).symm_apply_eq.mpr (S.residualTateEquiv_first L hline hcofixed hζ hp5 hclass hbad).symm
  · exact (eqv).symm_apply_eq.mpr (S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad).symm

/-- 選んだ第二点列は、以前の同じ Tate 直線の外にある。 -/
example : w ∉ S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad := by
  rw [← S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad,
    S.residualTateEquiv_mem_line_iff L hline hcofixed hζ hp5 hclass hbad]
  exact one_ne_zero

/-- 第2有限段の任意の p³ 捩れ点を、同じ二点列の第2成分で表示する。 -/
example (x : Torsion S.rationalCurve (p ^ 3)) :
    ∃ a b : ℕ, x.val = a • evaluation 2 v + b • evaluation 2 w :=
  pair_span v w hb 2 x.val x.property

/-- 有限第2段の座標は全 Tate 点列ではなく実際の p³ 捩れ点も往復できる。 -/
example (x : Torsion S.rationalCurve (p ^ 3)) :
    tatePairLevelEquiv S.rationalCurve v w hb 2
      ((tatePairLevelEquiv S.rationalCurve v w hb 2).symm x) = x :=
  (tatePairLevelEquiv S.rationalCurve v w hb 2).apply_symm_apply x

/-- 行列は恒等 Galois 元で単位行列となる実際の作用行列である。 -/
example : S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad 1 = 1 := by
  simp [Source.residualTateActionMatrix]

end
end FreyTateBasisTest

#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.pair_span
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairLevelEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairCoefficients_compatible
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_injective
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairParametrization_surjective
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tatePairEquiv
#print axioms DkMath.FLT.Frey.Source.residualTateFirstReduction_ne_zero
#print axioms DkMath.FLT.Frey.Source.residualTateSecondResidual_exists
#print axioms DkMath.FLT.Frey.Source.residualTateSecond
#print axioms DkMath.FLT.Frey.Source.residualTateResidualBasis
#print axioms DkMath.FLT.Frey.Source.residualTatePair_base_span
#print axioms DkMath.FLT.Frey.Source.residualTateEquiv
#print axioms DkMath.FLT.Frey.Source.residualTateBasis
#print axioms DkMath.FLT.Frey.Source.residualTateEquiv_mem_line_iff
#print axioms DkMath.FLT.Frey.Source.residualTateActionMatrix_first_column
