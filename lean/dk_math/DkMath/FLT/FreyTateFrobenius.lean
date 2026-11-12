/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll
import DkMath.Lib.RepresentationTheory.TriangularTwoCharacteristic

#print "file: DkMath.FLT.FreyTateFrobenius"

/-!
# 同じ Frey Tate 作用の Frobenius 特性多項式と有限段二次関係

実際の同じ Frobenius 元の円分値は q。トレース係数は実際の χ∞+qχ∞⁻¹。
有限体点数 q+1-#E(Fq) との一致は本章では証明しない。
hclass・全段 hbad を保持し、一般 hno の閉鎖とも区別する。
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
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "basis" => S.residualTateBasis L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "rho" => S.residualTateMatrixRepresentation L hline hcofixed hζ hp5 hclass hbad
local notation "tri" => S.residualTateMatrixRepresentation_lower_zero L hline hcofixed hζ hp5 hclass hbad
local notation "cyc" => tateCyclotomicCharacter (p := p)
open Polynomial ValuationInertia ValuationFrobenius

/-- 実際の同じ trace。 -/
theorem residualTate_trace (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).trace = (chi σ : ℤ_[p]) + (d σ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.trace rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 実際の特性多項式の因数分解。Galois 分裂を主張しない。 -/
theorem residualTate_charpoly (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).charpoly = (X - C (chi σ : ℤ_[p])) * (X - C (d σ : ℤ_[p])) := by
  have h := TriangularTwoCharacter.charpoly_factor rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 同じ有限基底の実際のトレースは、全トレースの同じ剰余。 -/
theorem residualTate_trace_reduction (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    (LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ)).trace =
      PadicInt.toZModPow (n + 1) (mat σ).trace := by
  simp only [Matrix.trace_fin_two, map_add]
  rw [S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad,
    S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad]

/-- 同じ実際の Frobenius の p 進円分値。良還元を要求しない。 -/
theorem tateCyclotomicCharacter_frobenius {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (cyc σ : ℤ_[p]) = q :=
  CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast hq hqp A hA hσ

/-- Frobenius の実際の行列式は q。 -/
theorem residualTate_frobenius_det {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).det = (q : ℤ_[p]) := by
  rw [S.residualTate_determinant_cyclotomic L hline hcofixed hζ hp5 hclass hbad]
  exact tateCyclotomicCharacter_frobenius hq hqp A hA hσ

/-- Frobenius の実際のトレース係数。有限体点数とはまだ同定していない。 -/
theorem residualTate_frobenius_trace {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).trace = (chi σ : ℤ_[p]) + (q : ℤ_[p]) * ((chi σ)⁻¹ : ℤ_[p]ˣ) := by
  rw [S.residualTate_trace L hline hcofixed hζ hp5 hclass hbad,
    S.residualTateSecondCharacter_eq_cyclotomic L hline hcofixed hζ hp5 hclass hbad,
    Units.val_mul, tateCyclotomicCharacter_frobenius hq hqp A hA hσ]

/-- 同じ Frobenius の特性多項式の定数項を実際に q と同定する。 -/
theorem residualTate_frobenius_charpoly {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).charpoly = X ^ 2 - C ((chi σ : ℤ_[p]) +
      (q : ℤ_[p]) * ((chi σ)⁻¹ : ℤ_[p]ˣ)) * X + C (q : ℤ_[p]) := by
  rw [Matrix.charpoly_fin_two,
    S.residualTate_frobenius_trace L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ,
    S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ]

/-- 同じ全 Tate 点列そのものが満たす、実際の Frobenius 二次関係。 -/
theorem residualTate_frobenius_relation {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (x : Tate p (Points S.rationalCurve)) :
    actionLinear S.residualPointActionHom σ (actionLinear S.residualPointActionHom σ x) +
      (q : ℤ_[p]) • x = (mat σ).trace • actionLinear S.residualPointActionHom σ x := by
  exact TriangularTwoCharacter.linear_quadratic basis (actionLinear S.residualPointActionHom σ)
    (mat σ).trace (q : ℤ_[p]) rfl
    (S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ) x

/-- 同じ有限捩れ点への二次関係。新たな Cayley–Hamilton provider は不要。 -/
theorem residualTate_finite_frobenius_relation (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (P : Torsion S.rationalCurve (p ^ (n + 1))) :
    representation S.rationalCurve (p ^ (n + 1)) σ (representation S.rationalCurve (p ^ (n + 1)) σ P) +
      (q : ZMod (p ^ (n + 1))) • P =
      PadicInt.toZModPow (n + 1) (mat σ).trace • representation S.rationalCurve (p ^ (n + 1)) σ P := by
  apply TriangularTwoCharacter.linear_quadratic (fb n)
  · exact S.residualTate_trace_reduction L hline hcofixed hζ hp5 hclass hbad n σ
  · rw [LinearMap.det_toMatrix,
      torsion_determinant_all S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (fb n) σ,
      ← S.residualTate_determinant_finite L hline hcofixed hζ hp5 hclass hbad n σ]
    rw [S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ, map_natCast]

end
end DkMath.FLT.Frey.Source
