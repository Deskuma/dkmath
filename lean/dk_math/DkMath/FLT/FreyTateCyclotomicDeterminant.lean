/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharactersModP
import DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll

#print "file: DkMath.FLT.FreyTateCyclotomicDeterminant"

/-!
# 同じ全 Frey Tate 作用の p 進円分行列式

同じ有限基底と全 Tate 基底の座標を標準剰余で比較する。
全非零捩れ段の実際の幾何学的 Weil 行列式を供給し、全正冪剰余の外延性で閉じる。
hclass・全段 hbad は基底構成から保持する。Frobenius や一般 hno は別の課題。
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
local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad
local notation "v" => Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad)
local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad
local notation "hb" => S.residualTatePair_base_span L hline hcofixed hζ hp5 hclass hbad
local notation "lev" => tatePairLevelEquiv S.rationalCurve v w hb
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 同じ二点列の第 n 成分による実際の有限基底。 -/
def residualTateFiniteBasis (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (p ^ (n + 1))) (Torsion S.rationalCurve (p ^ (n + 1))) :=
  (Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))).map (lev n)

local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad

/-- 同じ全点列の座標を還元すると、同じ有限点の座標になる。 -/
theorem residualTate_coordinate_reduction (x : Tate p (Points S.rationalCurve)) (n : ℕ) (i : Fin 2) :
    (fb n).repr ⟨evaluation n x, killed x n⟩ i = PadicInt.toZModPow (n + 1) ((basis).repr x i) := by
  have h := tatePairParametrization_level S.rationalCurve v w ((eqv).symm x) n
  have ha : tatePairParametrization S.rationalCurve v w ((eqv).symm x) = x := (eqv).apply_symm_apply x
  rw [ha] at h
  have hc : (lev n).symm ⟨evaluation n x, killed x n⟩ =
      (PadicInt.toZModPow (n + 1) ((eqv).symm x).1, PadicInt.toZModPow (n + 1) ((eqv).symm x).2) := by
    apply (lev n).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact h
  rw [residualTateFiniteBasis, Module.Basis.map_repr, residualTateBasis, Module.Basis.map_repr]
  change (Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))).repr
    ((lev n).symm ⟨evaluation n x, killed x n⟩) i =
    PadicInt.toZModPow (n + 1) ((Module.Basis.finTwoProd ℤ_[p]).repr ((eqv).symm x) i)
  rw [hc]
  fin_cases i <;> rfl

/-- 全基底の成分は、同じ有限基底の同じ点である。 -/
theorem residualTate_basis_reduction (n : ℕ) (j : Fin 2) :
    evaluation n (basis j) = (fb n j).val := by
  rw [residualTateBasis, Module.Basis.map_apply, residualTateFiniteBasis, Module.Basis.map_apply]
  fin_cases j
  · change evaluation n (eqv ((Module.Basis.finTwoProd ℤ_[p]) 0)) =
      (lev n ((Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))) 0)).val
    simp only [Module.Basis.finTwoProd_zero]
    rw [S.residualTateEquiv_first L hline hcofixed hζ hp5 hclass hbad]
    change evaluation n v = ((1 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (0 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [one_smul, zero_smul, add_zero]
  · change evaluation n (eqv ((Module.Basis.finTwoProd ℤ_[p]) 1)) =
      (lev n ((Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))) 1)).val
    simp only [Module.Basis.finTwoProd_one]
    rw [S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad]
    change evaluation n w = ((0 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (1 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [zero_smul, one_smul, zero_add]

/-- 実際の全 Galois 行列の各成分の剰余は、同じ有限表現の行列成分。 -/
theorem residualTate_matrix_reduction (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) (i j : Fin 2) :
    PadicInt.toZModPow (n + 1) (mat σ i j) =
      LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) i j := by
  rw [residualTateActionMatrix, LinearMap.toMatrix_apply,
    ← S.residualTate_coordinate_reduction L hline hcofixed hζ hp5 hclass hbad]
  rw [LinearMap.toMatrix_apply]
  congr 1
  apply congrArg (fb n).repr
  apply Subtype.ext
  change pointAction S.rationalCurve σ (evaluation n (basis j)) = pointAction S.rationalCurve σ (fb n j).val
  rw [S.residualTate_basis_reduction L hline hcofixed hζ hp5 hclass hbad]

/-- 各正冪精度で、実際の全行列式は同じ有限円分指標に一致する。 -/
theorem residualTate_determinant_finite (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    PadicInt.toZModPow (n + 1) (mat σ).det =
      (torsionCyclotomicCharacter (p ^ (n + 1)) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) := by
  rw [RingHom.map_det]
  have he : (mat σ).map (PadicInt.toZModPow (n + 1)) =
      LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) := by
    ext i j
    exact S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad n σ i j
  change ((mat σ).map (PadicInt.toZModPow (n + 1))).det = _
  rw [he, LinearMap.det_toMatrix]
  exact torsion_determinant_all S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (fb n) σ

/-- 全 p 冪乗根への作用から定まる、Mathlib の実際の p 進円分指標。 -/
def tateCyclotomicCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  (_root_.cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
    { toFun := fun σ => σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

local notation "cyc" => tateCyclotomicCharacter (p := p)

/-- p 進円分指標の同じ有限剰余。 -/
theorem tateCyclotomicCharacter_mod (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    PadicInt.toZModPow (n + 1) (cyc σ : ℤ_[p]) =
      (torsionCyclotomicCharacter (p ^ (n + 1)) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) := by
  exact _root_.cyclotomicCharacter.toZModPow (L := AlgebraicClosure ℚ) p σ.toRingEquiv

/-- 同じ全 Tate 作用の実際の行列式は、全 p 進精度で円分指標に一致する。 -/
theorem residualTate_determinant_cyclotomic (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).det = (cyc σ : ℤ_[p]) := by
  apply PadicCharacterLimit.ext_positive
  intro n
  rw [S.residualTate_determinant_finite L hline hcofixed hζ hp5 hclass hbad, tateCyclotomicCharacter_mod]

/-- 同じ第二指標の高位の関係。mod p だけでなく、実際の単元として一致する。 -/
theorem residualTateSecondCharacter_eq_cyclotomic (σ : Field.absoluteGaloisGroup ℚ) :
    d σ = cyc σ * (chi σ)⁻¹ := by
  have hu : chi σ * d σ = cyc σ := Units.ext
    ((S.residualTate_determinant L hline hcofixed hζ hp5 hclass hbad σ).symm.trans
      (S.residualTate_determinant_cyclotomic L hline hcofixed hζ hp5 hclass hbad σ))
  calc
    d σ = (chi σ)⁻¹ * (chi σ * d σ) := by simp
    _ = (chi σ)⁻¹ * cyc σ := by rw [hu]
    _ = cyc σ * (chi σ)⁻¹ := mul_comm _ _

end
end DkMath.FLT.Frey.Source
