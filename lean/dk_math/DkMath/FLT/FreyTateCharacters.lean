/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateBasis
import DkMath.Lib.RepresentationTheory.TriangularTwoCharacter

#print "file: DkMath.FLT.FreyTateCharacters"

/-!
# 同じ Frey Tate 作用の第二単元値指標と連続性

実際の行列準同型から第二対角指標を構成する。各有限剰余の核は
同じ全捩れ表現の開核を含むので連続となる。指標値1や分裂は仮定しない。
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
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad

/-- 同じ実際の全線形作用を同じ基底で行列化した群準同型。 -/
def residualTateMatrixRepresentation : Field.absoluteGaloisGroup ℚ →* Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  (LinearMap.toMatrixAlgEquiv basis).toMonoidHom.comp (actionLinear S.residualPointActionHom)

local notation "rho" => S.residualTateMatrixRepresentation L hline hcofixed hζ hp5 hclass hbad

theorem residualTateMatrixRepresentation_apply (σ : Field.absoluteGaloisGroup ℚ) : rho σ = mat σ := rfl

/-- 既存の第一列の零から得た、実際の上三角性。 -/
theorem residualTateMatrixRepresentation_lower_zero (σ : Field.absoluteGaloisGroup ℚ) : rho σ 1 0 = 0 :=
  (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).2

local notation "tri" => S.residualTateMatrixRepresentation_lower_zero L hline hcofixed hζ hp5 hclass hbad

/-- 第一対角指標は、以前の同じ p 進指標そのもの。 -/
theorem residualTateMatrix_first_character : TriangularTwoCharacter.first rho tri = chi := by
  apply MonoidHom.ext; intro σ
  apply Units.ext
  exact (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).1

/-- 群の逆元から可逆性を証明した同じ第二対角指標。 -/
def residualTateSecondCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  TriangularTwoCharacter.second rho tri

local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad

theorem residualTateSecondCharacter_coe (σ : Field.absoluteGaloisGroup ℚ) : (d σ : ℤ_[p]) = mat σ 1 1 := rfl

/-- 第二点列を動かした時の第二座標は、同じ行列の第二対角成分。 -/
theorem residualTateSecond_coordinate (σ : Field.absoluteGaloisGroup ℚ) :
    ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 = (d σ : ℤ_[p]) := by
  have h1 : basis 1 = w := by
    rw [residualTateBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_one]
    exact S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad
  rw [residualTateSecondCharacter_coe, residualTateActionMatrix, LinearMap.toMatrix_apply, h1,
    residualTateBasis, Module.Basis.map_repr]
  rfl

/-- 非対角成分の積公式。零や Galois 分裂は結論しない。 -/
theorem residualTate_offDiagonal_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    mat (σ * τ) 0 1 = (chi σ : ℤ_[p]) * mat τ 0 1 + mat σ 0 1 * (d τ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.offDiagonal_mul rho tri σ τ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 実際の行列式の積表示。高位円分指標との一致ではない。 -/
theorem residualTate_determinant (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).det = (chi σ : ℤ_[p]) * (d σ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.determinant rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 同じ全捩れ作用の核の元は、第二指標の同じ有限剰余の核に入る。 -/
theorem residualTateSecondCharacter_finite_kernel (n : ℕ) :
    representationKernel S.rationalCurve (p ^ (n + 1)) ≤ (PadicCharacterLimit.reductions d n).ker := by
  intro σ hσ
  change Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (d σ) = 1
  apply Units.ext
  change PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1
  let a := (eqv).symm (actionLinear S.residualPointActionHom σ w)
  have ha : tatePairParametrization S.rationalCurve v w a = actionLinear S.residualPointActionHom σ w :=
    (eqv).apply_symm_apply _
  have hpt : pointAction S.rationalCurve σ (evaluation n w) = evaluation n w := by
    change representation S.rationalCurve (p ^ (n + 1)) σ = 1 at hσ
    have he := congrArg (fun f : Module.End (ZMod (p ^ (n + 1))) (Torsion S.rationalCurve (p ^ (n + 1))) =>
      f ⟨evaluation n w, killed w n⟩) hσ
    exact congrArg Subtype.val he
  have he := congrArg (evaluation n) ha
  rw [tatePairParametrization_level] at he
  change _ = pointAction S.rationalCurve σ (evaluation n w) at he
  rw [hpt] at he
  have hi : (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2) = (0, 1) := by
    apply (tatePairLevelEquiv S.rationalCurve v w hb n).injective
    apply Subtype.ext
    change (tatePairLevel S.rationalCurve v w n
      (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2)).val =
      (tatePairLevel S.rationalCurve v w n (0, 1)).val
    change _ = ((0 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (1 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [zero_smul, one_smul, zero_add]
    exact he
  have hs := congrArg Prod.snd hi
  change PadicInt.toZModPow (n + 1) ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 = 1 at hs
  rw [S.residualTateSecond_coordinate L hline hcofixed hζ hp5 hclass hbad] at hs
  exact hs

/-- 第二指標の各有限剰余は、実際に開核を持つ。 -/
theorem residualTateSecondCharacter_finite_kernel_isOpen (n : ℕ) :
    IsOpen ((PadicCharacterLimit.reductions d n).ker : Set (Field.absoluteGaloisGroup ℚ)) :=
  Subgroup.isOpen_mono
    (S.residualTateSecondCharacter_finite_kernel L hline hcofixed hζ hp5 hclass hbad n)
    (representationKernel_isOpen_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- 第二単元値指標は連続。新しい連続性・開核 provider は不要。 -/
theorem residualTateSecondCharacter_continuous : Continuous d :=
  PadicCharacterLimit.continuous_of_reduction_kernels d
    (S.residualTateSecondCharacter_finite_kernel_isOpen L hline hcofixed hζ hp5 hclass hbad)

end
end DkMath.FLT.Frey.Source
