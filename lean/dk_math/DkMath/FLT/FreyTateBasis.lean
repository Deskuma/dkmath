/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateReduction
import DkMath.FLT.FreyResidualRankTwo
import DkMath.Lib.NumberTheory.EllipticTatePairBasis
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.ToLin

#print "file: DkMath.FLT.FreyTateBasis"

/-!
# 元の Frey 互換生成元を第一ベクトルに持つ全 Tate 加群の基底

同じ E[p] の次元2から第二残余点を選び、実際の第0評価で持ち上げる。
有限捩れ濃度と互換係数復元によって全 Tate 加群の自由階数2を構成する。
同じ第一ベクトルへの既存の指標作用は、実際の作用行列の第一列になる。
hclass と全段 hbad は保持し、行列式や Frobenius の最終算術はまだ証明しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
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
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "v" => Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad)
local notation "P" => tateReduction S.rationalCurve p v
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 元の第一点列の残余点は同じ非零 seed。 -/
theorem residualTateFirstReduction_ne_zero : P ≠ 0 := by
  intro h
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  have he : evaluation 0 v = 0 := congrArg (fun z : S.ResidualSpace => z.val) h
  exact Subtype.ext he

/-- 同じ残余空間の実際の次元2から、第一点と独立な第二点が存在する。 -/
theorem residualTateSecondResidual_exists : ∃ q : S.ResidualSpace, LinearIndependent (ZMod p) ![P, q] :=
  exists_linearIndependent_pair_of_one_lt_finrank (by rw [S.residual_finrank_eq_two]; decide)
    (S.residualTateFirstReduction_ne_zero L hline hcofixed hζ hp5 hclass hbad)

def residualTateSecondResidual : S.ResidualSpace :=
  (S.residualTateSecondResidual_exists L hline hcofixed hζ hp5 hclass hbad).choose

local notation "Q" => S.residualTateSecondResidual L hline hcofixed hζ hp5 hclass hbad

theorem residualTateResidualPair_independent : LinearIndependent (ZMod p) ![P, Q] :=
  (S.residualTateSecondResidual_exists L hline hcofixed hζ hp5 hclass hbad).choose_spec

/-- 第二残余点を、同じ曲線の実際の Tate 点列へ持ち上げる。 -/
def residualTateSecond : Tate p (Points S.rationalCurve) :=
  (tateReduction_surjective S.rationalCurve p Q).choose

local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad

theorem residualTateSecond_reduction : tateReduction S.rationalCurve p w = Q :=
  (tateReduction_surjective S.rationalCurve p Q).choose_spec

/-- 同じ第一残余点を含む実際の二次元基底。 -/
def residualTateResidualBasis : Module.Basis (Fin 2) (ZMod p) S.ResidualSpace :=
  Module.Basis.mk (S.residualTateResidualPair_independent L hline hcofixed hζ hp5 hclass hbad)
    ((S.residualTateResidualPair_independent L hline hcofixed hζ hp5 hclass hbad).span_eq_top_of_card_eq_finrank
      (by simp only [Fintype.card_fin, S.residual_finrank_eq_two])).ge

/-- 同じ二つの点列の第0成分は、実際の E[p] 全体を生成する。 -/
theorem residualTatePair_base_span (x : Points S.rationalCurve) (hx : p • x = 0) :
    ∃ a b : ℕ, x = a • evaluation 0 v + b • evaluation 0 w := by
  let b := S.residualTateResidualBasis L hline hcofixed hζ hp5 hclass hbad
  let t : S.ResidualSpace := ⟨x, hx⟩
  have hb0 : b 0 = P := by simp only [b, residualTateResidualBasis, Module.Basis.coe_mk, Matrix.cons_val_zero]
  have hb1 : b 1 = Q := by simp only [b, residualTateResidualBasis, Module.Basis.coe_mk, Matrix.cons_val_one, Matrix.cons_val_zero]
  have he := congrArg (torsionGroup S.rationalCurve p).subtype (b.sum_repr t)
  rw [Fin.sum_univ_two, map_add] at he
  change ((b.repr t 0) • b 0).val + ((b.repr t 1) • b 1).val = x at he
  rw [torsion_smul_val, torsion_smul_val, hb0, hb1] at he
  have hw := congrArg Subtype.val (S.residualTateSecond_reduction L hline hcofixed hζ hp5 hclass hbad)
  change evaluation 0 w = (Q).val at hw
  change (b.repr t 0).val • evaluation 0 v + (b.repr t 1).val • (Q).val = x at he
  rw [← hw] at he
  exact ⟨(b.repr t 0).val, (b.repr t 1).val, he.symm⟩

/-- 全 Tate 加群の実際の二成分表示。第一ベクトルは元の同じ v。 -/
def residualTateEquiv : (ℤ_[p] × ℤ_[p]) ≃ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) :=
  tatePairEquiv S.rationalCurve v w (S.residualTatePair_base_span L hline hcofixed hζ hp5 hclass hbad)

local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad

theorem residualTateEquiv_first : eqv (1, 0) = v := by
  change (1 : ℤ_[p]) • v + (0 : ℤ_[p]) • w = v
  simp

theorem residualTateEquiv_second : eqv (0, 1) = w := by
  change (0 : ℤ_[p]) • v + (1 : ℤ_[p]) • w = w
  simp

/-- 既存の同じ Tate 直線は、新しい座標の正確な第一成分である。 -/
theorem residualTateEquiv_mem_line_iff (a b : ℤ_[p]) :
    eqv (a, b) ∈ S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad ↔ b = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := S.residualCyclicTateParametrization_surjective L hline hcofixed hζ hp5 hclass hbad ⟨eqv (a, b), h⟩
    have he : eqv (c, 0) = eqv (a, b) := by
      change c • v + (0 : ℤ_[p]) • w = _
      rw [zero_smul, add_zero]
      have he := congrArg (fun x : S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad => x.val) hc
      change c • v = eqv (a, b) at he
      exact he
    exact (congrArg Prod.snd ((eqv).injective he)).symm
  · intro h
    subst b
    change a • v + (0 : ℤ_[p]) • w ∈ _
    rw [zero_smul, add_zero]
    exact (S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad).smul_mem a (vec).property

/-- 実際の全 Tate 加群の Fin 2 基底。 -/
def residualTateBasis : Module.Basis (Fin 2) ℤ_[p] (Tate p (Points S.rationalCurve)) :=
  (Module.Basis.finTwoProd ℤ_[p]).map eqv

local notation "basis" => S.residualTateBasis L hline hcofixed hζ hp5 hclass hbad

theorem residualTateBasis_first : basis 0 = v := by
  rw [residualTateBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_zero]
  exact S.residualTateEquiv_first L hline hcofixed hζ hp5 hclass hbad

/-- 同じ実際の全 Galois 線形作用の、この基底での行列。 -/
def residualTateActionMatrix (σ : Field.absoluteGaloisGroup ℚ) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  LinearMap.toMatrix basis basis (actionLinear S.residualPointActionHom σ)

/-- 第一列は元の指標と0。基底と同じ作用から導き、三角性を仮定しない。 -/
theorem residualTateActionMatrix_first_column (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) 0 0 = (padicChar σ : ℤ_[p]) ∧
    (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) 1 0 = 0 := by
  have hv : actionLinear S.residualPointActionHom σ v = (padicChar σ : ℤ_[p]) • v :=
    S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ
      ⟨v, (vec).property⟩
  have hcol (i : Fin 2) : (S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad σ) i 0 =
      (padicChar σ : ℤ_[p]) * (if i = 0 then 1 else 0) := by
    rw [residualTateActionMatrix, LinearMap.toMatrix_apply,
      S.residualTateBasis_first L hline hcofixed hζ hp5 hclass hbad, hv,
      ← S.residualTateBasis_first L hline hcofixed hζ hp5 hclass hbad, map_smul]
    by_cases hi : i = 0
    · subst i; simp
    · simp [hi]
  exact ⟨by simpa using hcol 0, by simpa using hcol 1⟩

end
end DkMath.FLT.Frey.Source
