/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant

#print "file: DkMath.FLT.FreyTateFiniteQuotient"

/-!
# 同じ有限巡回段の商を記述する第二座標

実際の有限基底の第二座標は全射で、その核は元の同じ巡回段。
hclass・全段 hbad を保持し、高位商作用の自明性を仮定しない。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

/-- 同じ有限基底の第二座標。 -/
def residualFiniteSecond (n : ℕ) :
    Torsion S.rationalCurve (p ^ (n + 1)) →ₗ[ZMod (p ^ (n + 1))] ZMod (p ^ (n + 1)) where
  toFun x := (fb n).repr x 1
  map_add' x y := by simp
  map_smul' a x := by simp

local notation "second" => S.residualFiniteSecond L hline hcofixed hζ hp5 hclass hbad

/-- 第二座標は実際に全射。 -/
theorem residualFiniteSecond_surjective (n : ℕ) : Function.Surjective (second n) := by
  intro a
  refine ⟨a • fb n 1, ?_⟩
  simp [residualFiniteSecond]

/-- 有限第一基底ベクトルは以前の同じ段生成元。 -/
theorem residualFiniteBasis_first (n : ℕ) : (fb n 0).val = (gen n).val := by
  let : Fact (1 < p ^ (n + 1)) := ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)⟩
  rw [residualTateFiniteBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_zero]
  change (tatePairLevel S.rationalCurve
    (Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad))
    (S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad) n (1, 0)).val = _
  rw [tatePairLevel_val]
  simp only [ZMod.val_one, one_nsmul, ZMod.val_zero, zero_nsmul, add_zero]
  rfl

/-- 第二座標の核は、同型な別の部分群でなく元の同じ巡回段。 -/
theorem residualFiniteSecond_eq_zero_iff (n : ℕ) (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    second n x = 0 ↔ x.val ∈ (tower n).carrier := by
  constructor
  · intro hx
    have he := (fb n).sum_repr x
    rw [Fin.sum_univ_two] at he
    have hx' : (fb n).repr x 1 = 0 := hx
    rw [hx', zero_smul, add_zero] at he
    have hv := congrArg (fun z : Torsion S.rationalCurve (p ^ (n + 1)) => z.val) he
    rw [torsion_smul_val, S.residualFiniteBasis_first L hline hcofixed hζ hp5 hclass hbad] at hv
    rw [← hv]
    exact (tower n).carrier.nsmul_mem (gen n).property _
  · intro hx
    rw [← S.residualTateGenerators_generate L hline hcofixed hζ hp5 hclass hbad n] at hx
    obtain ⟨a, ha⟩ := hx
    have he : x = a • fb n 0 := by
      apply Subtype.ext
      change x.val = (torsionGroup S.rationalCurve _).subtype (a • fb n 0)
      rw [map_zsmul]
      change x.val = a • (fb n 0).val
      rw [S.residualFiniteBasis_first L hline hcofixed hζ hp5 hclass hbad]
      exact ha.symm
    rw [he, map_zsmul]
    have hz : second n (fb n 0) = 0 := by simp [residualFiniteSecond]
    rw [hz, zsmul_zero]

/-- 元の同じ段を核とする商は、標準有限環と線形同型。 -/
def residualFiniteQuotientEquiv (n : ℕ) :
    (Torsion S.rationalCurve (p ^ (n + 1)) ⧸ (second n).ker) ≃ₗ[ZMod (p ^ (n + 1))]
      ZMod (p ^ (n + 1)) :=
  (second n).quotKerEquivOfSurjective
    (S.residualFiniteSecond_surjective L hline hcofixed hζ hp5 hclass hbad n)

end
end DkMath.FLT.Frey.Source
