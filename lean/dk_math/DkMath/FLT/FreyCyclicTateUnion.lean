/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateLine
import DkMath.Lib.Algebra.CyclicPrimePowerTorsion

#print "file: DkMath.FLT.FreyCyclicTateUnion"

/-!
# 同じ合併の全 p 冪捩れと標準 Tate 加群の同定

U[p^(n+1)]=Kₙ を同じ巡回段の濃度から証明する。
標準の Tate p U から同じ既存直線への自然な線形同型を作り、
同じ全点群への包含と Galois 作用を保つ。hclass・全段 hbad は保持する。
全 Tate 加群の階数2や Frobenius 特性多項式、一般 hno はまだ証明しない。
-/

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
noncomputable section

section Stages
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n m : ℕ}

/-- 同じ大きい巡回段の低位捩れは、含まれる同じ小さい段全体。
既存段の群論であり、hclass/hbad を新たに要求しない。 -/
theorem ResidualCyclicStage.mem_iff_killed_in_later
    (T : S.ResidualCyclicStage L n) (V : S.ResidualCyclicStage L m)
    (hnm : n ≤ m) (hTV : T.carrier ≤ V.carrier) (x : Points S.rationalCurve) :
    x ∈ T.carrier ↔ x ∈ V.carrier ∧ p ^ (n + 1) • x = 0 := by
  let := V.finite
  let := V.cyclic
  exact CyclicPrimePowerTorsion.mem_iff_killed (Nat.add_le_add_right hnm 1)
    V.carrier T.carrier V.card hTV T.card T.killed
end Stages

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
local notation "union" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 同じ合併の全ての p^(n+1) 捩れは、正確に同じ第 n 段である。 -/
theorem residualCyclicTowerUnion_torsion (n : ℕ) (x : Points S.rationalCurve) :
    (x ∈ union ∧ p ^ (n + 1) • x = 0) ↔ x ∈ (tower n).carrier := by
  constructor
  · rintro ⟨hx, hk⟩
    obtain ⟨m, hm⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    by_cases hnm : n ≤ m
    · exact ((tower n).mem_iff_killed_in_later (tower m) hnm
        (S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad hnm) x).mpr ⟨hm, hk⟩
    · exact S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad (by omega : m ≤ n) hm
  · intro hx
    exact ⟨(S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr ⟨n, hx⟩,
      (tower n).killed x hx⟩

/-- 標準 Tate p U の全点群への包含。成分は元の同じ点である。 -/
def residualUnionTate_inclusion : Tate p (union) →ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) :=
  mapLinear (union).subtype

theorem residualUnionTate_inclusion_injective :
    Function.Injective (S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  map_injective (union).subtype Subtype.val_injective

/-- 標準 Tate p U の零化条件を使って、各成分を同じ段へ戻す線形写像。 -/
def residualUnionTateToLine : Tate p (union) →ₗ[ℤ_[p]] line where
  toFun x := ⟨S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x, fun n => by
    apply (S.residualCyclicTowerUnion_torsion L hline hcofixed hζ hp5 hclass hbad n (evaluation n x).val).mp
    refine ⟨(evaluation n x).property, ?_⟩
    have h := congrArg (union).subtype (killed x n)
    rw [map_nsmul, map_zero] at h
    exact h⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' a x := Subtype.ext (map_smul _ a x)

local notation "toLine" => S.residualUnionTateToLine L hline hcofixed hζ hp5 hclass hbad

/-- 標準 Tate p U と以前の同じ Tate 直線の自然な線形同型。
逆向きは各有限段の点を同じ合併内の点とみなすだけである。 -/
def residualUnionTateLineEquiv : Tate p (union) ≃ₗ[ℤ_[p]] line :=
  LinearEquiv.ofBijective toLine ⟨by
    intro x y h
    apply S.residualUnionTate_inclusion_injective L hline hcofixed hζ hp5 hclass hbad
    exact congrArg Subtype.val h, by
    intro x
    let y : Tate p (union) := ⟨fun n => ⟨evaluation n x.val,
      (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr ⟨n, x.property n⟩⟩,
      ⟨fun n => Subtype.ext (killed x.val n), fun n => Subtype.ext (compatible x.val n)⟩⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply PrimePowerTateSequence.ext
    intro n
    rfl⟩

/-- 標準 Tate p U 自体が自由階数1であることを与える同じ線形同型。 -/
def residualUnionTateEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] Tate p (union) :=
  (S.residualCyclicTateLineEquiv L hline hcofixed hζ hp5 hclass hbad).trans
    (S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad).symm

/-- 自然な同定の前後で全点群の Tate 加群内の点列は変わらない。 -/
theorem residualUnionTateLineEquiv_inclusion (x : Tate p (union)) :
    S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad
      (S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad x) =
    S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x := rfl

/-- 同じ合併への元の実際の点作用の制限。 -/
def residualTowerUnionAction : Field.absoluteGaloisGroup ℚ →* AddMonoid.End (union) where
  toFun σ :=
    { toFun := fun x => ⟨pointAction S.rationalCurve σ x.val,
        S.residualCyclicTowerUnion_stable L hline hcofixed hζ hp5 hclass hbad σ x.val x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext; intro x
    exact Subtype.ext (pointAction_one S.rationalCurve x.val)
  map_mul' σ τ := by
    apply AddMonoidHom.ext; intro x
    exact Subtype.ext (pointAction_mul S.rationalCurve σ τ x.val)

local notation "uAction" => S.residualTowerUnionAction L hline hcofixed hζ hp5 hclass hbad

/-- 標準 Tate p U への包含は同じ実際の線形 Galois 作用と可換。 -/
theorem residualUnionTate_inclusion_equivariant (σ : Field.absoluteGaloisGroup ℚ) (x : Tate p (union)) :
    S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad (actionLinear uAction σ x) =
    actionLinear S.residualPointActionHom σ
      (S.residualUnionTate_inclusion L hline hcofixed hζ hp5 hclass hbad x) := rfl

/-- 同じ標準 Tate p U の全ての点列への作用は、元の同じ指標の scalar 倍。 -/
theorem residualUnionTate_action_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : Tate p (union)) :
    actionLinear uAction σ x = (padicChar σ : ℤ_[p]) • x := by
  apply S.residualUnionTate_inclusion_injective L hline hcofixed hζ hp5 hclass hbad
  rw [S.residualUnionTate_inclusion_equivariant L hline hcofixed hζ hp5 hclass hbad, map_smul]
  exact S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ (toLine x)

/-- 元の非零生成元点列は、全 Tate 加群の p 倍には入らない。
第0成分の非零性で検出する。全 Tate 加群の階数2は仮定しない。 -/
theorem residualCyclicTateVector_not_p_multiple (w : Tate p (Points S.rationalCurve)) :
    (p : ℤ_[p]) • w ≠ (vec).val := by
  intro h
  have hz : evaluation 0 ((p : ℤ_[p]) • w) = 0 := by
    rw [evaluation_smul, map_natCast]
    have he := nsmul_eq_of_residue (evaluation 0 w) (killed w 0)
      (ZMod.natCast_zmod_val (p : ZMod (p ^ (0 + 1))))
    exact he.trans (by simpa only [Nat.zero_add, pow_one] using killed w 0)
  have he := congrArg (evaluation 0) h
  rw [hz] at he
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  exact Subtype.ext he.symm

end
end DkMath.FLT.Frey.Source
