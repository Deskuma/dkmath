/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateUnion

#print "file: DkMathTest.FLT.FreyCyclicTateUnion"

namespace FreyCyclicTateUnionTest
open DkMath.Lib.Algebra

/-- ZMod 125 内の実際の25捩れ。 -/
def small : AddSubgroup (ZMod 125) := (nsmulAddMonoidHom 25).ker

example (x : ZMod 125) : x ∈ small ↔ (25 : ℕ) • x = 0 := by
  have hB : Nat.card small = 5 ^ 2 := by
    rw [small, IsAddCyclic.card_nsmulAddMonoidHom_ker]
    norm_num
  have h := CyclicPrimePowerTorsion.mem_iff_killed (p := 5) (a := 2) (b := 3) (by omega)
    (⊤ : AddSubgroup (ZMod 125)) small (by norm_num [AddSubgroup.card_top])
    le_top hB (fun _ hx => hx) (x := x)
  simpa only [AddSubgroup.mem_top, true_and, show (5 : ℕ) ^ 2 = 25 by norm_num] using h

example : (5 : ZMod 125) ∈ small ∧ (1 : ZMod 125) ∉ small := by
  change (25 : ℕ) • (5 : ZMod 125) = 0 ∧ (25 : ℕ) • (1 : ZMod 125) ≠ 0
  decide

/-- 非巡回群では、小さい位数5の部分群以外にも5捩れがある。
巡回性の仮定を落とす誤用を防ぐ具体的な点。 -/
example : (5 : ℕ) • ((0, 1) : ZMod 5 × ZMod 5) = 0 ∧
    ((0, 1) : ZMod 5 × ZMod 5) ∉ (AddMonoidHom.snd (ZMod 5) (ZMod 5)).ker := by decide

end FreyCyclicTateUnionTest

namespace FreyCyclicTateUnionSourceTest
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "union" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad
local notation "eqv" => S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad

/-- 合併に属する p² 捩れは、どの後段から来ても同じ第1段へ戻る。 -/
example (x : Points S.rationalCurve) (hx : x ∈ (tower 4).carrier) (hk : p ^ 2 • x = 0) :
    x ∈ (tower 1).carrier := by
  apply (S.residualCyclicTowerUnion_torsion L hline hcofixed hζ hp5 hclass hbad 1 x).mp
  exact ⟨(S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr ⟨4, hx⟩, hk⟩

/-- 元の各点を保ったまま標準 Tate p U と同じ直線を往復する。 -/
example (x : Tate p (union)) : (eqv).symm (eqv x) = x := (eqv).symm_apply_apply x

/-- 同定後も全点群への実際の第3成分が変わらない。 -/
example (x : Tate p (union)) :
    evaluation 3 (eqv x).val = (evaluation 3 x).val := rfl

/-- 任意の全 Tate 点列の p 倍と、元の非零生成元点列を区別する。 -/
example (w : Tate p (Points S.rationalCurve)) :
    (p : ℤ_[p]) • w ≠ (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val :=
  S.residualCyclicTateVector_not_p_multiple L hline hcofixed hζ hp5 hclass hbad w

end
end FreyCyclicTateUnionSourceTest

#print axioms DkMath.Lib.Algebra.CyclicPrimePowerTorsion.mem_iff_killed
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.mem_iff_killed_in_later
#print axioms DkMath.FLT.Frey.Source.residualCyclicTowerUnion_torsion
#print axioms DkMath.FLT.Frey.Source.residualUnionTate_inclusion
#print axioms DkMath.FLT.Frey.Source.residualUnionTate_inclusion_injective
#print axioms DkMath.FLT.Frey.Source.residualUnionTateToLine
#print axioms DkMath.FLT.Frey.Source.residualUnionTateLineEquiv
#print axioms DkMath.FLT.Frey.Source.residualUnionTateEquiv
#print axioms DkMath.FLT.Frey.Source.residualUnionTateLineEquiv_inclusion
#print axioms DkMath.FLT.Frey.Source.residualTowerUnionAction
#print axioms DkMath.FLT.Frey.Source.residualUnionTate_inclusion_equivariant
#print axioms DkMath.FLT.Frey.Source.residualUnionTate_action_scalar
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateVector_not_p_multiple
