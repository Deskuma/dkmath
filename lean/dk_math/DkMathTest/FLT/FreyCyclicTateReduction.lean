/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateReduction

#print "file: DkMathTest.FLT.FreyCyclicTateReduction"

namespace FreyCyclicTateReductionTest
open DkMath.Lib.Algebra.PrimePowerTateSequence

/-- 有限群 ZMod 25 では Tate 点列は零で、第0評価の全射性は自動ではない。 -/
theorem finite_tate_zero (x : Tate 5 (ZMod 25)) : x = 0 := by
  apply DkMath.Lib.Algebra.PrimePowerTateSequence.ext; intro n
  have h : (25 : ℕ) • evaluation (n + 2) x = evaluation n x := by
    change (5 * 5 : ℕ) • evaluation (n + 1 + 1) x = evaluation n x
    rw [mul_nsmul', compatible, compatible]
  change evaluation n x = 0
  simpa only [nsmul_eq_mul, ZMod.natCast_self, zero_mul] using h.symm

example : ¬ Function.Surjective (reduction (p := 5) (G := ZMod 25)) := by
  intro hs
  let a : (nsmulAddMonoidHom 5 : ZMod 25 →+ ZMod 25).ker := ⟨5, by decide⟩
  obtain ⟨x, hx⟩ := hs a
  rw [finite_tate_zero x, map_zero] at hx
  have he := congrArg Subtype.val hx
  change (0 : ZMod 25) = 5 at he
  exact (by decide : (0 : ZMod 25) ≠ 5) he

/-- 第0成分が零の任意の点列には、具体的な一段シフトによる p 倍逆像がある。 -/
example {G : Type*} [AddCommGroup G] (x : Tate 5 G) (hx : reduction x = 0) :
    5 • shiftOfZero x hx = x := nsmul_shiftOfZero x hx

end FreyCyclicTateReductionTest

namespace FreyCyclicTateReductionSourceTest
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
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad
local notation "red" => S.residualTateLineReduction L hline hcofixed hζ hp5 hclass hbad
local notation "eqv" => S.residualTateLineModPLinearEquiv L hline hcofixed hζ hp5 hclass hbad

/-- 全 Tate 加群の任意の同じ残余点を実際に持ち上げる。class/resonance 入力は不要。 -/
example (q : S.ResidualSpace) : ∃ x : Tate p (Points S.rationalCurve), tateReduction S.rationalCurve p x = q :=
  tateReduction_surjective S.rationalCurve p q

/-- 同じ直線 mod p の任意の点は同型の逆写像で正確に回収される。 -/
example (q : L) : eqv ((eqv).symm q) = q := (eqv).apply_symm_apply q

/-- p² 倍が直線に入るなら、飽和性を二度使って同じ点列も直線へ戻る。 -/
example (x : Tate p (Points S.rationalCurve)) (hx : p ^ 2 • x ∈ line) : x ∈ line := by
  apply (S.residualCyclicTateLine_p_saturated L hline hcofixed hζ hp5 hclass hbad x).mp
  apply (S.residualCyclicTateLine_p_saturated L hline hcofixed hζ hp5 hclass hbad (p • x)).mp
  simpa only [pow_two, mul_nsmul'] using hx

/-- 全加群の還元と直線の還元は同じ幾何学的 p 捩れ点を返す。 -/
example (x : line) : (red x).val.val = evaluation 0 x.val := rfl

end
end FreyCyclicTateReductionSourceTest

#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_shiftOfZero
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.nsmul_injective
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.range_nsmul_eq_reduction_ker
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.reduction_surjective
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.quotientEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateReduction_surjective
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModPLinearEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.tateModP_finrank
#print axioms DkMath.FLT.Frey.Source.residualTateModP_finrank
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLine_p_saturated
#print axioms DkMath.FLT.Frey.Source.residualTateLineReduction_surjective
#print axioms DkMath.FLT.Frey.Source.residualTateLineReduction_ker
#print axioms DkMath.FLT.Frey.Source.residualTateLineModPLinearEquiv
#print axioms DkMath.FLT.Frey.Source.residualTateLineModP_finrank
#print axioms DkMath.FLT.Frey.Source.residualTateLineReduction_inclusion
