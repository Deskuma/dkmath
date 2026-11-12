/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateVector

#print "file: DkMathTest.FLT.FreyCyclicTateVector"

namespace FreyCyclicTateVectorTest
open DkMath.Lib.Algebra PrimePowerTateSequence

/-- 有限群 ZMod 25 の5進 Tate 点列は零。
単なる有限段の非零点を、互換な無限点列と取り違えない。 -/
example (x : Tate 5 (ZMod 25)) : x = 0 := by
  apply PrimePowerTateSequence.ext
  intro n
  have h : (25 : ℕ) • evaluation (n + 2) x = evaluation n x := by
    change (5 * 5 : ℕ) • evaluation (n + 1 + 1) x = evaluation n x
    rw [mul_nsmul', compatible, compatible]
  change evaluation n x = 0
  simpa only [nsmul_eq_mul, ZMod.natCast_self, zero_mul] using h.symm

/-- 成分ごとの写像は、元の単射を失わない。 -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (PrimePowerTateSequence.map (p := 5) f) := map_injective f hf

end FreyCyclicTateVectorTest

namespace FreyCyclicTateVectorSourceTest
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
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad

/-- 第2成分は同じ第0生成元の実際の p² 倍逆像で、位数は p³。 -/
example : p ^ 2 • (gen 2).val = (gen 0).val ∧ addOrderOf (gen 2).val = p ^ 3 :=
  ⟨S.residualTateGenerators_to_seed L hline hcofixed hζ hp5 hclass hbad 2,
    S.residualTateGenerators_order L hline hcofixed hζ hp5 hclass hbad 2⟩

/-- 実際の点列の第2成分は、再帰的に選んだ同じ生成元である。 -/
example : evaluation 2 (vec).val = (gen 2).val := rfl

/-- 同じ塔の単射で全点群の Tate 点列へ移しても非零。 -/
example : S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad vec ≠ 0 := by
  intro h
  apply S.residualCyclicTateVector_ne_zero L hline hcofixed hζ hp5 hclass hbad
  apply S.residualCyclicTate_inclusion_injective L hline hcofixed hζ hp5 hclass hbad
  exact h.trans (map_zero _).symm

end
end FreyCyclicTateVectorSourceTest

#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.map_injective
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.action
#print axioms DkMath.FLT.Frey.Source.residualTateGenerators
#print axioms DkMath.FLT.Frey.Source.residualTateGenerators_order
#print axioms DkMath.FLT.Frey.Source.residualTateGenerators_generate
#print axioms DkMath.FLT.Frey.Source.residualCyclicTate_inclusion_injective
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateAction
#print axioms DkMath.FLT.Frey.Source.residualCyclicTate_inclusion_equivariant
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateVector
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateVector_ne_zero
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateVector_fixed_iff
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateVector_frobenius_moved
