/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateLine

#print "file: DkMathTest.FLT.FreyCyclicTateLine"

namespace FreyCyclicTateLineTest
open DkMath.Lib.Algebra PrimePowerTateSequence
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 標準剰余を復元すると、単元に限らず任意の5進整数を回収する。 -/
theorem recover (a : ℤ_[5]) :
    liftResidues (fun n => PadicInt.toZModPow (n + 1) a)
      (fun n => congrArg (fun f : ℤ_[5] →+* ZMod (5 ^ (n + 1)) => f a)
        (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _))) = a := by
  apply PadicCharacterLimit.ext_positive
  intro n
  exact liftResidues_mod _ _ n

/-- 非単元5は第1剰余が0でも、実際の極限では非零。 -/
example : liftResidues (fun n => PadicInt.toZModPow (n + 1) (5 : ℤ_[5]))
    (fun n => congrArg (fun f : ℤ_[5] →+* ZMod (5 ^ (n + 1)) => f 5)
      (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _))) ≠ 0 := by
  rw [recover]
  norm_num

/-- scalar の評価と元の加法写像による移送が可換。 -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (a : ℤ_[5]) (x : Tate 5 G) (n : ℕ) :
    evaluation n (mapLinear f (a • x)) =
      (PadicInt.toZModPow (n + 1) a).val • f (evaluation n x) := by
  change f ((PadicInt.toZModPow (n + 1) a).val • evaluation n x) = _
  exact map_nsmul f _ _

end
end FreyCyclicTateLineTest

namespace FreyCyclicTateLineSourceTest
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
local notation "param" => S.residualCyclicTateParametrization L hline hcofixed hζ hp5 hclass hbad
local notation "equiv" => S.residualCyclicTateLineEquiv L hline hcofixed hζ hp5 hclass hbad

/-- 任意の同じ点列を復元する線形同型の実際の逆写像。 -/
example (x : line) : equiv ((equiv).symm x) = x := (equiv).apply_symm_apply x

/-- 第0成分が零でも、点列全体は零ではない。単位元成分だけで検出しない。 -/
example : evaluation 0 (param (p : ℤ_[p])).val = 0 ∧ param (p : ℤ_[p]) ≠ 0 := by
  constructor
  · change (PadicInt.toZModPow 1 (p : ℤ_[p])).val •
      (S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad 0).val = 0
    rw [map_natCast]
    have hk := (S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad 0).killed _
      (S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad 0).property
    have he := nsmul_eq_of_residue
      (S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad 0).val hk
      (ZMod.natCast_zmod_val (p : ZMod (p ^ (0 + 1))))
    exact he.trans (by simpa only [Nat.zero_add, pow_one] using hk)
  · intro h
    have he : (p : ℤ_[p]) = 0 :=
      S.residualCyclicTateParametrization_injective L hline hcofixed hζ hp5 hclass hbad
        (h.trans (map_zero param).symm)
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he

/-- 同じ包含の p 進線形性は、第0成分だけでなく全点列で成立。 -/
example (a : ℤ_[p]) (x : line) :
    S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad (a • x) =
      a • S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad x :=
  map_smul _ _ _

end
end FreyCyclicTateLineSourceTest

#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.padicModule
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.mapLinear
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.actionLinear
#print axioms DkMath.Lib.Algebra.PrimePowerTateSequence.liftResidues_mod
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLine
#print axioms DkMath.FLT.Frey.Source.residualTateGeneratorCoordinates
#print axioms DkMath.FLT.Frey.Source.residualTateCoefficient_compatible
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateParametrization_injective
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateParametrization_surjective
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLineEquiv
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion_injective
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLine_action_scalar
#print axioms DkMath.FLT.Frey.Source.residualCyclicTateLine_inclusion_scalar
