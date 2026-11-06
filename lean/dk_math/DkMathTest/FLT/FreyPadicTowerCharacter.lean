/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPadicTowerCharacter

#print "file: DkMathTest.FLT.FreyPadicTowerCharacter"

namespace FreyPadicTowerCharacterTest

open DkMath.Lib.Algebra
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- 具体的な5進単元群からの、全ての標準有限剰余。 -/
def reductions (n : ℕ) : ℤ_[5]ˣ →* (ZMod (5 ^ (n + 1)))ˣ :=
  Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom

theorem reductions_compatible (n : ℕ) (u : ℤ_[5]ˣ) :
    Units.map (ZMod.castHom (pow_dvd_pow 5 (Nat.le_succ (n + 1)))
      (ZMod (5 ^ (n + 1)))).toMonoidHom (reductions (n + 1) u) = reductions n u := by
  apply Units.ext
  exact congrArg (fun f : ℤ_[5] →+* ZMod (5 ^ (n + 1)) => f u.val)
    (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _))

/-- 全ての有限成分から、元の5進単元を正確に復元する。 -/
example : PadicCharacterLimit.character reductions reductions_compatible = MonoidHom.id ℤ_[5]ˣ := by
  apply PadicCharacterLimit.character_unique
  intro n u
  rfl

example (u : ℤ_[5]ˣ) :
    PadicInt.toZModPow 4 (PadicCharacterLimit.character reductions reductions_compatible u).val =
      PadicInt.toZModPow 4 u.val :=
  congrArg Units.val (PadicCharacterLimit.character_mod reductions reductions_compatible 3 u)

/-- mod 5 で1でも mod 25 で1とは限らない。逆元21も実際に検証する。 -/
def six : (ZMod 25)ˣ := ⟨6, 21, by decide, by decide⟩

example : Units.map (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toMonoidHom six = 1 := by
  apply Units.ext
  decide

example : six ≠ 1 := by decide

end
end FreyPadicTowerCharacterTest

namespace FreyPadicTowerCharacterSourceTest
open DkMath.FLT.Frey DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)

/-- 元の点数 N を段番号に使う判定は、hclass/hbad/hchar を必要としない。 -/
example (hn : S.goodReductionPointCount ell ≤ n) : T.character σ ≠ 1 :=
  T.character_ne_one_of_good_count hell hellp hgood A hA σ hσ hn

/-- 同じ有限段で実際に動く点の存在も固定性判定から得られる。 -/
example (hn : S.goodReductionPointCount ell ≤ n) :
    ∃ x ∈ T.carrier, pointAction S.rationalCurve σ x ≠ x := by
  classical
  have h := T.character_ne_one_of_good_count hell hellp hgood A hA σ hσ hn
  have hnot : ¬ ∀ x ∈ T.carrier, pointAction S.rationalCurve σ x = x :=
    fun hf => h ((T.character_eq_one_iff σ).mpr hf)
  push Not at hnot
  exact hnot

end
end FreyPadicTowerCharacterSourceTest

#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.value_mod
#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.character
#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.character_unique
#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.character_eq_one_iff
#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.character_continuous
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_bound
#print axioms DkMath.FLT.Frey.Source.ResidualCyclicStage.character_ne_one_of_good_count
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter_mod_prime
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter_eq_one_iff
#print axioms DkMath.FLT.Frey.Source.residualPadicTowerCharacter_frobenius_ne_one
