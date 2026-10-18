import DkMath

open DkMath.Lib.NumberTheory DkMath.Lib.Cosmic DkMath.FLT.Kummer
open scoped NumberField
local instance prime37 : Fact (Nat.Prime 37) := ⟨by decide⟩

example {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - u ^ 37 = x * DkMath.CosmicFormula.GN 37 x u :=
  thirtySeven_difference_left x u
example {R : Type*} [CommRing R] (x u : R) :
    (x + u) ^ 37 - x ^ 37 = u * DkMath.CosmicFormula.GN 37 u x :=
  thirtySeven_difference_right x u
example {R : Type*} [Monoid R] (x : R) :
    x ^ 37 = (((x ^ 2) ^ 2) ^ 3) ^ 3 * x := pow_thirtySeven_small x
example : BernoulliPrime37.BernoulliIrregularPair 37 32 :=
  (BernoulliPrime37.irregular_pair_thirtySeven_iff 32).mpr rfl
example {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1)) :
    (∏ i, (IrregularPrime37.observe E).phases.obstruction i) = 1 :=
  IrregularPrime37.product_obstruction_one E

-- Existing standard endpoints remain available.
example : FermatLastTheoremFor 11 := fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := fermatLastTheoremFor_thirteen

#print axioms IdealPowerObstruction.trivial_iff_unit_power
#print axioms IrregularDescent.ofState
#print axioms IrregularDescent.ObstructedState.exists_weighted
#print axioms IrregularDescent.WeightedObstructedState.normalize
#print axioms BernoulliPrime37.irregular_pair_thirtySeven_iff
