/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.BezoutBridge
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget

#print "file: DkMath.Petal.ErdosBridge"

/-!
# Petal Erdos Bridge

This file starts the experimental bridge from Petal/GN carriers to the finite
Erdos #1196 log-capacity machinery.

The first step is intentionally small:

```text
Petal carrier
  -> prime-valued Erdos channel
  -> multiplicity-budgeted log sub-probability
```

No multiplicity budget is proved here.  The caller still supplies the existing
`PrimitiveSet.NatBaseMultiplicityBudgetOn` hypothesis.  This keeps the bridge
honest: Petal supplies carrier location, while the Erdos side supplies the
global capacity bound once a multiplicity budget is available.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom

/--
A Petal GN carrier read as a prime Erdos channel.

This is the prime-channel specialization of `AnchoredGNCarrier`: the carrier is
the anchor prime itself.
-/
def PetalPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q

/--
A Petal prime channel with local no-lift on the observed GN surface.

This records the local multiplicity condition for the selected channel only.
It is deliberately weaker than asking the whole `GN` value to be squarefree.
-/
def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u

/-- A Petal prime channel carries a prime label. -/
theorem petalPrimeChannel_prime
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q) :
    Nat.Prime q :=
  anchoredGNCarrier_anchor_prime h

/-- A Petal no-lift prime channel carries a prime label. -/
theorem petalNoLiftPrimeChannel_prime
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    Nat.Prime q :=
  petalPrimeChannel_prime h.1

/-- Extract the underlying Petal prime channel from a no-lift channel. -/
theorem petalNoLiftPrimeChannel_channel
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    PetalPrimeChannel d x u q :=
  h.1

/-- Extract the local no-lift condition from a Petal no-lift prime channel. -/
theorem petalNoLiftPrimeChannel_noLift
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    ¬ q ^ 2 ∣ GN d x u :=
  h.2

/--
PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
-/
theorem primitivePrimeFactor_petalPrimeChannel
    {q a b d : ℕ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    PetalPrimeChannel d (a - b) b q :=
  anchoredGNCarrier_of_primitivePrimeFactor hq hd hd1 hab_lt

/--
Zsigmondy primitive divisors enter the Erdos bridge as Petal prime channels.
-/
theorem zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    PetalPrimeChannel d (a - b) b q :=
  anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor hprim hd hd1 hab_lt

/--
The logarithmic cost of a Petal prime channel is nonnegative.
-/
theorem petalPrimeChannel_log_nonneg
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q) :
    0 ≤ Real.log (q : ℝ) :=
  DkMath.NumberTheory.PrimitiveSet.real_log_nat_nonneg_of_one_le
    (le_of_lt (petalPrimeChannel_prime h).one_lt)

/--
A finite family of Petal prime channels is prime-valued in the Erdos
`PrimitiveSet` sense.
-/
theorem petalPrimeChannel_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I qOf := by
  intro i hi
  exact petalPrimeChannel_prime (hcarrier i hi)

/--
A finite family of Petal prime channels supplies the real/log nonnegativity
input for the Erdos log-capacity route.
-/
theorem petalPrimeChannel_realLogNonnegOn
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.RealLogNonnegOn I qOf :=
  DkMath.NumberTheory.PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I qOf
    (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)

/--
First Petal-to-Erdos capacity bridge.

If a finite Petal carrier family has a base-prime multiplicity budget against
`n`, then the corresponding log-ratio provider is sub-probability.

The multiplicity budget is an explicit hypothesis.  This theorem does not claim
that Petal geometry or Zsigmondy alone supplies it.
-/
theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i))
    (hbudget : DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I qOf n) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf n
      (petalPrimeChannel_realLogNonnegOn I d x u qOf hcarrier)
      hn).SubProbability :=
  DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
    I qOf n hn
    (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
    hbudget

end Petal
end DkMath
