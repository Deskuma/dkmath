/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Address
import DkMath.Petal.BezoutBridge
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
import Mathlib.NumberTheory.PrimeCounting

#print "file: DkMath.Petal.ErdosBridge"

/-!
# Petal Erdos Bridge

This file is the public bridge from Petal/GN carriers to the finite Erdos
#1196 log-capacity machinery.

It does **not** prove the analytic Erdos #1196 tail estimate.  Instead, it
shows that GN-observed Petal carriers can be read as prime-valued channels for
the existing `PrimitiveSet` log-capacity route.

The current implemented route is:

```text
PetalPrimeChannel family
  -> prime-valued Erdos channel family
  -> multiplicity-budgeted log sub-probability

PetalPrimeChannel family on one GN surface
  + PetalCarrierLabelNoncollisionOn prime labels
  -> GN multiplicity budget
  -> log sub-probability against that GN surface

PetalNoLiftPrimeChannel
  -> padicValNat q (GN d x u) = 1
```

Two conditions remain separate by design:

* `PetalCarrierLabelNoncollisionOn I qOf` is the family noncollision condition
  that prevents selected channels from reusing the same exponent slot.
* `PetalNoLiftPrimeChannel` is a local one-slot condition for one selected
  prime label.  A family of no-lift channels does not by itself imply that the
  labels are distinct.

The current crossroad is:

```text
NoLift family
  + carrier-label noncollision
  -> distinct selected channels, each with one local GN slot
  -> finite log-capacity control
```

Current research target:

```text
Petal address / carrier noncollision
  + address-to-label compatibility
  -> PetalCarrierLabelNoncollisionOn I qOf
```

The file also keeps explicit guardrails: Zsigmondy alone is not claimed to imply
no-lift, squarefreeness of GN, or the full multiplicity budget.
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

/--
Family data for a Petal carrier label map on one GN surface.

This is the predicate form of the planned `carrierAnchorOf` route.  It avoids
choosing a canonical carrier function too early: callers may supply any
finite-family assignment `mOf/qOf` as long as values are valid and injective,
labels recover values, and every label is an actual Petal prime channel.
-/
structure PetalCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → ℕ) : Prop where
  validValue :
    ∀ i, i ∈ I → 1 ≤ mOf i
  valueInjective :
    Set.InjOn mOf ↑I
  labelRecovery :
    ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
  carrier :
    ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)

/--
No-lift version of `PetalCarrierLabelMapData`.

This strengthens the local channel condition from `PetalPrimeChannel` to
`PetalNoLiftPrimeChannel`, while keeping the same value/address and label
recovery contract.
-/
structure PetalNoLiftCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → ℕ) : Prop where
  validValue :
    ∀ i, i ∈ I → 1 ≤ mOf i
  valueInjective :
    Set.InjOn mOf ↑I
  labelRecovery :
    ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
  carrier :
    ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)

/--
The standard Mathlib prime enumeration, exposed under Petal naming.

This is an experimental label map for the outer-address route.  It supplies
prime labels and injectivity, but it does not say that the chosen prime divides
any particular GN surface.
-/
noncomputable def petalNthPrimeLabel (m : Nat) : Nat :=
  Nat.nth Nat.Prime m

/--
Carrier-label noncollision for a finite Petal channel family.

This is intentionally just the Petal-facing name for
`NatPairwiseDistinctOn I qOf`: different selected carriers must not reuse the
same prime label.  It is **not** yet derived from Petal addresses.  The next
geometry layer should prove this predicate from an address/carrier
noncollision theorem and then feed the public bridge below.
-/
def PetalCarrierLabelNoncollisionOn
    {ι : Type _}
    (I : Finset ι)
    (qOf : ι → ℕ) : Prop :=
  DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf

/--
Address-level noncollision for a finite Petal carrier family.

This says only that distinct selected indices have distinct Petal addresses.
It does not by itself say anything about the selected prime labels.
-/
def PetalAddressNoncollisionOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → addrOf i ≠ addrOf j

/--
Compatibility between Petal addresses and selected prime labels.

This is the explicit bridge assumption saying that distinct observed addresses
produce distinct selected labels.  Keeping this separate prevents the public
API from pretending that address geometry alone already knows how labels are
chosen.
-/
def PetalCarrierLabelCompatibleOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I → addrOf i ≠ addrOf j → qOf i ≠ qOf j

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

/-- The Petal nth-prime label is prime. -/
theorem petalNthPrimeLabel_prime
    (m : Nat) :
    Nat.Prime (petalNthPrimeLabel m) := by
  unfold petalNthPrimeLabel
  exact Nat.prime_nth_prime m

/-- The Petal nth-prime label map is injective. -/
theorem petalNthPrimeLabel_injective :
    Function.Injective petalNthPrimeLabel := by
  unfold petalNthPrimeLabel
  exact Nat.nth_injective Nat.infinite_setOf_prime

/-- Equal Petal nth-prime labels recover equal source values. -/
theorem petalNthPrimeLabel_eq_imp_eq
    {m n : Nat}
    (h : petalNthPrimeLabel m = petalNthPrimeLabel n) :
    m = n :=
  petalNthPrimeLabel_injective h

/--
Unfold carrier-label noncollision to the underlying `PrimitiveSet`
duplicate-free condition.
-/
theorem petalCarrierLabelNoncollisionOn_pairwiseDistinct
    {ι : Type _}
    (I : Finset ι)
    (qOf : ι → ℕ)
    (h : PetalCarrierLabelNoncollisionOn I qOf) :
    DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf :=
  h

/--
Carrier-label noncollision gives injectivity of selected labels on the finite
index.

This is the form needed by the older injective-family multiplicity-budget
theorem.
-/
theorem petalCarrierLabelNoncollisionOn_injOn
    {ι : Type _}
    (I : Finset ι)
    (qOf : ι → ℕ)
    (h : PetalCarrierLabelNoncollisionOn I qOf) :
    Set.InjOn qOf ↑I :=
  DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn I qOf h

/--
Address noncollision plus address-to-label compatibility gives carrier-label
noncollision.

This is the first formal address-facing checkpoint.  The hard geometric work is
still outside this theorem: callers must provide both the address noncollision
fact and the compatibility explaining how addresses determine labels.
-/
theorem petalAddressNoncollision_labelNoncollision
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf := by
  intro i hi j hj hij
  exact hcompat i hi j hj (haddr i hi j hj hij)

/--
Address noncollision plus compatibility gives injectivity of selected labels.

This is the `Set.InjOn` form for older bridge theorems.
-/
theorem petalAddressNoncollision_label_injOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf) :
    Set.InjOn qOf ↑I :=
  petalCarrierLabelNoncollisionOn_injOn I qOf
    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)

/--
Injective selected addresses supply Petal address noncollision.

This is a generic bridge for concrete address constructions: once a construction
is known to be injective on the selected finite index, it satisfies the Petal
noncollision predicate used by the log-capacity route.
-/
theorem petalAddressNoncollisionOn_of_injOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (hinj : Set.InjOn addrOf ↑I) :
    PetalAddressNoncollisionOn I addrOf := by
  intro i hi j hj hij haddr
  exact hij (hinj hi hj haddr)

/--
Contrapositive label compatibility criterion.

If equal selected labels force equal Petal addresses, then distinct Petal
addresses force distinct selected labels.
-/
theorem petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → addrOf i = addrOf j) :
    PetalCarrierLabelCompatibleOn I addrOf qOf := by
  intro i hi j hj haddr hij
  exact haddr (hlabel i hi j hj hij)

/--
Outer Petal addresses are noncolliding when their source one-based values are
injective on the selected finite index.

This is the first concrete address-construction supply theorem for the current
Erdos bridge.
-/
theorem petalAddressNoncollisionOn_outer_of_value_injOn
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf : ι → Nat)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hinj : Set.InjOn mOf ↑I) :
    PetalAddressNoncollisionOn I (fun i => outerPetalAddress n lap (mOf i)) := by
  apply petalAddressNoncollisionOn_of_injOn
  intro i hi j hj haddr
  exact hinj hi hj
    (outerPetalAddress_eq_value_eq (hm i hi) (hm j hj) haddr)

/--
Outer-address label compatibility from value determination by labels.

If equality of selected labels forces equality of the underlying one-based
values, then those labels are compatible with the corresponding outer Petal
addresses.
-/
theorem petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j) :
    PetalCarrierLabelCompatibleOn I
      (fun i => outerPetalAddress n lap (mOf i)) qOf := by
  apply petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
  intro i hi j hj hij
  rw [hlabel i hi j hj hij]

/--
Outer-address value conditions supply carrier-label noncollision.

This is the first fully outer-address-facing noncollision theorem: injective
values give address noncollision, and labels that determine values give
address-to-label compatibility.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_value_injOn
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j) :
    PetalCarrierLabelNoncollisionOn I qOf :=
  petalAddressNoncollision_labelNoncollision I
    (fun i => outerPetalAddress n lap (mOf i)) qOf
    (petalAddressNoncollisionOn_outer_of_value_injOn I n lap mOf hm hminj)
    (petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
      I n lap mOf qOf hlabel)

/--
Outer-address label compatibility from a value-indexed label map.

This is the concrete `qOf = f(mOf)` supply form.  The map `f` does not have to
be a global injection; it only has to recover the selected one-based values on
the finite family under consideration.
-/
theorem petalCarrierLabelCompatibleOn_outer_of_value_map_injective
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (f : Nat → Nat)
    (hq :
      ∀ i, i ∈ I → qOf i = f (mOf i))
    (hf :
      ∀ i, i ∈ I → ∀ j, j ∈ I →
        f (mOf i) = f (mOf j) → mOf i = mOf j) :
    PetalCarrierLabelCompatibleOn I
      (fun i => outerPetalAddress n lap (mOf i)) qOf := by
  apply petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
  intro i hi j hj hij
  apply hf i hi j hj
  rw [← hq i hi, ← hq j hj]
  exact hij

/--
Outer-address value conditions supply carrier-label noncollision when labels
come from a value-indexed map.

This packages the common experimental situation:

```text
mOf i          selected one-based Petal value
qOf i = f(mOf i)  selected prime/carrier label
```

The theorem only asks for the local recovery property of `f` on the selected
family.  It does not claim that `f` constructs prime channels by itself.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (f : Nat → Nat)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = f (mOf i))
    (hf :
      ∀ i, i ∈ I → ∀ j, j ∈ I →
        f (mOf i) = f (mOf j) → mOf i = mOf j) :
    PetalCarrierLabelNoncollisionOn I qOf :=
  petalAddressNoncollision_labelNoncollision I
    (fun i => outerPetalAddress n lap (mOf i)) qOf
    (petalAddressNoncollisionOn_outer_of_value_injOn I n lap mOf hm hminj)
    (petalCarrierLabelCompatibleOn_outer_of_value_map_injective
      I n lap mOf qOf f hq hf)

/--
Toy outer-address route where the selected label is the selected value itself.

This is the `f = id` sanity check for the value-map API.  It proves only
noncollision of labels; it does **not** say that the selected values are prime
channels.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_value_self
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf : ι → Nat)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I) :
    PetalCarrierLabelNoncollisionOn I mOf :=
  petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
    I n lap mOf mOf id hm hminj
    (fun _ _ => rfl)
    (fun _ _ _ _ h => h)

/--
Carrier-label map data supplies outer-address label noncollision.

This is the packaged form of the current DkMath route: a family data object
stores valid values, value injectivity, label recovery, and carrier facts.
This theorem extracts only the noncollision part.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf :=
  petalCarrierLabelNoncollisionOn_outer_of_value_injOn
    I n lap mOf qOf hdata.validValue hdata.valueInjective
    hdata.labelRecovery

/--
No-lift carrier-label map data supplies outer-address label noncollision.

The no-lift data has the same recovery contract as the prime-channel data, so
the noncollision extraction is identical.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf :=
  petalCarrierLabelNoncollisionOn_outer_of_value_injOn
    I n lap mOf qOf hdata.validValue hdata.valueInjective
    hdata.labelRecovery

/--
No-lift carrier-label map data can be weakened to prime-channel data.

This keeps the structure layer composable: no-lift data is a stronger version
of the same carrier-label contract.
-/
theorem petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → Nat)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    PetalCarrierLabelMapData I d x u mOf qOf :=
  ⟨hdata.validValue, hdata.valueInjective, hdata.labelRecovery,
    fun i hi => (hdata.carrier i hi).1⟩

/--
Outer-address label compatibility for the nth-prime label map.

This is the first standard prime-enumeration experiment:
`qOf i = petalNthPrimeLabel (mOf i)`.  It supplies label recovery from the
injectivity of Mathlib's prime enumeration.
-/
theorem petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
    PetalCarrierLabelCompatibleOn I
      (fun i => outerPetalAddress n lap (mOf i)) qOf :=
  petalCarrierLabelCompatibleOn_outer_of_value_map_injective
    I n lap mOf qOf petalNthPrimeLabel hq
    (fun _ _ _ _ h => petalNthPrimeLabel_eq_imp_eq h)

/--
Outer-address noncollision for nth-prime labels.

The nth-prime map gives prime labels and label recovery.  This theorem only
uses the recovery part; channel divisibility is still handled by separate
PetalPrimeChannel hypotheses in the log-capacity route.
-/
theorem petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
    PetalCarrierLabelNoncollisionOn I qOf :=
  petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
    I n lap mOf qOf petalNthPrimeLabel hm hminj hq
    (fun _ _ _ _ h => petalNthPrimeLabel_eq_imp_eq h)

/--
The nth-prime label map gives a prime-valued family.

This records the part of the experiment that really is supplied by
`petalNthPrimeLabel`: primality of the selected labels.
-/
theorem petalNthPrimeLabel_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (mOf qOf : ι → Nat)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I qOf := by
  intro i hi
  rw [hq i hi]
  exact petalNthPrimeLabel_prime (mOf i)

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
PrimitiveBeam witnesses have nonnegative Erdos log cost after entering the
Petal prime channel.
-/
theorem primitivePrimeFactor_log_nonneg
    {q a b d : ℕ}
    (hq : DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q a b d)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    0 ≤ Real.log (q : ℝ) :=
  petalPrimeChannel_log_nonneg
    (primitivePrimeFactor_petalPrimeChannel hq hd hd1 hab_lt)

/--
Zsigmondy primitive divisors have nonnegative Erdos log cost after entering the
Petal prime channel.
-/
theorem zsigmondyPrimitivePrimeDivisor_log_nonneg
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
    0 ≤ Real.log (q : ℝ) :=
  petalPrimeChannel_log_nonneg
    (zsigmondyPrimitivePrimeDivisor_petalPrimeChannel hprim hd hd1 hab_lt)

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
A finite family of Zsigmondy primitive divisors is prime-valued in the Erdos
`PrimitiveSet` sense.

This is the family-level handoff from Zsigmondy witnesses to the Erdos channel
language.
-/
theorem zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (q a b d : ι → ℕ)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
    (hd : ∀ i, i ∈ I → 0 < d i)
    (hd1 : ∀ i, i ∈ I → 1 < d i)
    (hab_lt : ∀ i, i ∈ I → b i < a i) :
    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I q := by
  apply petalPrimeChannel_natPrimeValuedOn I d (fun i => a i - b i) b q
  intro i hi
  exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
    (hprim i hi) (hd i hi) (hd1 i hi) (hab_lt i hi)

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

/--
Distinct Petal prime channels on the same GN surface supply an Erdos
multiplicity budget against that GN surface.

This is the multi-channel counterpart of the singleton budget theorem.  The
new ingredient is injectivity of the selected prime labels on `I`; it prevents
two selected channels from consuming the same prime exponent slot.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hinj : Set.InjOn qOf ↑I)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  DkMath.NumberTheory.PrimitiveSet.natBaseMultiplicityBudgetOn_of_injOn_of_dvd
    I qOf (GN d x u) hGN0 hinj
    (fun i hi => anchoredGNCarrier_dvd_GN (hcarrier i hi))

/--
Distinct Petal prime channels on the same GN surface give an Erdos
sub-probability provider once that GN surface is above `1`.

This is still an injective-family theorem, not a Petal-address theorem.  A
future address/noncollision layer should supply the `Set.InjOn` hypothesis.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_injOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (hinj : Set.InjOn qOf ↑I)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalCarrierFamily_logSubProbability_of_multiplicityBudget
    I (fun _ => d) (fun _ => x) (fun _ => u) qOf (GN d x u) hGN
    hcarrier
    (petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
      I d x u qOf (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hGN))
      hinj hcarrier)

/--
Pairwise distinct Petal prime-channel labels on the same GN surface supply an
Erdos multiplicity budget against that GN surface.

This is the duplicate-free vocabulary version of
`petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn`.  It is the form that
an address/noncollision layer should be able to target first.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_pairwiseDistinct
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hdistinct :
      DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_injOn
    I d x u qOf hGN0
    (DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn
      I qOf hdistinct)
    hcarrier

/--
Pairwise distinct Petal prime-channel labels on the same GN surface give an
Erdos sub-probability provider.

This is the current address-facing theorem: once Petal geometry can prove
pairwise distinct prime labels, the log-capacity bridge is available.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (hdistinct :
      DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_injOn
    I d x u qOf hGN
    (DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn
      I qOf hdistinct)
    hcarrier

/--
Carrier-label noncollision on one GN surface supplies an Erdos multiplicity
budget against that GN surface.

This theorem is the Petal-named entry point for the current research target:
future address/carrier geometry should prove
`PetalCarrierLabelNoncollisionOn I qOf`, then this bridge handles the
valuation-budget side.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_pairwiseDistinct
    I d x u qOf hGN0
    (petalCarrierLabelNoncollisionOn_pairwiseDistinct I qOf hnoncollision)
    hcarrier

/--
Carrier-label noncollision on one GN surface gives the Erdos log
sub-probability provider.

This is the recommended public theorem for callers that already know their
Petal carriers do not collide as prime labels.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_pairwiseDistinct I qOf hnoncollision)
    hcarrier

/--
Address-facing GN multiplicity-budget bridge.

If Petal addresses do not collide and the selected labels are compatible with
those addresses, the existing carrier-label bridge supplies the GN multiplicity
budget.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_addressNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u qOf hGN0
    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
    hcarrier

/--
Address-facing finite Erdos bridge for Petal prime channels on one GN surface.

This is the public route:

```text
address noncollision
  + address-to-label compatibility
  + PetalPrimeChannel family
  -> finite GN log-capacity sub-probability
```
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
    hcarrier

/--
Outer-address value conditions supply an Erdos multiplicity budget on one GN
surface.

This is the multiplicity-budget form of the outer-address route.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_injOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN0 : GN d x u ≠ 0)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u qOf hGN0
    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
      I n lap mOf qOf hm hminj hlabel)
    hcarrier

/--
Outer-address value conditions feed Petal prime channels into the finite GN
log-capacity route.

The hypotheses say that the selected one-based values are noncolliding and that
the selected prime labels determine those values.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
      I n lap mOf qOf hm hminj hlabel)
    hcarrier

/--
Carrier-label map data supplies an Erdos multiplicity budget on one GN surface.

This is the packaged `carrierAnchorOf`-preparation theorem: once a family data
object supplies valid values, label recovery, and prime-channel carriers, the
GN multiplicity budget follows.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u qOf hGN0
    (petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
      I d x u n lap mOf qOf hdata)
    hdata.carrier

/--
Carrier-label map data feeds the finite GN log-capacity route.

This is the structure-packaged version of
`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hdata.carrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
      I d x u n lap mOf qOf hdata)
    hdata.carrier

/--
Value-map form of the outer-address GN multiplicity-budget route.

This is the practical wrapper for experiments where the selected label is
presented as `qOf i = f (mOf i)`.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (f : Nat → Nat)
    (hGN0 : GN d x u ≠ 0)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = f (mOf i))
    (hf :
      ∀ i, i ∈ I → ∀ j, j ∈ I →
        f (mOf i) = f (mOf j) → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u qOf hGN0
    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
      I n lap mOf qOf f hm hminj hq hf)
    hcarrier

/--
Value-map form of the outer-address GN log-capacity route.

The finite-family label noncollision is supplied from:

* valid one-based values,
* injectivity of `mOf` on the selected index set,
* `qOf i = f (mOf i)`,
* local recovery of `mOf` from equal `f (mOf)` labels.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (f : Nat → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = f (mOf i))
    (hf :
      ∀ i, i ∈ I → ∀ j, j ∈ I →
        f (mOf i) = f (mOf j) → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
      I n lap mOf qOf f hm hminj hq hf)
    hcarrier

/--
Toy `qOf = mOf` form of the outer-address GN multiplicity-budget route.

This is an API sanity check: if the selected values themselves are assumed to
be Petal prime-channel labels, then value injectivity supplies the required
label noncollision.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf : ι → Nat)
    (hGN0 : GN d x u ≠ 0)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (mOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I mOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u mOf hGN0
    (petalCarrierLabelNoncollisionOn_outer_of_value_self
      I n lap mOf hm hminj)
    hcarrier

/--
Toy `qOf = mOf` form of the outer-address GN log-capacity route.

This theorem intentionally keeps the strong hypothesis
`PetalPrimeChannel d x u (mOf i)` explicit.  It is a control theorem for the
noncollision machinery, not a prime-construction theorem.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (mOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I mOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) mOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u mOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_self
      I n lap mOf hm hminj)
    hcarrier

/--
Nth-prime label form of the outer-address GN multiplicity-budget route.

The label map supplies prime labels and noncollision.  The theorem still
requires explicit `PetalPrimeChannel` hypotheses, because being the nth prime
does not imply divisibility of the observed GN surface.
-/
theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN0 : GN d x u ≠ 0)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      I qOf (GN d x u) :=
  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
    I d x u qOf hGN0
    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
      I n lap mOf qOf hm hminj hq)
    hcarrier

/--
Nth-prime label form of the outer-address GN log-capacity route.

This is the standard prime-enumeration experiment for the value-map API.
It proves that the route works with a genuine prime-valued injective label map,
while keeping the actual GN-carrier condition explicit.
-/
theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
      I n lap mOf qOf hm hminj hq)
    hcarrier

/--
Local no-lift makes the observed GN surface nonzero.

If `GN d x u` were zero, then every number, in particular `q ^ 2`, would divide
it.  This contradicts the no-lift condition.
-/
theorem petalNoLiftPrimeChannel_GN_ne_zero
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    GN d x u ≠ 0 := by
  intro hzero
  exact h.2 (by rw [hzero]; exact dvd_zero _)

/--
A Petal prime channel on a nonzero GN surface forces that surface to be larger
than `1`.

The reason is purely arithmetic: the prime label `q` divides the nonzero GN
surface, so `q ≤ GN d x u`, while primality gives `1 < q`.
-/
theorem petalPrimeChannel_GN_one_lt_of_ne_zero
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q)
    (hGN0 : GN d x u ≠ 0) :
    1 < GN d x u := by
  have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h
  have hq_le : q ≤ GN d x u :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hGN0) hq_dvd
  exact lt_of_lt_of_le (petalPrimeChannel_prime h).one_lt hq_le

/-- A no-lift Petal prime channel automatically lies on a GN surface above `1`. -/
theorem petalNoLiftPrimeChannel_GN_one_lt
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    1 < GN d x u :=
  petalPrimeChannel_GN_one_lt_of_ne_zero h.1
    (petalNoLiftPrimeChannel_GN_ne_zero h)

/--
No-lift means that the selected prime has exactly one `p`-adic slot on the GN
surface.

This is the local valuation reading of `PetalNoLiftPrimeChannel`: the channel
prime divides `GN d x u`, but its square does not.
-/
theorem petalNoLiftPrimeChannel_padicValNat_GN_eq_one
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    padicValNat q (GN d x u) = 1 := by
  letI : Fact q.Prime := ⟨petalNoLiftPrimeChannel_prime h⟩
  have hGN0 : GN d x u ≠ 0 := petalNoLiftPrimeChannel_GN_ne_zero h
  have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h.1
  have hle_one : 1 ≤ padicValNat q (GN d x u) :=
    one_le_padicValNat_of_dvd hGN0 hq_dvd
  have hnot_two : ¬ 2 ≤ padicValNat q (GN d x u) := by
    intro htwo
    exact h.2 ((padicValNat_dvd_iff_le hGN0).mpr htwo)
  omega

/--
A no-lift Petal channel family has exact one-slot valuation at every selected
label.

This theorem does not assert distinctness of the labels.  If two indices choose
the same prime label, they read the same one-slot valuation.
-/
theorem petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    ∀ i, i ∈ I → padicValNat (qOf i) (GN d x u) = 1 := by
  intro i hi
  exact petalNoLiftPrimeChannel_padicValNat_GN_eq_one (hcarrier i hi)

/--
No-lift Petal channel families with noncolliding labels feed the finite Erdos
log-capacity bridge on the observed GN surface.

This is the crossroads theorem for the current public API:

* no-lift gives exact one-slot local valuation at each selected label;
* carrier-label noncollision prevents two selected indices from reusing the
  same prime label;
* the existing GN budget bridge then gives log sub-probability.

The theorem still does not claim that Petal address geometry supplies
noncollision, nor that Zsigmondy alone supplies no-lift.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN hnoncollision
    (fun i hi => (hcarrier i hi).1)

/--
Address-facing finite Erdos bridge for no-lift Petal channels.

This composes the current address checkpoint with the crossroads theorem:

```text
address noncollision
  + address-to-label compatibility
  + NoLift Petal channel family
  -> finite GN log-capacity sub-probability
```

It still keeps the two hard inputs explicit: address noncollision and
compatibility between addresses and selected labels.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
    hcarrier

/--
Outer-address value conditions feed no-lift Petal channels into the finite GN
log-capacity route.

This is the no-lift version of
`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
      I n lap mOf qOf hm hminj hlabel)
    hcarrier

/--
No-lift carrier-label map data feeds the finite GN log-capacity route.

This is the packaged form for the future `carrierAnchorOf` route when the
selected carriers also have local one-slot/no-lift information.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hdata.carrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
      I d x u n lap mOf qOf hdata)
    hdata.carrier

/--
Value-map form of the outer-address no-lift GN log-capacity route.

This is the no-lift counterpart of
`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective`.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (f : Nat → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = f (mOf i))
    (hf :
      ∀ i, i ∈ I → ∀ j, j ∈ I →
        f (mOf i) = f (mOf j) → mOf i = mOf j)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
      I n lap mOf qOf f hm hminj hq hf)
    hcarrier

/--
Toy `qOf = mOf` form of the outer-address no-lift GN log-capacity route.

The theorem checks that the no-lift bridge composes with the identity value-map
route.  It still assumes that each selected value is already a no-lift Petal
prime-channel label.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (mOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I mOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) mOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u mOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_value_self
      I n lap mOf hm hminj)
    hcarrier

/--
Nth-prime label form of the outer-address no-lift GN log-capacity route.

The nth-prime map supplies a standard injective prime-valued label family.
No-lift and GN divisibility remain explicit hypotheses through
`PetalNoLiftPrimeChannel`.
-/
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hGN : 1 < GN d x u)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hq :
      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
        (fun i hi => (hcarrier i hi).1))
      hGN).SubProbability :=
  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    I d x u qOf hGN
    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
      I n lap mOf qOf hm hminj hq)
    hcarrier

/--
A single Petal prime channel fits into the Erdos multiplicity budget of its own
nonzero GN surface.

This isolates the lower-slot part of the argument: `q ∣ GN d x u` supplies one
factorization slot at `q`.  No no-lift hypothesis is needed for this lower
bound; no-lift only supplies nonzeroness in the specialized theorem below.
-/
theorem petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q)
    (hGN0 : GN d x u ≠ 0) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u) := by
  classical
  intro p hp
  unfold DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityOn
  by_cases hpq : q = p
  · subst hpq
    simp only [Finset.filter_true, Finset.card_singleton]
    have hq_dvd : q ∣ GN d x u := anchoredGNCarrier_dvd_GN h
    have hq_pow_dvd : q ^ 1 ∣ GN d x u := by simpa using hq_dvd
    exact (hp.pow_dvd_iff_le_factorization hGN0).mp hq_pow_dvd
  · simp [hpq]

/--
A single no-lift Petal prime channel fits into the Erdos multiplicity budget of
its own GN surface.

This is the no-lift specialization of
`petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero`.
-/
theorem petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u) :=
  petalPrimeChannel_singleton_multiplicityBudget_GN_of_ne_zero h.1
    (petalNoLiftPrimeChannel_GN_ne_zero h)

/--
Singleton no-lift Petal channels give a direct Erdos log sub-probability
against the observed GN surface.

This is intentionally a one-channel theorem.  Multi-channel budgets still need
separate collision/multiplicity control.
-/
theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q)
    (hGN : 1 < GN d x u) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
        (fun _ : Unit => u) (fun _ : Unit => q)
        (by
          intro i _hi
          cases i
          exact h.1))
      hGN).SubProbability :=
  petalCarrierFamily_logSubProbability_of_multiplicityBudget
    ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
    (fun _ : Unit => u) (fun _ : Unit => q) (GN d x u) hGN
    (by
      intro i _hi
      cases i
      exact h.1)
    (petalNoLiftPrimeChannel_singleton_multiplicityBudget_GN h)

/--
No-lift Petal channels give a direct singleton Erdos log sub-probability
against their own GN surface.

Compared with `petalNoLiftPrimeChannel_singleton_logSubProbability_GN`, this
version removes the explicit `1 < GN d x u` hypothesis: it is forced by the
prime channel and local no-lift.
-/
theorem petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
    {d x u q : ℕ}
    (h : PetalNoLiftPrimeChannel d x u q) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d x u)
      (petalPrimeChannel_realLogNonnegOn
        ({()} : Finset Unit) (fun _ : Unit => d) (fun _ : Unit => x)
        (fun _ : Unit => u) (fun _ : Unit => q)
        (by
          intro i _hi
          cases i
          exact h.1))
      (petalNoLiftPrimeChannel_GN_one_lt h)).SubProbability :=
  petalNoLiftPrimeChannel_singleton_logSubProbability_GN h
    (petalNoLiftPrimeChannel_GN_one_lt h)

/--
Zsigmondy primitive divisors with an explicit no-lift condition give a singleton
Erdos log sub-probability on the corresponding GN surface.

This theorem deliberately keeps no-lift as an explicit hypothesis.  Zsigmondy
alone does not imply no-lift.
-/
theorem zsigmondyPrimitivePrimeDivisor_noLift_singleton_logSubProbability_GN
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hNoLift : ¬ q ^ 2 ∣ GN d (a - b) b) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
      ({()} : Finset Unit) (fun _ : Unit => q) (GN d (a - b) b)
      (petalPrimeChannel_realLogNonnegOn
        ({()} : Finset Unit) (fun _ : Unit => d)
        (fun _ : Unit => a - b) (fun _ : Unit => b) (fun _ : Unit => q)
        (by
          intro i _hi
          cases i
          exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
            hprim hd hd1 hab_lt))
      (petalNoLiftPrimeChannel_GN_one_lt
        ⟨zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
          hprim hd hd1 hab_lt, hNoLift⟩)).SubProbability :=
  petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
    ⟨zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
      hprim hd hd1 hab_lt, hNoLift⟩

/--
Zsigmondy-family form of the first Petal-to-Erdos capacity bridge.

Once a finite Zsigmondy witness family has a base-prime multiplicity budget
against `n`, its log-ratio provider is sub-probability.  The theorem still
keeps the multiplicity budget explicit; Zsigmondy supplies prime channels, not
global capacity by itself.
-/
theorem zsigmondyFamily_logSubProbability_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (q a b d : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor (a i) (b i) (d i) (q i))
    (hd : ∀ i, i ∈ I → 0 < d i)
    (hd1 : ∀ i, i ∈ I → 1 < d i)
    (hab_lt : ∀ i, i ∈ I → b i < a i)
    (hbudget : DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn I q n) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I q n
      (DkMath.NumberTheory.PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I q
        (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
          I q a b d hprim hd hd1 hab_lt))
      hn).SubProbability :=
  DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
    I q n hn
    (zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
      I q a b d hprim hd hd1 hab_lt)
    hbudget

end Petal
end DkMath
