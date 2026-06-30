/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.ErdosBridge

#print "file: DkMath.Petal.Obstruction"

/-!
# Petal Obstruction Lemmas

This file records small `False` lemmas for Petal carrier routes.

The purpose is not to add inconsistent assumptions as axioms.  Instead, each
theorem names a boundary condition:

```text
positive gate hypothesis
  + route-breaking witness
  -> False
```

These lemmas are useful during experimental development.  They make it clear
where a candidate route stops being compatible with address noncollision,
carrier-label recovery, finite-channel independence, or local no-lift
valuation control.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom

/--
Address noncollision breaks as soon as two distinct selected indices have the
same Petal address.

This is the address-level obstruction: if a route assigns the same address to
two different selected carriers, it cannot pass through
`PetalAddressNoncollisionOn`.
-/
theorem petalAddressNoncollision_contradiction_of_same_address_ne_index
    {ι : Type _}
    {I : Finset ι}
    {addrOf : ι → PetalAddress}
    {i j : ι}
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hsame : addrOf i = addrOf j)
    (hne : i ≠ j) :
    False :=
  haddr i hi j hj hne hsame

/--
Label recovery breaks when the same selected label points to two different
Petal values.

This is the smallest obstruction behind the finite-family recovery contract.
-/
theorem labelRecovery_contradiction_of_same_label_ne_value
    {ι : Type _}
    {I : Finset ι}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hrec :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j)
    (hneq : mOf i ≠ mOf j) :
    False :=
  hneq (hrec i hi j hj hlabel)

/--
Value injectivity breaks when two distinct selected indices carry the same
Petal value.

This names the value/address side of the finite-family obstruction.
-/
theorem valueInjective_contradiction_of_same_value_ne_index
    {ι : Type _}
    {I : Finset ι}
    {mOf : ι → ℕ}
    {i j : ι}
    (hinj : Set.InjOn mOf ↑I)
    (hi : i ∈ I) (hj : j ∈ I)
    (hvalue : mOf i = mOf j)
    (hne : i ≠ j) :
    False :=
  hne (hinj hi hj hvalue)

/--
Label recovery followed by value injectivity turns equal labels into equal
selected indices.

This is the positive form of the finite-family safety chain:

```text
same label -> same value -> same index
```
-/
theorem labelRecovery_valueInjective_eq_of_same_label
    {ι : Type _}
    {I : Finset ι}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hrec :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hinj : Set.InjOn mOf ↑I)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j) :
    i = j :=
  hinj hi hj (hrec i hi j hj hlabel)

/--
Carrier-label map data turns equal labels into equal selected indices.

This packages the safety chain stored in `PetalCarrierLabelMapData`.
-/
theorem petalCarrierLabelMapData_eq_of_same_label
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j) :
    i = j :=
  labelRecovery_valueInjective_eq_of_same_label
    hdata.labelRecovery hdata.valueInjective hi hj hlabel

/--
No-lift carrier-label map data also turns equal labels into equal selected
indices.

The no-lift data carries the same finite-family recovery and injectivity
contract as the prime-channel data.
-/
theorem petalNoLiftCarrierLabelMapData_eq_of_same_label
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j) :
    i = j :=
  labelRecovery_valueInjective_eq_of_same_label
    hdata.labelRecovery hdata.valueInjective hi hj hlabel

/--
Carrier-label map data makes the selected label map injective on the finite
index set.

This is the `Set.InjOn` API form of the safety chain
`same label -> same value -> same selected index`.
-/
theorem petalCarrierLabelMapData_label_injOn
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    Set.InjOn qOf ↑I := by
  intro i hi j hj hlabel
  exact petalCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel

/--
No-lift carrier-label map data makes the selected label map injective on the
finite index set.
-/
theorem petalNoLiftCarrierLabelMapData_label_injOn
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    Set.InjOn qOf ↑I := by
  intro i hi j hj hlabel
  exact petalNoLiftCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel

/--
Carrier-label map data supplies duplicate-free selected labels directly.

Unlike the outer-address route, this theorem uses only the data object's
recovery and injectivity fields.
-/
theorem petalCarrierLabelMapData_labelNoncollision
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf := by
  intro i hi j hj hij hlabel
  exact hij (petalCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)

/--
No-lift carrier-label map data supplies duplicate-free selected labels
directly.

The duplicate-free conclusion comes from the finite-family label contract, not
from the no-lift valuation condition.
-/
theorem petalNoLiftCarrierLabelMapData_labelNoncollision
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf := by
  intro i hi j hj hij hlabel
  exact hij (petalNoLiftCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)

/--
Carrier-label map data breaks if two distinct selected indices reuse the same
label.

This is the packaged obstruction form of
`same label -> same value -> same index`.
-/
theorem petalCarrierLabelMapData_contradiction_of_same_label_ne_index
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j)
    (hne : i ≠ j) :
    False :=
  hne (petalCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)

/--
No-lift carrier-label map data breaks if two distinct selected indices reuse
the same label.

NoLift does not cause this obstruction; the finite-family recovery contract
does.  Keeping the theorem named for no-lift data makes the packaged route easy
to diagnose.
-/
theorem petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
    {ι : Type _}
    {I : Finset ι}
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    {i j : ι}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j)
    (hne : i ≠ j) :
    False :=
  hne (petalNoLiftCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)

/--
Carrier-label noncollision breaks when two distinct selected indices reuse the
same prime label.

This is the finite-prime-channel independence obstruction.  If it fires, the
family cannot be used as a duplicate-free channel family for the log-capacity
or multiplicity-budget route.
-/
theorem petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
    {ι : Type _}
    {I : Finset ι}
    {qOf : ι → ℕ}
    {i j : ι}
    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
    (hi : i ∈ I) (hj : j ∈ I)
    (hlabel : qOf i = qOf j)
    (hne : i ≠ j) :
    False :=
  hne (petalCarrierLabelNoncollisionOn_injOn I qOf hnoncollision hi hj hlabel)

/--
Local no-lift breaks as soon as the selected square also divides the observed
GN surface.

This records the exact boundary of `PetalNoLiftPrimeChannel`: a channel may be
a carrier, but it is not no-lift if `q^2` divides the same GN value.
-/
theorem noLift_contradiction_of_square_dvd_GN
    {d x u q : ℕ}
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hlift : q ^ 2 ∣ GN d x u) :
    False :=
  hNoLift.2 hlift

/--
The p-adic one-slot reading breaks against a two-slot lower bound.

This is the valuation form of the no-lift obstruction.
-/
theorem padicValNat_eq_one_contradiction_of_two_le
    {q n : ℕ}
    (hval : padicValNat q n = 1)
    (hge : 2 ≤ padicValNat q n) :
    False := by
  omega

/--
Petal no-lift breaks against any valuation lower bound at least `2` on the
same GN surface.
-/
theorem petalNoLift_contradiction_of_padicValNat_two_le
    {d x u q : ℕ}
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hge : 2 ≤ padicValNat q (GN d x u)) :
    False :=
  padicValNat_eq_one_contradiction_of_two_le
    (petalNoLiftPrimeChannel_padicValNat_GN_eq_one hNoLift) hge

/--
Petal no-lift breaks against a `d`-level valuation lower bound when `1 < d`.

This is the thin FLT-facing obstruction gate: a later theorem may supply the
lower bound from a power or branch equation, while this theorem records only
the collision with no-lift.
-/
theorem petalNoLift_obstruction_of_padicValNat_ge
    {d x u q : ℕ}
    (hd1 : 1 < d)
    (hNoLift : PetalNoLiftPrimeChannel d x u q)
    (hge : d ≤ padicValNat q (GN d x u)) :
    False :=
  petalNoLift_contradiction_of_padicValNat_two_le hNoLift
    (le_trans (Nat.succ_le_of_lt hd1) hge)

end Petal
end DkMath
