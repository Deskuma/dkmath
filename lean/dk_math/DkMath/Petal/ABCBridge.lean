/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Obstruction
import DkMath.ABC.MassBridge

#print "file: DkMath.Petal.ABCBridge"

/-!
# Petal ABC Bridge

This file is the first thin negotiation layer from Petal carrier-label data to
the ABC `supportMass` / `rad` bridge.

The key observation is deliberately modest:

```text
PetalCarrierLabelMapData
  -> selected prime labels divide the observed GN surface
  -> their finite support product is bounded by supportMass / rad
```

NoLift is not required for this bridge.  ABC support/rad only needs distinct
prime support; the no-lift valuation condition remains a separate local gate.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom

/--
The selected label support of a finite Petal carrier family.

This is the ABC-facing finite support: duplicate labels are collapsed by the
`Finset.image`, exactly as radical/support-mass arguments should do.
-/
def petalCarrierLabelSupport
    {ι : Type _}
    (I : Finset ι)
    (qOf : ι → ℕ) : Finset ℕ :=
  I.image qOf

/--
Carrier-label map data supplies prime divisors of the observed GN surface on
its label support.
-/
theorem petalCarrierLabelMapData_labelSupport_prime_dvd_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    ∀ q, q ∈ petalCarrierLabelSupport I qOf →
      Nat.Prime q ∧ q ∣ GN d x u := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
  exact ⟨petalPrimeChannel_prime (hdata.carrier i hi),
    anchoredGNCarrier_dvd_GN (hdata.carrier i hi)⟩

/--
No-lift carrier-label map data also supplies prime divisors of the observed GN
surface on its label support.

The no-lift component is not used here; support/rad only needs prime support.
-/
theorem petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    ∀ q, q ∈ petalCarrierLabelSupport I qOf →
      Nat.Prime q ∧ q ∣ GN d x u := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
  exact ⟨petalNoLiftPrimeChannel_prime (hdata.carrier i hi),
    anchoredGNCarrier_dvd_GN (hdata.carrier i hi).1⟩

/--
Petal carrier-label data gives an ABC support-mass lower bound for the observed
GN surface.

This is the first ABC-facing payoff of the finite carrier support.
-/
theorem petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).prod id ≤
      DkMath.ABC.supportMass (GN d x u) :=
  DkMath.ABC.supportMass_ge_prod_of_prime_channel_family
    (n := GN d x u) hGN0
    (petalCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata)

/--
No-lift carrier-label data gives the same ABC support-mass lower bound.

NoLift is intentionally not consumed by this theorem; it remains available for
valuation-obstruction routes.
-/
theorem petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).prod id ≤
      DkMath.ABC.supportMass (GN d x u) :=
  DkMath.ABC.supportMass_ge_prod_of_prime_channel_family
    (n := GN d x u) hGN0
    (petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata)

/--
Petal carrier-label data gives an ABC radical lower bound for the observed GN
surface.
-/
theorem petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).prod id ≤ DkMath.ABC.rad (GN d x u) := by
  simpa [DkMath.ABC.supportMass_eq_abc_rad] using
    petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata

/--
No-lift carrier-label data gives the same ABC radical lower bound.
-/
theorem petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).prod id ≤ DkMath.ABC.rad (GN d x u) := by
  simpa [DkMath.ABC.supportMass_eq_abc_rad] using
    petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata

end Petal
end DkMath
