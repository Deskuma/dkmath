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
Carrier-label map data identifies the ABC label support cardinality with the
selected finite index cardinality.

The support is defined by `Finset.image`; the point of this theorem is that
the Petal noncollision contract prevents that image from losing entries.
-/
theorem petalCarrierLabelMapData_labelSupport_card_eq
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).card = I.card := by
  unfold petalCarrierLabelSupport
  exact Finset.card_image_of_injOn (petalCarrierLabelMapData_label_injOn hdata)

/--
No-lift carrier-label map data has the same support-cardinality identification.

The no-lift condition is not needed for cardinality; the inherited
label-noncollision contract is enough.
-/
theorem petalNoLiftCarrierLabelMapData_labelSupport_card_eq
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    (petalCarrierLabelSupport I qOf).card = I.card := by
  unfold petalCarrierLabelSupport
  exact Finset.card_image_of_injOn (petalNoLiftCarrierLabelMapData_label_injOn hdata)

/--
A finite natural support whose members are all at least `2` has product at
least `2 ^ card`.

This small counting spine is intentionally local to the Petal/ABC bridge:
it converts a support cardinality statement into a product lower bound without
committing to any stronger ABC or Zsigmondy vocabulary.
-/
theorem petal_two_pow_card_le_prod_of_two_le
    {S : Finset ℕ}
    (hS : ∀ q, q ∈ S → 2 ≤ q) :
    2 ^ S.card ≤ S.prod id := by
  classical
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _hS
    simp
  · intro p s hp ih hS
    have hp_two : 2 ≤ p := hS p (Finset.mem_insert_self p s)
    have hs_two : ∀ q, q ∈ s → 2 ≤ q := by
      intro q hq
      exact hS q (Finset.mem_insert_of_mem hq)
    have ih' : 2 ^ s.card ≤ s.prod id := ih hs_two
    calc
      2 ^ (insert p s).card = 2 ^ s.card * 2 := by
        simp [hp, Nat.pow_succ]
      _ = 2 * 2 ^ s.card := by
        rw [Nat.mul_comm]
      _ ≤ p * s.prod id := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul ih' hp_two
      _ = (insert p s).prod id := by
        simp [hp]

/--
Carrier-label map data turns selected index count into a lower bound on the
label-support product.
-/
theorem petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ (petalCarrierLabelSupport I qOf).prod id := by
  rw [← petalCarrierLabelMapData_labelSupport_card_eq I hdata]
  exact petal_two_pow_card_le_prod_of_two_le
    (fun q hq =>
      (petalCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata q hq).1.two_le)

/--
No-lift carrier-label map data gives the same count-to-product lower bound.
-/
theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ (petalCarrierLabelSupport I qOf).prod id := by
  rw [← petalNoLiftCarrierLabelMapData_labelSupport_card_eq I hdata]
  exact petal_two_pow_card_le_prod_of_two_le
    (fun q hq =>
      (petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata q hq).1.two_le)

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

/--
Carrier-label map data gives an ABC support-mass lower bound measured only by
the number of selected Petal channels.
-/
theorem petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
  le_trans
    (petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
    (petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata)

/--
No-lift carrier-label map data gives the same channel-count lower bound on
ABC support mass.
-/
theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
  le_trans
    (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
    (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata)

/--
Carrier-label map data gives an ABC radical lower bound measured by selected
Petal channel count.
-/
theorem petalCarrierLabelMapData_two_pow_card_le_rad_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
  le_trans
    (petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
    (petalCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)

/--
No-lift carrier-label map data gives the same channel-count lower bound on the
ABC radical.
-/
theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
    {ι : Type _}
    (I : Finset ι)
    {d x u : ℕ}
    {mOf qOf : ι → ℕ}
    (hGN0 : GN d x u ≠ 0)
    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
  le_trans
    (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
    (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)

/--
Direct PrimitiveBeam-to-ABC support-mass count lower bound in body coordinates.

PrimitiveBeam witnesses supply the Petal carrier locations.  The address and
label-recovery hypotheses ensure that the selected labels remain distinct, so
`card I` independent prime supports force `2 ^ I.card` into the ABC support
mass of the GN surface.
-/
theorem petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
  petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0
    (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
      I d x u mOf qOf hd hd1 hm hminj hlabel hprim)

/--
Direct PrimitiveBeam-to-ABC radical count lower bound in body coordinates.

This is the compact ABC-facing form:

```text
PrimitiveBeam family with k selected carriers
  -> 2^k <= rad(GN d x u)
```
-/
theorem petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
  petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0
    (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
      I d x u mOf qOf hd hd1 hm hminj hlabel hprim)

/--
Direct Zsigmondy-to-ABC support-mass count lower bound on the GN surface
`GN d (a - b) b`.

Zsigmondy supplies carrier locations; the explicit family-level address and
label-recovery hypotheses supply distinct selected support.
-/
theorem petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
    {ι : Type _}
    (I : Finset ι)
    (a b d : ℕ)
    (mOf qOf : ι → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d (a - b) b) :=
  petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0
    (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)

/--
Direct Zsigmondy-to-ABC radical count lower bound on the GN surface
`GN d (a - b) b`.

This is the compact Zsigmondy-facing ABC form:

```text
Zsigmondy primitive-divisor family with k selected carriers
  -> 2^k <= rad(GN d (a - b) b)
```
-/
theorem petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
    {ι : Type _}
    (I : Finset ι)
    (a b d : ℕ)
    (mOf qOf : ι → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
    (hminj : Set.InjOn mOf ↑I)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
    (hprim :
      ∀ i, i ∈ I →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ I.card ≤ DkMath.ABC.rad (GN d (a - b) b) :=
  petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0
    (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)

end Petal
end DkMath
