/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.ABCBridge

#print "file: DkMath.Petal.RangeFamily"

/-!
# Petal Range Family Constructors

This file is the first concrete finite-family construction layer for the
Petal-to-ABC route.

`DkMath.Petal.ABCBridge` intentionally consumes abstract finite carrier data:

```text
PetalCarrierLabelMapData on I
  -> 2^card(I) <= supportMass/rad(GN)
```

Here we provide the smallest concrete index choice:

```text
I = Finset.range k
mOf i = i + 1
```

The range supplies exactly `k` addresses, while `mOf i = i + 1` supplies
positive, injective selected values.  The caller still supplies the meaningful
arithmetic input: primitive/Zsigmondy witnesses and label injectivity.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom

/--
The standard range value map `i ↦ i + 1` is injective on `Finset.range k`.
-/
theorem rangeSuccValue_injOn (k : ℕ) :
    Set.InjOn (fun i : ℕ => i + 1) ↑(Finset.range k) := by
  intro i _hi j _hj h
  exact Nat.succ.inj h

/--
Pairwise label noncollision on natural range indices gives label injectivity on
`Finset.range k`.

This is a caller-facing helper for concrete experiments: it is often easier to
prove

```text
i < k, j < k, i != j -> qOf i != qOf j
```

than to construct `Set.InjOn qOf ↑(Finset.range k)` directly.
-/
theorem rangeLabel_injOn_of_pairwise_ne
    {k : ℕ} {qOf : ℕ → ℕ}
    (hneq :
      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j) :
    Set.InjOn qOf ↑(Finset.range k) := by
  intro i hi j hj hq
  by_contra hij
  exact hneq i (by simpa using hi) j (by simpa using hj) hij hq

/--
Body-coordinate range-family constructor for `PetalCarrierLabelMapData`.

The concrete address/value choice is:

```text
I = Finset.range k
mOf i = i + 1
```

The caller supplies label injectivity and the PrimitiveBeam witnesses.  This is
the first practical construction that can feed `ABCBridge` without manually
assembling every field of `PetalCarrierLabelMapData`.
-/
theorem petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
    (k d x u : ℕ)
    (qOf : ℕ → ℕ)
    (hd : 0 < d) (hd1 : 1 < d)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    PetalCarrierLabelMapData (Finset.range k) d x u (fun i => i + 1) qOf :=
  petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
    (Finset.range k) d x u (fun i => i + 1) qOf hd hd1
    (by
      intro i _hi
      exact Nat.succ_le_succ (Nat.zero_le i))
    (rangeSuccValue_injOn k)
    (by
      intro i hi j hj hq
      have hij : i = j := hqinj hi hj hq
      simp [hij])
    hprim

/--
Zsigmondy range-family constructor for `PetalCarrierLabelMapData`.

This is the range-indexed counterpart of
`petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family`.
-/
theorem petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
    (k a b d : ℕ)
    (qOf : ℕ → ℕ)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    PetalCarrierLabelMapData (Finset.range k) d (a - b) b (fun i => i + 1) qOf :=
  petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
    (Finset.range k) a b d (fun i => i + 1) qOf hd hd1 hab_lt
    (by
      intro i _hi
      exact Nat.succ_le_succ (Nat.zero_le i))
    (rangeSuccValue_injOn k)
    (by
      intro i hi j hj hq
      have hij : i = j := hqinj hi hj hq
      simp [hij])
    hprim

/--
Range-indexed PrimitiveBeam family gives the concrete ABC support-mass lower
bound `2^k <= supportMass(GN d x u)`.
-/
theorem petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
    (k d x u : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) := by
  simpa [Finset.card_range] using
    petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
      (Finset.range k) hGN0
      (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
        k d x u qOf hd hd1 hqinj hprim)

/--
Range-indexed PrimitiveBeam family gives the concrete ABC radical lower bound
`2^k <= rad(GN d x u)`.
-/
theorem petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
    (k d x u : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ k ≤ DkMath.ABC.rad (GN d x u) := by
  simpa [Finset.card_range] using
    petalCarrierLabelMapData_two_pow_card_le_rad_GN
      (Finset.range k) hGN0
      (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
        k d x u qOf hd hd1 hqinj hprim)

/--
Pairwise-noncollision version of
`petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family`.

The caller may provide label separation as
`i < k -> j < k -> i != j -> qOf i != qOf j`; this theorem converts it to the
`Set.InjOn` hypothesis required by the core range-family constructor.
-/
theorem petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
    (k d x u : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hneq :
      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) :=
  petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
    k d x u qOf hGN0 hd hd1
    (rangeLabel_injOn_of_pairwise_ne hneq) hprim

/--
Pairwise-noncollision version of
`petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family`.
-/
theorem petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
    (k d x u : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d x u ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d)
    (hneq :
      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
          (qOf i) (x + u) u d) :
    2 ^ k ≤ DkMath.ABC.rad (GN d x u) :=
  petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
    k d x u qOf hGN0 hd hd1
    (rangeLabel_injOn_of_pairwise_ne hneq) hprim

/--
Range-indexed Zsigmondy family gives the concrete ABC support-mass lower bound
`2^k <= supportMass(GN d (a - b) b)`.
-/
theorem petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
    (k a b d : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ k ≤ DkMath.ABC.supportMass (GN d (a - b) b) := by
  simpa [Finset.card_range] using
    petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
      (Finset.range k) hGN0
      (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
        k a b d qOf hd hd1 hab_lt hqinj hprim)

/--
Range-indexed Zsigmondy family gives the concrete ABC radical lower bound
`2^k <= rad(GN d (a - b) b)`.
-/
theorem petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
    (k a b d : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hqinj : Set.InjOn qOf ↑(Finset.range k))
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) := by
  simpa [Finset.card_range] using
    petalCarrierLabelMapData_two_pow_card_le_rad_GN
      (Finset.range k) hGN0
      (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
        k a b d qOf hd hd1 hab_lt hqinj hprim)

/--
Pairwise-noncollision version of
`petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family`.
-/
theorem petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
    (k a b d : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hneq :
      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ k ≤ DkMath.ABC.supportMass (GN d (a - b) b) :=
  petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
    k a b d qOf hGN0 hd hd1 hab_lt
    (rangeLabel_injOn_of_pairwise_ne hneq) hprim

/--
Pairwise-noncollision version of
`petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family`.
-/
theorem petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
    (k a b d : ℕ)
    (qOf : ℕ → ℕ)
    (hGN0 : GN d (a - b) b ≠ 0)
    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
    (hneq :
      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
    (hprim :
      ∀ i, i ∈ Finset.range k →
        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) :=
  petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
    k a b d qOf hGN0 hd hd1 hab_lt
    (rangeLabel_injOn_of_pairwise_ne hneq) hprim

end Petal
end DkMath
