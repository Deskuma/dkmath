# FLGNB Petal Roadmap

## Position

This note records the next implementation plan after the
`FermatLittleGNBridge` checkpoint.

The current project target is not only primality itself.  The target is the
structure around primeness:

```text
prime character
primitive prime factor
divisibility support
GN / Beam / Petal observation
```

The base tool is the binomial theorem, but the preferred direction is now:

```text
GN difference kernel
  -> Petal / relative polygon form
  -> Pascal coefficient section
  -> prime-row and p-adic observation
  -> primitive-factor and Zsigmondy bridge
```

`DkMath.Petal.*` should become the package where the Petal side of this route is
made visible.

Current status:

```text
Petal import surface: implemented
Petal GN bridge: implemented for the degree-three S0 face
Petal counting layer: implemented
Petal address layer: implemented
Dynamic / factorial / prime-base orbit layer: implemented
Distinct / strict prime-base sequence layer: implemented
```

This places Petal as the bridge layer between:

```text
Phase 4.5: AKSBridge v1
Phase 5: Zsigmondy preparation
```

The reason for this intermediate layer is that the project wants a
factorial-like and primorial-like counting surface without committing the next
step to Gamma-function continuation.  Petal counting keeps the construction
inside natural-number products and divisibility first.

## Design Principle

The Petal package should describe the relative polygon layer, not replace the
existing number-theory proofs.

The intended reading is:

```text
(x + u)^d = Core + Beam + Gap

GN d x u = ((x + u)^d - u^d) / x
```

For `d = 3`, the GN kernel becomes the basic Petal form:

```text
GN 3 (c - b) b = c^2 + c*b + b^2
```

This is currently implemented as:

```lean
theorem GN_three_sub_eq_S0_nat
```

The Petal layer should make this relation the main API surface:

```text
relative polygon / Petal form
  = low-degree visible face of GN
```

Thus, Pascal rows are not treated as the only source of the structure.  They are
the natural-number coefficient table obtained when the GN kernel is expanded.

## Existing Theorem Inventory

### `DkMath.UnitCycle.RelPolygon`

This file contains the current dynamic relative polygon skeleton.

Important names:

```lean
structure RPState
def g
def T
def I
lemma hg
lemma hT
theorem I_iterate_ge_sum
theorem I_iterate_ge_sum_fn
def s0
lemma g_s0
lemma g_Ts0
theorem sum_g_pos9_k2
theorem sum_g_pos9_k2_extra
theorem I_pos9_k2_ge_6
```

Role:

```text
dynamic state model for relative polygon growth
```

Planned Petal location:

```text
DkMath.Petal.RelPolygon
```

For the first pass, this should be a re-export / wrapper layer.

### `DkMath.FLT.PetalCoreUnit`

This file contains the current Petal unit and phase skeleton.

Important names:

```lean
structure PetalCoreUnit
def ofNP
def coreSucc
def coreVal
abbrev PeriodIndex
def HarmonicPoint
def isExceptionalPhase
lemma coreSucc_val
lemma harmonicPoint_ofNP
lemma notExceptional_ofNP_zero
```

Role:

```text
unit/phase vocabulary for Petal-side arithmetic
```

Planned Petal location:

```text
DkMath.Petal.CoreUnit
```

### `DkMath.FLT.PetalDetect`

This is the main existing arithmetic file for the Petal detector.

Important definitions:

```lean
def S0
def S1
def S0_nat
def S1_nat
```

Important theorem names:

```lean
theorem S0_ne_zero
theorem two_mul_S0
theorem two_mul_S0_nat
theorem sq_mod4
theorem not_square_of_mod4_eq3
theorem S0_mod4_eq3_of_congr1
theorem S0_not_square_of_congr1
theorem diff_kernel
theorem diff_kernel_nat
theorem apb_dvd_S1
theorem apb_dvd_S0_iff_dvd_bsq
theorem apb_dvd_S0_implies_eq_one
theorem S0_comm
theorem S1_comm
theorem S0_le_S1_nat
theorem S0_as_diff
theorem S0_related_perfect_square_property
theorem mod_q_ab_analysis
theorem prime_dvd_S0_coprime_imp_not_dvd_apb
theorem padicValNat_le_one_of_not_sq_dvd
theorem zsigmondy_not_dvd_apb
```

Role:

```text
S0/S1 completed phase, difference kernel, and divisibility detector
```

Planned Petal location:

```text
DkMath.Petal.Forms
```

Initial policy:

```text
Keep the existing file in place.
Expose Petal-facing aliases and imports from DkMath.Petal.Forms.
Move proofs only after downstream dependencies are stable.
```

### `DkMath.FLT.CosmicPetalBridge`

This file is the current bridge from GN and the cosmic formula to Petal `S0`.

Important theorem names:

```lean
theorem sub_eq_mul_GN
theorem sub_pow_eq_mul_GN
theorem prime_dvd_GN_of_dvd_sub_not_dvd_left
theorem prime_dvd_GN_three_of_dvd_sub_not_dvd_left_via_zsigmondy
theorem dvd_GN_of_dvd_sub_pow
theorem dvd_GN_of_dvd_sub_cube_via_zsigmondy
theorem GN_three_sub_eq_S0_nat
theorem prime_dvd_S0_via_cosmic_bridge
theorem hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3
```

Role:

```text
GN -> S0 bridge for degree 3 Petal arithmetic
```

Planned Petal location:

```text
DkMath.Petal.GNBridge
```

This is the most important immediate bridge file.

### `DkMath.NumberTheory.Gcd.GN`

This file contains the gcd and valuation control around `GN`.

Important theorem names:

```lean
theorem gcd_boundary_sd_divides_exp_int
theorem gn_natCast_int
theorem gn_natCast
theorem natAbs_gn_natCast_int
theorem natAbs_gn_gap_natCast_int
theorem gn_sub_eq_sd_int
theorem quotientPrimePow_eq_gn_gap
theorem quotientPrimePow_natCast_eq_gn_int
theorem diffPowQuotient_eq_gn_int
theorem gcd_gap_GN_dvd_exp_int
theorem gcd_gap_GN_dvd_exp
theorem coprime_boundary_GN_of_coprime_add_of_coprime_exp
theorem body_not_perfect_pow_of_squarefree_GN_of_coprime_add
theorem body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add
theorem coprime_gap_GN_of_not_dvd_exp_prime
theorem padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
theorem not_sq_dvd_of_squarefree
theorem gcd_boundary_GN_three_eq_gcd_boundary_three
theorem gcd_boundary_GN_three_dvd_three
theorem coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

Role:

```text
gcd and p-adic control for GN, especially useful after S0 is identified with GN 3
```

Planned Petal location:

```text
DkMath.Petal.GcdBridge
```

### `DkMath.CosmicFormula.CosmicDerivativePower`

This file gives the analytic-looking kernel without starting from Gamma
completion.

Important names:

```lean
def powerKernel
theorem powerKernel_eq_GN_swap
theorem sub_pow_eq_u_mul_powerKernel
theorem sub_eq_u_mul_powerKernel
theorem cosmicKernel_pow_eq_powerKernel_of_ne_zero
```

`DkMath.CosmicFormula.CosmicDerivativePowerLimit` also has:

```lean
theorem continuous_powerKernel
theorem powerKernel_zero
theorem tendsto_powerKernel_zero
theorem tendsto_powerKernel_zero_punctured
theorem hasDerivAt_pow_cosmic
```

Role:

```text
continuous / derivative-facing version of the same GN kernel
```

Planned Petal relation:

```text
DkMath.Petal.AnalyticBridge
```

This should be later than the arithmetic bridge.

### `DkMath.FLT.PhaseLift`

This is a downstream consumer of `S0`.

Important names include:

```lean
def NoSqOnS0
def PrimitiveOnS0
def NonLiftableS0
def AllNonLiftableOnS0
def S0PrimeSupportExceptThree
theorem cube_sub_eq_mul_sub_S0
theorem prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff
theorem padicValNat_upper_bound_d3
```

Role:

```text
phase-lift and non-liftability layer
```

Policy:

```text
Do not move this into Petal at first.
Use Petal as its dependency surface later.
```

### `DkMath.FLT.GEisensteinBridge`

This file connects `S0` to an Eisenstein norm viewpoint.

Important names:

```lean
def eisensteinNormNat
theorem S0_eq_eisensteinNorm_shift
theorem GN3_sub_eq_S0
theorem GN3_sub_eq_eisensteinNorm_shift
```

Role:

```text
Petal S0 -> Eisenstein norm bridge
```

Planned Petal location:

```text
DkMath.Petal.EisensteinBridge
```

This should be a bridge layer, not the initial foundation.

## Petal Package Plan

The package is being built in small steps.  The current surface is:

```text
DkMath/Petal/Basic.lean
DkMath/Petal/Forms.lean
DkMath/Petal/RelPolygon.lean
DkMath/Petal/CoreUnit.lean
DkMath/Petal/GNBridge.lean
DkMath/Petal/Counting.lean
DkMath/Petal/Address.lean
DkMath/Petal/GcdBridge.lean
DkMath/Petal/EisensteinBridge.lean
DkMath/Petal.lean
```

Implemented:

```text
DkMath/Petal/Basic.lean
DkMath/Petal/Forms.lean
DkMath/Petal/RelPolygon.lean
DkMath/Petal/CoreUnit.lean
DkMath/Petal/GNBridge.lean
DkMath/Petal/Counting.lean
DkMath/Petal/Address.lean
DkMath/Petal.lean
```

Still planned:

```text
DkMath/Petal/GcdBridge.lean
DkMath/Petal/EisensteinBridge.lean
DkMath/Petal/AnalyticBridge.lean
```

### `DkMath.Petal.Basic`

Purpose:

```text
common Petal vocabulary and small aliases
```

Initial content:

```lean
import DkMath.FLT.PetalDetect

namespace DkMath
namespace Petal

-- aliases only at first

end Petal
end DkMath
```

This file should not become a proof dumping ground.

### `DkMath.Petal.Forms`

Purpose:

```text
S0/S1 and relative polygon forms
```

First-pass content:

```text
re-export or alias S0, S1, S0_nat, S1_nat
Petal-facing names for diff_kernel and diff_kernel_nat
Petal-facing names for commutativity and S0 <= S1
```

Candidate theorem aliases:

```lean
theorem petal_diff_kernel
theorem petal_diff_kernel_nat
theorem petal_S0_comm
theorem petal_S1_comm
theorem petal_S0_le_S1_nat
```

Do not rename the old theorem names away yet.  The first step is bridge
stability.

### `DkMath.Petal.RelPolygon`

Purpose:

```text
dynamic relative polygon growth model
```

First-pass content:

```text
import DkMath.UnitCycle.RelPolygon
```

Potential aliases:

```lean
abbrev RelPolygonState := RPState
```

Avoid heavy refactoring until imports are clear.

### `DkMath.Petal.CoreUnit`

Purpose:

```text
unit and phase vocabulary for Petal arithmetic
```

First-pass content:

```text
import DkMath.FLT.PetalCoreUnit
```

This gives `PetalCoreUnit`, `HarmonicPoint`, and exceptional phase vocabulary a
stable Petal-facing import path.

### `DkMath.Petal.GNBridge`

Purpose:

```text
GN kernel -> Petal S0 bridge
```

This should be the first theorem-heavy file in the package.

Initial bridge theorem candidates:

```lean
theorem S0_nat_eq_GN_three_sub
    {c b : Nat} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

This is the Petal-facing direction of:

```lean
GN_three_sub_eq_S0_nat
```

Next candidates:

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b

theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3]
```

These should follow from the existing FLGNB endpoint:

```lean
theorem prime_GN_modEq_one_of_not_dvd_x
theorem prime_not_dvd_GN_of_not_dvd_x
```

with `p = 3`, `x = c - b`, `u = b`.

This is the first concrete place where:

```text
Fermat boundary return
  -> GN control
  -> Petal S0 control
```

becomes a reusable bridge theorem.

Current status:

```text
implemented
```

Implemented names:

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
```

### `DkMath.Petal.Counting`

Purpose:

```text
fixed Petal totals, dynamic orbit products, factorial orbit,
and abstract prime-base prefix products
```

Current status:

```text
implemented
```

Implemented fixed and dynamic names:

```lean
def baseUnitCore
def inheritanceSlot
def lapBase
def relPetalTotal
def relPolygonKernel
def dynamicOrbitTotal
def dynamicPetalTotal
```

Implemented factorial and const bridges:

```lean
theorem dynamicOrbitTotal_const
theorem dynamicOrbitTotal_succIndex_eq_factorial
theorem dynamicPetalTotal_const
```

Implemented divisibility facts:

```lean
theorem dynamicOrbitTotal_base_dvd_of_lt
theorem dynamicOrbitTotal_dvd_succ
theorem dynamicOrbitTotal_dvd_of_le
```

Implemented prime-base orbit:

```lean
def primeBaseOrbitTotal
def IsPrimeBaseSequence
def IsDistinctPrimeBaseSequence
def IsStrictPrimeBaseSequence
```

Implemented prime-base persistence:

```lean
theorem primeBaseOrbitTotal_base_dvd_of_lt
theorem primeBaseOrbitTotal_prime_dvd_of_lt
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
theorem primeBaseOrbitTotal_dvd_of_le
```

Implemented sequence API:

```lean
theorem IsPrimeBaseSequence.prime_at
theorem IsDistinctPrimeBaseSequence.prime_at
theorem IsDistinctPrimeBaseSequence.injective
theorem IsDistinctPrimeBaseSequence.ne_of_ne
theorem IsDistinctPrimeBaseSequence.ne_of_lt
theorem IsStrictPrimeBaseSequence.prime_at
theorem IsStrictPrimeBaseSequence.strictMono
theorem IsStrictPrimeBaseSequence.injective
theorem IsStrictPrimeBaseSequence.distinct
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
theorem IsStrictPrimeBaseSequence.ne_of_lt
```

Role:

```text
avoid jumping directly to Gamma-function continuation;
first express factorial-like and primorial-like growth as prefix products
with stable divisibility persistence theorems
```

### `DkMath.Petal.Address`

Purpose:

```text
one-based Petal channel addressing and nested address observations
```

Current status:

```text
implemented
```

Implemented names:

```lean
def relPetalBlockSize
structure PetalAddress
def IsInheritanceChannel
def IsPetalChannel
def outerPetalAddress
def outerPetalRemainder
def nestedPetalAddress
```

Key theorems:

```lean
theorem outerPetalRemainder_le_prevTotal_of_valid
theorem outerPetalRemainder_valid_for_prevTotal
theorem outerPetalAddress_decompose
theorem outerPetalAddress_decompose_sub_one
theorem nestedPetalAddress_length
theorem nestedPetalAddress_head?_eq_none_iff_lap_zero
```

Role:

```text
make a Petal layer address into quotient-remainder arithmetic:

m = channel * blockSize + remainder
```

This gives a stable language for later nested channel observations.

### `DkMath.Petal.GcdBridge`

Purpose:

```text
transfer GN gcd control to S0/Petal statements
```

Candidate bridge theorem:

```lean
theorem coprime_boundary_S0_nat_of_coprime_of_not_dvd_three
```

This should be derived from:

```lean
theorem coprime_boundary_GN_three_of_coprime_of_not_dvd_three
```

using:

```lean
theorem GN_three_sub_eq_S0_nat
```

This file should also collect p-adic bridge statements where the S0 theorem is
only a rewritten GN theorem.

Status:

```text
completed
```

Implemented bridge files:

```text
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
```

Important names:

```lean
gcd_sub_S0_nat_eq_gcd_sub_three
padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
primitive_prime_dvd_S0_nat
primitive_prime_padicValNat_cube_sub_eq_S0_nat
primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
exists_prime_dvd_S0_nat_of_not_three_dvd_sub
```

This completed the Petal-side Zsigmondy preparation bridge for the cubic S0
surface.  The remaining experiment is the reduced-support / anchor vocabulary,
not the S0/GN bridge itself.

### `DkMath.Petal.ReducedSupport`

Purpose:

```text
introduce a small carrier-level vocabulary for r-started prime support
```

Status:

```text
initial API implemented
```

Implemented names:

```lean
HasNoPrimeBelow
HasAnchorPrime
HasPositiveAnchorPrime
hasAnchorPrime_prime
hasAnchorPrime_anchor_dvd
hasAnchorPrime_no_smaller_prime
hasAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_pos
hasPositiveAnchorPrime_ne_zero
hasPositiveAnchorPrime_of_pos
hasPositiveAnchorPrime_prime
hasPositiveAnchorPrime_anchor_dvd
hasPositiveAnchorPrime_no_smaller_prime
hasPositiveAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_self_of_prime
```

This layer intentionally does not import S0/GN bridge files yet.  It should
first remain a thin carrier predicate surface, then connect to GN/S0 support
only after a concrete theorem needs that bridge.

Design note:

```text
HasAnchorPrime is the wide raw carrier predicate.
HasPositiveAnchorPrime is the strict support predicate for nonzero carriers.
```

This keeps the entrance broad while preventing `0` from being treated as an
actual support carrier in downstream theorems.

### `DkMath.Petal.Anchor`

Purpose:

```text
connect positive anchored carriers to concrete S0/GN divisibility surfaces
```

Status:

```text
initial API implemented
```

Implemented names:

```lean
AnchoredS0Carrier
AnchoredGNCarrier
anchoredS0Carrier_anchor
anchoredS0Carrier_anchor_prime
anchoredS0Carrier_dvd_S0
anchoredS0Carrier_pos
anchoredS0Carrier_ne_zero
anchoredS0Carrier_anchor_le_of_prime_dvd
anchoredGNCarrier_anchor
anchoredGNCarrier_anchor_prime
anchoredGNCarrier_dvd_GN
anchoredGNCarrier_pos
anchoredGNCarrier_ne_zero
anchoredGNCarrier_anchor_le_of_prime_dvd
anchoredGNCarrier_of_anchoredS0Carrier
anchoredS0Carrier_of_anchoredGNCarrier
exists_anchoredS0Carrier_of_not_three_dvd_sub
```

This layer is the first place where `ReducedSupport` imports meet the S0/GN
surface.  `ReducedSupport` itself remains independent.

### `DkMath.Petal.BoundaryD3`

Purpose:

```text
record the degree-three split between the 3-boundary branch and the reduced
S0 branch
```

Status:

```text
initial API implemented
```

Implemented names:

```lean
BoundaryD3Branch
BoundaryD3Reduced
boundaryD3Branch_or_reduced
not_boundaryD3Branch_of_reduced
three_dvd_S0_nat_of_three_dvd_sub
three_dvd_sub_of_three_dvd_S0_nat
three_dvd_S0_nat_iff_three_dvd_sub
boundaryD3Reduced_three_not_dvd_S0_nat
boundaryD3Branch_three_dvd_S0_nat
boundaryD3Reduced_coprime_sub_S0_nat
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

This layer makes the cubic contact prime explicit:

```text
3 | S0_nat c b  iff  3 | (c - b)
```

In the reduced branch, and under `Nat.Coprime c b`, the boundary gap is
coprime to `S0_nat c b`.  This is the usable S0 surface for primitive and
Zsigmondy-facing arguments.

### `DkMath.Petal.EisensteinBridge`

Purpose:

```text
Petal S0 -> Eisenstein norm bridge
```

Status:

```text
initial API implemented
```

Implemented names:

```lean
petal_S0_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
petal_S0_nat_eq_eisensteinNorm_shift_of_lt
```

These should reference:

```lean
theorem S0_eq_eisensteinNorm_shift
theorem GN3_sub_eq_eisensteinNorm_shift
```

This layer is intentionally thin.  It re-exposes the existing FLT Eisenstein
norm facts through Petal-facing names so later Petal/Zsigmondy files can import
the package surface.

## Implementation Steps

### Step 1: Create the Petal import surface

Status:

```text
completed
```

Implemented:

```text
DkMath/Petal/Basic.lean
DkMath/Petal/Forms.lean
DkMath/Petal/RelPolygon.lean
DkMath/Petal/CoreUnit.lean
DkMath/Petal.lean
```

At this step, only import and expose the existing files.  No major proof moves.

Expected validation:

```sh
lake build DkMath.Petal
```

### Step 2: Add `DkMath.Petal.GNBridge`

Status:

```text
completed
```

Implemented the first Petal bridge theorem group:

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
```

Expected imports:

```lean
import DkMath.FLT.CosmicPetalBridge
import DkMath.NumberTheory.WeightedGNBridge
```

Expected validation:

```sh
lake build DkMath.Petal.GNBridge
lake build DkMath.Petal
```

### Step 3: Add `DkMath.Petal.Counting`

Status:

```text
completed
```

This step was added after the original roadmap because the project needed a
factorial-like and primorial-like prefix-product layer before moving to
Zsigmondy.

Implemented:

```text
fixed Petal totals
dynamic orbit products
factorial orbit bridge
prime-base prefix products
prime / distinct / strict prime-base sequence predicates
factor persistence across later prefix products
```

Expected validation:

```sh
lake build DkMath.Petal.Counting
lake build DkMath.Petal
```

### Step 4: Add `DkMath.Petal.Address`

Status:

```text
completed
```

This step fixes the one-based Petal channel address system and its
quotient-remainder decomposition.

Implemented:

```lean
theorem outerPetalAddress_decompose
theorem outerPetalAddress_decompose_sub_one
```

Expected validation:

```sh
lake build DkMath.Petal.Address
lake build DkMath.Petal
```

### Step 5: Add `DkMath.Petal.GcdBridge`

Status:

```text
completed
```

Transfer the existing GN gcd statements to S0-facing names.

Do this only by rewriting with:

```lean
GN_three_sub_eq_S0_nat
```

This step should not invent new gcd theory.  It should provide link theorem
names that downstream FLT and primitive-factor files can import.

Implemented as the three bridge files:

```text
DkMath/Petal/GcdBridge.lean
DkMath/Petal/PadicBridge.lean
DkMath/Petal/PrimitiveBridge.lean
```

Additional caller-friendly projection:

```lean
exists_prime_dvd_S0_nat_of_not_three_dvd_sub
```

### Step 5.5: Add `DkMath.Petal.ReducedSupport`

Status:

```text
initial API implemented
```

Implemented:

```lean
HasNoPrimeBelow
HasAnchorPrime
HasPositiveAnchorPrime
hasAnchorPrime_prime
hasAnchorPrime_anchor_dvd
hasAnchorPrime_no_smaller_prime
hasAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_pos
hasPositiveAnchorPrime_ne_zero
hasPositiveAnchorPrime_of_pos
hasPositiveAnchorPrime_prime
hasPositiveAnchorPrime_anchor_dvd
hasPositiveAnchorPrime_no_smaller_prime
hasPositiveAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_self_of_prime
```

Expected validation:

```sh
lake build DkMath.Petal.ReducedSupport
lake build DkMath.Petal
```

### Step 5.6: Add `DkMath.Petal.Anchor`

Status:

```text
initial API implemented
```

Implemented:

```lean
AnchoredS0Carrier
AnchoredGNCarrier
anchoredS0Carrier_anchor_prime
anchoredGNCarrier_anchor_prime
anchoredGNCarrier_of_anchoredS0Carrier
anchoredS0Carrier_of_anchoredGNCarrier
exists_anchoredS0Carrier_of_not_three_dvd_sub
```

Expected validation:

```sh
lake build DkMath.Petal.Anchor
lake build DkMath.Petal
```

### Step 5.7: Add `DkMath.Petal.BoundaryD3`

Status:

```text
initial API implemented
```

Implemented:

```lean
BoundaryD3Branch
BoundaryD3Reduced
boundaryD3Branch_or_reduced
not_boundaryD3Branch_of_reduced
three_dvd_S0_nat_of_three_dvd_sub
three_dvd_sub_of_three_dvd_S0_nat
three_dvd_S0_nat_iff_three_dvd_sub
boundaryD3Reduced_three_not_dvd_S0_nat
boundaryD3Branch_three_dvd_S0_nat
boundaryD3Reduced_coprime_sub_S0_nat
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

Expected validation:

```sh
lake build DkMath.Petal.BoundaryD3
lake build DkMath.Petal
```

### Step 6: Add `DkMath.Petal.EisensteinBridge`

Status:

```text
initial API implemented
```

Expose the Eisenstein norm route as a Petal-facing bridge.

This makes the following triangle explicit:

```text
GN 3
  <-> S0 Petal form
  <-> Eisenstein norm
```

Implemented:

```lean
petal_S0_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
petal_S0_nat_eq_eisensteinNorm_shift_of_lt
```

Expected validation:

```sh
lake build DkMath.Petal.EisensteinBridge
lake build DkMath.Petal
```

### Step 5.8: Petal cubic surface closure

Status:

```text
completed
```

This checkpoint closes the current degree-three Petal surface:

```text
S0_nat c b
  = GN 3 (c - b) b
  = shifted Eisenstein norm
```

Completed package layers:

```text
DkMath.Petal.GNBridge
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
DkMath.Petal.ReducedSupport
DkMath.Petal.Anchor
DkMath.Petal.BoundaryD3
DkMath.Petal.EisensteinBridge
```

Closed surface:

```text
S0 / GN3 / BoundaryD3 / Anchor / Eisenstein
```

The main interpretation is:

```text
BoundaryD3Reduced
  -> boundary and S0 are separated
  -> primitive S0 witnesses can be read as anchored carriers
  -> the same S0/GN3 face can be viewed as a shifted Eisenstein norm
```

Deferred:

```text
BoundaryD3Anchor split
FLT namespace dependency refactor
DkMath.Lib.* promotion of neutral Eisenstein and S0 facts
general d boundary behavior
full Zsigmondy bridge
FLT descent
```

Validation:

```sh
lake build DkMath.Petal
git diff --check
```

### Step 5.9: Zsigmondy preflight investigation

Status:

```text
investigated
```

Record:

```text
DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
```

Conclusion:

```text
Zsigmondy gives existence.
Petal gives location.
Squarefree/NoLift gives multiplicity.
```

The next Lean-facing bridge is `DkMath.Petal.ZsigmondyD3Bridge`.  It feeds the
reduced cubic Petal hypotheses into Zsigmondy's `d = 3` existence theorem and
shares the same witness with the anchored `S0_nat` carrier surface.

The same witness is also exposed as
`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q c b 3`, so later
squarefree/no-lift APIs can consume the primitive divisor without changing
the chosen `q`.

It should not try to prove `padicValNat q (c^3 - b^3) <= 1` without an explicit
squarefree or no-lift hypothesis.

### Step 6.0: Add `DkMath.Petal.ZsigmondyD3Bridge`

Status:

```text
initial API implemented
```

Implemented:

```lean
exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
primitivePrimeDivisor_d3_not_dvd_sub
primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3
primitivePrimeDivisor_d3_dvd_S0_nat
anchoredS0Carrier_of_primitivePrimeDivisor_d3
exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
```

Meaning:

```text
BoundaryD3Reduced hypotheses
  -> Zsigmondy primitive divisor q for c^3 - b^3
  -> the same q as an anchored S0 carrier
```

Expected validation:

```sh
lake build DkMath.Petal.ZsigmondyD3Bridge
lake build DkMath.Petal
```

### Step 7: Refactor imports gradually

Status:

```text
planned
```

After the Petal bridge files build, downstream files may be updated to import
Petal-facing modules.

Candidates:

```text
DkMath.FLT.PhaseLift
DkMath.FLT.GEisensteinBridge
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN*
```

Policy:

```text
Prefer import replacement and theorem alias usage first.
Move original definitions only when dependency direction becomes obviously cleaner.
```

## Relative Polygon Petal Plan

The phrase "relative polygon number" should be kept close to the existing note:

```text
DkMath/NumberTheory/docs/Petal_vs_termial.md
```

The conceptual relation is:

```text
termial T(n) = n(n + 1) / 2
relative polygon R(n) = n(n + 1)
```

Thus:

```text
R(n) = 2 * T(n)
```

and:

```text
T(a + b) = T(a) + T(b) + a*b
R(a + b) = R(a) + R(b) + 2*a*b
```

The Petal package should eventually formalize these as arithmetic lemmas.

Candidate future definitions:

```lean
def termialNat (n : Nat) : Nat := n * (n + 1) / 2
def relPolygonNat (n : Nat) : Nat := n * (n + 1)
```

Candidate future theorem names:

```lean
theorem relPolygonNat_eq_two_mul_termialNat
theorem termialNat_add
theorem relPolygonNat_add
theorem relPolygonNat_split
```

However, these should be added after the GN/S0 bridge surface is stable.  The
first Petal target is not a new polygon-number library.  The first target is to
make the already-used relative polygon/Petal detector visible as a package.

## Planned Bridge Link Theorems

### GN to Petal

```lean
theorem S0_nat_eq_GN_three_sub
    {c b : Nat} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

Purpose:

```text
make S0 a named Petal face of GN 3
```

### Fermat boundary to Petal

```lean
theorem three_S0_nat_modEq_one_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    S0_nat c b ≡ 1 [MOD 3]
```

Purpose:

```text
transfer the FLGNB theorem to the d = 3 Petal detector
```

### Non-divisibility support

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : Nat} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b
```

Purpose:

```text
read p-adic support directly from the Petal form
```

### GN gcd to Petal gcd

```lean
theorem coprime_boundary_S0_nat_of_coprime_of_not_dvd_three
```

Purpose:

```text
convert existing GN gcd control into S0/Petal gcd control
```

Exact statement should be chosen from the existing
`coprime_boundary_GN_three_of_coprime_of_not_dvd_three` theorem shape.

### Petal to Eisenstein

```lean
theorem petal_S0_eq_eisensteinNorm_shift
```

Purpose:

```text
connect the relative polygon Petal detector to the Eisenstein norm route
```

This bridge should come after the GN bridge, because the GN bridge is the main
route back to Pascal/Beam and primitive-factor work.

## Refactoring Policy

The current theorem base is valuable and should not be disturbed too early.

Use this order:

```text
1. create DkMath.Petal.* import surface
2. add Petal-facing aliases and bridge theorem names
3. update downstream imports only where it reduces confusion
4. move definitions only after dependencies are proven clean
```

Keep these files as downstream or specialized layers for now:

```text
DkMath.FLT.PhaseLift
DkMath.FLT.PrimeProvider.*
DkMath.FLT.GEisensteinBridge
```

Do not pull FLT-specific provider hypotheses into the Petal foundation.

The Petal package should stay focused on:

```text
relative polygon form
S0/S1 detector
GN degree-3 bridge
gcd and p-adic support links
Eisenstein bridge as a later connection
```

## Next Concrete Checkpoint

The next implementation checkpoint should be:

```text
Create DkMath.Petal.Basic / Forms / GNBridge / aggregate import.
Prove S0_nat_eq_GN_three_sub.
Prove the two d = 3 Fermat-boundary Petal bridge theorems.
Build DkMath.Petal.
```

This keeps the step small, but it creates the foundation for later primitive
factor and Zsigmondy-facing work.
