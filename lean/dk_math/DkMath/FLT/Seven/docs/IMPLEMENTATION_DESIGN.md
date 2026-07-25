# FLT7 seven-primary terminal route: implementation design

Updated: 2026-07-24  
Target branch: `wip/FLT7-magic-core-260722-WiseWolf`

## 1. Scope

This document gives Codex an implementation design for the work after:

```text
SevenBaseTerminalPrimePowerScaleProjection.lean
SevenBaseTerminalPrimePowerPairScaleGluing.lean
```

The design separates four kinds of gluing that must not be conflated:

```text
1. scale-residue gluing
2. coordinate-residue gluing
3. local-equation certificate preservation
4. signed integral reconstruction
```

Chinese remainder theory solves the first two over a finite set of pairwise coprime moduli. It does not automatically solve the third or fourth.

## 2. Existing types to reuse

The implementation must build on these existing types.

```lean
AwaySevenBaseTerminalQuotientCorePacket
AwaySevenBaseTerminalUnitSectorPacket
AwaySevenBaseTerminalRoutingPacket
AwaySevenBaseTerminalOriginalPrimeDepthPacket
AwaySevenBaseTerminalPrimePowerClassificationPacket
AwaySevenBaseTerminalPrimePowerOrbitPacket
AwayNonSevenPrimePowerOrbitProjection
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket
AwaySevenBaseTerminalPrimePowerPairScaleGluingPacket
```

Important existing values and theorems include:

```lean
awaySevenBaseTerminalCubicRootLoad
AwayNonSevenPrimeDepthPacket.modulus
AwayNonSevenPrimeDepthPacket.modulus_coprime_of_prime_ne
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.localScale
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.localScale_isUnit
AwaySevenBaseTerminalPrimePowerScaleProjectionPacket.actual_eq_weightedScale
AwaySevenBaseTerminalRoutingPacket
  .nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
AwaySevenBaseTerminalRoutingPacket
  .nonempty_pairScaleGluingPacket_of_dvd_cubicRootLoad
```

Use exact current names from the source if a namespace-qualified name differs slightly.

## 3. Proposed module layout

Add the remaining implementation in this order.

```text
DkMath/FLT/Seven/
  SevenBaseTerminalPrimeSupport.lean
  SevenBaseTerminalPrimeScaleFamily.lean
  SevenBaseTerminalPrimePowerFiniteScaleGluing.lean
  SevenBaseTerminalPrimePowerFiniteScaleReduction.lean
  SevenBaseTerminalCubicRootLoadModulus.lean
  SevenBaseTerminalGlobalCoordinates.lean
  SevenBaseTerminalLocalCertificateFamily.lean
  SevenBaseTerminalLiftedReconstruction.lean
  SevenBaseTerminalExclusion.lean
  SevenBaseTerminalDescentClosure.lean
```

Do not create all files in one checkpoint. Create a file only when the previous layer has established the input API required by it.

## 4. Module: `SevenBaseTerminalPrimeSupport.lean`

### 4.1. Imports

Start with the thinnest import that provides the fixed routing packet and the terminal cubic-root load. Add `Mathlib` prime-factor imports only if not already transitively available.

### 4.2. Positivity API

Before using `Nat.primeFactors`, expose:

```lean
theorem awaySevenBaseTerminalCubicRootLoad_pos ... :
  0 < awaySevenBaseTerminalCubicRootLoad r
```

or reuse an existing theorem with this content.

The proof should come from positivity/nonvanishing of the three cubic-root factors already carried by the routing packet.

Also export:

```lean
theorem awaySevenBaseTerminalCubicRootLoad_ne_zero ... :
  awaySevenBaseTerminalCubicRootLoad r ≠ 0
```

### 4.3. Canonical support

Preferred definition:

```lean
def awaySevenBaseTerminalPrimeSupport
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) : Finset ℕ :=
  Nat.primeFactors (awaySevenBaseTerminalCubicRootLoad r)
```

Confirm the exact mathlib signature of `Nat.mem_primeFactors` in the current environment.

Required theorem shape:

```lean
theorem mem_awaySevenBaseTerminalPrimeSupport_iff ... :
    q ∈ awaySevenBaseTerminalPrimeSupport r ↔
      Nat.Prime q ∧ q ∣ awaySevenBaseTerminalCubicRootLoad r
```

Then prove:

```lean
theorem primeSupport_ne_seven ...
    (hq : q ∈ awaySevenBaseTerminalPrimeSupport r) : q ≠ 7
```

Use the existing terminal theorem that primes of the cubic-root load are non-seven.

### 4.4. Index subtype

Define a canonical dependent index:

```lean
abbrev AwaySevenBaseTerminalPrimeIndex
    {x y z : ℕ} (r : AwayCubicRoutingPacket x y z) :=
  {q : ℕ // q ∈ awaySevenBaseTerminalPrimeSupport r}
```

Export:

```lean
PrimeIndex.prime
PrimeIndex.dvd_cubicRootLoad
PrimeIndex.ne_seven
```

This subtype should be the index type for all later finite families.

## 5. Module: `SevenBaseTerminalPrimeScaleFamily.lean`

### 5.1. Purpose

Choose one existing scale projection packet for every canonical terminal prime.

### 5.2. Structure

Recommended shape:

```lean
structure AwaySevenBaseTerminalPrimeScaleFamily
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (packet : AwaySevenBaseTerminalRoutingPacket (source := source) p) : Type where
  localPacket :
    (q : AwaySevenBaseTerminalPrimeIndex r) →
      AwaySevenBaseTerminalPrimePowerScaleProjectionPacket packet q.1
```

### 5.3. Constructor

A noncomputable constructor may use:

```lean
Classical.choose
```

on:

```lean
packet.nonempty_primePowerScaleProjectionPacket_of_dvd_cubicRootLoad
```

The theorem should be:

```lean
noncomputable def AwaySevenBaseTerminalRoutingPacket.primeScaleFamily ...
```

or:

```lean
theorem nonempty_awaySevenBaseTerminalPrimeScaleFamily ...
```

Choose one style and keep later APIs consistent.

### 5.4. Accessors

Provide short accessors:

```lean
PrimeScaleFamily.localDepth
PrimeScaleFamily.localModulus
PrimeScaleFamily.localScale
PrimeScaleFamily.localScale_isUnit
PrimeScaleFamily.localActual
PrimeScaleFamily.localModel
PrimeScaleFamily.localActual_eq_weightedScale
```

The accessor types should reduce transparently to the existing projection packet fields.

### 5.5. Distinct-prime coprimality

For distinct subtype indices, prove:

```lean
theorem PrimeScaleFamily.localModulus_coprime
    (q₁ q₂ : AwaySevenBaseTerminalPrimeIndex r)
    (hneq : q₁ ≠ q₂) :
    Nat.Coprime (family.localModulus q₁) (family.localModulus q₂)
```

Reduce subtype inequality to `q₁.1 ≠ q₂.1` and reuse the existing pair theorem.

## 6. Generic finite CRT helper

Before tying recursion directly to FLT7, consider a small private or reusable helper local to the finite-gluing module.

### 6.1. Why a helper is useful

The existing pair packet glues two terminal scale packets. Finite induction must glue:

```text
an accumulated combined scale
with
one new local scale
```

The accumulated object is no longer a terminal local packet. Therefore the pair packet alone is not the induction algebra.

### 6.2. Candidate generic packet

```lean
structure BinaryUnitResidueGluingPacket
    (m₁ m₂ : ℕ) (s₁ : ZMod m₁) (s₂ : ZMod m₂) : Type where
  coprime : Nat.Coprime m₁ m₂
  combined : ZMod (m₁ * m₂)
  reductions : ZMod.chineseRemainder coprime combined = (s₁, s₂)
```

Optionally add:

```lean
combined_isUnit : IsUnit combined
```

Prove unit preservation separately if the initial implementation becomes too large.

### 6.3. Reduction representation

For arbitrary finite products, dependent `ZMod` casts can become cumbersome. Use one stable reduction predicate throughout the module.

Recommended value-level predicate:

```lean
def ZModReducesTo {M m : ℕ} (global : ZMod M) (local : ZMod m) : Prop :=
  ((global.val : ℕ) : ZMod m) = local
```

When needed, also store:

```lean
m ∣ M
```

An alternative is:

```lean
global.val % m = local.val
```

Pick one representation and prove conversion lemmas once. Do not mix several congruence encodings in later files.

## 7. Module: `SevenBaseTerminalPrimePowerFiniteScaleGluing.lean`

### 7.1. Product modulus

For a family define:

```lean
noncomputable def PrimeScaleFamily.combinedModulus : ℕ :=
  ∏ q : AwaySevenBaseTerminalPrimeIndex r, family.localModulus q
```

The exact syntax may instead use `Finset.univ` after installing `Fintype` for the subtype.

### 7.2. Finite gluing packet

Recommended structure:

```lean
structure AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) : Type where
  combinedScale : ZMod family.combinedModulus
  localModulus_dvd_combined :
    ∀ q, family.localModulus q ∣ family.combinedModulus
  reduces :
    ∀ q, ZModReducesTo combinedScale (family.localScale q)
```

Add later:

```lean
combinedScale_isUnit : IsUnit combinedScale
```

if it is not convenient in the first checkpoint.

### 7.3. Induction invariant

If direct `Fintype` CRT is unavailable, induct on a list or Finset of prime indices.

Maintain:

```text
support subset S
M_S = product of local moduli over S
s_S : ZMod M_S
all local reductions for q ∈ S
```

For the insert step prove:

```lean
Nat.Coprime M_S (family.localModulus q)
```

from pairwise coprimality.

Confirm exact mathlib lemmas for coprimality of a product. If API friction is high, prove the needed Finset lemma locally by induction rather than importing a large unrelated theory.

### 7.4. Empty support

The canonical load is positive, but it may equal `1`. The empty support case must still typecheck.

Use:

```text
combined modulus = 1
combined scale = 1
```

`isUnit_one` handles the trivial ring case.

### 7.5. Public constructor

Required result:

```lean
theorem nonempty_awaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet) :
    Nonempty (AwaySevenBaseTerminalPrimePowerFiniteScaleGluingPacket family)
```

## 8. Module: `SevenBaseTerminalPrimePowerFiniteScaleReduction.lean`

Separate reduction usability from the CRT construction proof.

### 8.1. Required API

```lean
FiniteScaleGluingPacket.reduces_to_localScale
FiniteScaleGluingPacket.localScale_isUnit
FiniteScaleGluingPacket.combinedScale_isUnit
FiniteScaleGluingPacket.localActual_eq_weightedScale
```

The last theorem should not claim that the combined scale directly acts in the local ring. It should first reduce the combined scale to the local scale and then rewrite the existing local orbit equation.

### 8.2. Coordinatewise reduction lemma

For weights `3` and `7`, prove generic lemmas:

```lean
reduction_pow_three
reduction_pow_seven
reduction_weighted_root_coordinate
reduction_weighted_endpoint_coordinate
```

These will be reused when gluing actual/model coordinates later.

## 9. Module: `SevenBaseTerminalCubicRootLoadModulus.lean`

### 9.1. The exponent transport problem

The local modulus exponent is currently exact for the original routing cell:

```text
e_q = padicValNat q (routingCell ...)
```

The finite product reconstructs the cubic-root load only after proving:

```text
e_q = padicValNat q (awaySevenBaseTerminalCubicRootLoad r)
```

### 9.2. Suggested intermediate theorems

For the local cell selected by `q`:

```lean
q_not_dvd_other_cells_in_column
padicValNat_rootFactor_eq_padicValNat_selectedCell
q_not_dvd_other_rootFactors
padicValNat_cubicRootLoad_eq_padicValNat_rootFactor
```

Then combine them:

```lean
terminalPrimeDepth_exponent_eq_padicValNat_cubicRootLoad
```

Do not prove these by cancellation in `Nat` unless positivity and exact factorization are explicit. Prefer the existing coprime routing identities and `padicValNat` product theorems.

### 9.3. Product theorem

Once exponent transport is established, prove:

```lean
PrimeScaleFamily.combinedModulus_eq_cubicRootLoad
```

A canonical prime-factor product theorem may already exist in mathlib. Confirm the exact theorem before reimplementing unique factorization.

If the equality is false because the support omits a factor, record the exact corrected identity and stop.

## 10. Module: `SevenBaseTerminalGlobalCoordinates.lean`

### 10.1. Motivation

`AwayRoutingPrimePowerSolution` depends on both:

```text
modulus
routing column
```

Different terminal primes may occupy different columns. Therefore there is no single value of the existing solution type that can directly hold all local models.

Introduce a column-independent coordinate carrier.

### 10.2. Generic coordinates

Recommended definition:

```lean
structure AwayRoutingCoordinates (R : Type*) where
  u : R
  v : R
  y : R
  z : R
```

Add conversions:

```lean
AwayRoutingPrimePowerSolution.toCoordinates
AwayNonSevenPrimePowerOrbitProjection.actualCoordinates
AwayNonSevenPrimePowerOrbitProjection.modelCoordinates
```

### 10.3. Coordinatewise finite gluing

Glue the four local model coordinates by CRT into:

```lean
AwayRoutingCoordinates (ZMod family.combinedModulus)
```

Do the same for actual coordinates if useful, although actual coordinates should also be reducible directly from the original integral data.

Suggested packets:

```lean
AwaySevenBaseTerminalGlobalModelCoordinatesPacket
AwaySevenBaseTerminalGlobalActualCoordinatesPacket
```

Each packet stores four combined coordinates and four families of local reduction equations.

### 10.4. Important limitation

Coordinate CRT always provides a finite residue tuple. It does not prove that this tuple satisfies one column-independent global polynomial system.

Keep the local column and equation certificates separately.

## 11. Module: `SevenBaseTerminalLocalCertificateFamily.lean`

### 11.1. Purpose

Preserve the exact statement satisfied at each local prime power after coordinate gluing.

Recommended structure:

```lean
structure AwaySevenBaseTerminalLocalCertificateFamily
    (family : AwaySevenBaseTerminalPrimeScaleFamily packet)
    (globalModel : AwayRoutingCoordinates (ZMod family.combinedModulus)) : Type where
  local_model_reduction : ∀ q, ...
  local_column : ∀ q, RootRoutingColumn
  local_solution_certificate : ∀ q,
    AwayRoutingPrimePowerSolution
      (family.localModulus q)
      p.row
      (local_column q)
```

The exact structure may reuse `family.localPacket q |>.projection.model` instead of copying it.

### 11.2. What to analyze

Determine whether the local columns and canonical root parameters satisfy an additional global compatibility law.

Possible results:

```text
all local models come from one integral parameter
local models split into finitely many coherent sectors
some pair of local certificates is incompatible with a global signed model
```

Name and package whichever result Lean supports.

## 12. Module: `SevenBaseTerminalLiftedReconstruction.lean`

### 12.1. Stage 1: modular weighted equation

Using combined model coordinates and combined scale, construct combined weighted coordinates:

```text
root coordinates multiplied by combinedScale^3
endpoint coordinates multiplied by combinedScale^7
```

Prove that reduction at every local modulus recovers the actual local coordinates.

This theorem is modular and should be achievable before integral reconstruction.

### 12.2. Stage 2: signed representatives

Define a signed representative function for `ZMod M`, for example in the interval centered at zero, only if no suitable existing helper exists.

Do not use unsigned `.val` when the terminal equations require signed integer information.

Candidate packet:

```lean
structure AwaySevenBaseTerminalSignedLiftCandidate where
  scale : ℤ
  model : AwayRoutingCoordinates ℤ
  weighted : AwayRoutingCoordinates ℤ
  scale_modulus : ...
  local_reductions : ...
```

### 12.3. Stage 3: equality criterion

A congruence modulo the combined modulus becomes an integer equality only with an additional theorem such as:

```text
combined modulus divides the difference
absolute value of the difference is strictly smaller than the modulus
```

or an exact factorization proving that no other multiple is possible.

Package the equality criterion as a named theorem. Do not bury it in `omega` or `norm_num` after adding an unjustified bound.

### 12.4. Reconstruction outcomes

Define one of:

```lean
AwaySevenBaseTerminalSignedReconstructionPacket
AwaySevenBaseTerminalSignedReconstructionObstruction
```

The obstruction form is acceptable and may be the useful theorem.

## 13. Module: `SevenBaseTerminalExclusion.lean`

### 13.1. Inputs

Use the existing exact row normal forms from `SevenBaseTerminalPacket.lean` and the result of lifted reconstruction.

### 13.2. Branches

Implement three explicit row cases or two unit-sector cases:

```text
positive sector: row Y
negative sector: row Z or row Sum
```

Do not erase the row before the endpoint quotient and load equations have been specialized.

### 13.3. Target theorem forms

Preferred unconditional target:

```lean
theorem no_terminal_depth_one_packet ... :
  IsEmpty (AwaySevenBaseTerminalRoutingPacket ...)
```

or a contradiction from a packet value.

If one arithmetic statement remains, define:

```lean
def AwaySevenBaseTerminalArithmeticReceiver : Prop := ...
```

and prove:

```lean
terminal_exclusion_of_receiver
```

The receiver must contain only the missing arithmetic fact. It must not restate terminal exclusion itself.

## 14. Module: `SevenBaseTerminalDescentClosure.lean`

### 14.1. Purpose

Construct the existing `AwayDescentClosureProvider` from the completed terminal theorem.

### 14.2. Requirements

Use the pre-existing descent interface. The new module should be a bridge, not a second independent descent framework.

Prove all preservation facts explicitly:

```text
positivity
primitive normalization
FLT7 equation
strict measure decrease
coverage of all routing branches
```

### 14.3. Final export

Only after provider construction should `DkMath.FLT.Seven` import the new closure and final theorem modules.

## 15. Facade policy

During development, add each completed module to:

```text
DkMath/FLT/Seven.lean
```

only after its focused build passes.

Update the facade docstring at major boundaries:

```text
finite scale synchronization complete
complete modulus relation complete
signed reconstruction complete
terminal exclusion complete
descent closure complete
```

Do not change the current statement that terminal exclusion and lifted signed reconstruction are open until the corresponding theorem is actually imported.

## 16. Checkpoint discipline

Every Codex checkpoint should report:

```text
files changed
new definitions
new theorem names
mathematical meaning
what remains unproved
whether the facade was updated
focused build command and result
```

Recommended focused build pattern:

```text
lake build DkMath.FLT.Seven.<NewModule>
lake build DkMath.FLT.Seven
```

The project-level build policy may be applied separately by the user.

## 17. First Codex task

The first implementation request should be limited to:

```text
SevenBaseTerminalPrimeSupport.lean
```

Required result:

```text
canonical finite support of terminal cubic-root primes
membership iff prime and divides the load
all support primes are non-seven
canonical prime-index subtype
```

Do not implement finite CRT in the same checkpoint.

After this task, stop and report the exact theorem names and any mathlib API mismatch found around `Nat.primeFactors`.

## 18. TERM-009 chart-resolution boundary

`SevenBaseTerminalFermatChartResolution.lean` is the canonical terminal chart
layer.  Later work should consume:

```lean
AwaySevenBaseTerminalUnitSectorPacket.fermatChartResolution
```

rather than reopening the three original row profiles independently.  Its
meaning is deliberately asymmetric:

```text
Row Y   has an existing natural RamifiedCoordinateNormalForm
Row Sum is impossible
Row Z   has a proved signed chart and proved seven-divisible signed gap
```

The Row-Z continuation target is exactly:

```lean
AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
```

It asks only for a root satisfying

```lean
cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
  sevenAxis * root ^ 7
```

All nonzero, primitive, Fermat-equation, and gap-divisibility fields are
already discharged.  A future signed extractor should prove this receiver
without adding positivity to the signed chart and without assuming terminal
exclusion.  Reusing the natural extractor requires a separately designed
integer factorization layer because the current chain uses natural
subtraction, natural `GN`, positivity, `padicValNat`, and
`seventh_power_factor_split`.

Do not claim FLT7 after inhabiting this receiver alone.  The natural ramified
summit remains a separate closure problem.
