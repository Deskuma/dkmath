# PRIM-PAR-000: Valuation Tower / Parity Asset Reconnaissance

Date: 2026-08-24
Branch: `wip/number-theory-primitive-structure-260822-v2`
Environment: Lean / Mathlib v4.32.2

This checkpoint is a read-only mathematical and API reconnaissance.  The
Lean source files, `lean-toolchain`, Lake configuration, dependency revisions,
and existing PRIM-C001/C002 and PRIM-L022 modules were not changed.

## Executive outcome

**Outcome B — LOSSLESS COORDINATE.**

DkMath and Mathlib already contain the ingredients for the local normal form

```text
v = 2 * (v / 2) + v % 2,       v % 2 ∈ {0, 1},
```

with `v = padicValNat p m`, and they already contain the finite exponent-slot
specification needed to interpret `p^j` for `1 ≤ j ≤ v`.  The exact
valuation/factorization bridge also already exists in Mathlib.  No new
`Finset` of local depths is needed.

The audit did not find an existing theorem connecting a parity-gap coordinate
to a stronger constraint on `SquareOffsetsFullyCovered n`.  The current
Direction/Depth and pair-overlap ledgers retain the support and depth facts
used by the Legendre frontier, while parity only records one additional
residue bit of an exact exponent.  It is therefore reusable bookkeeping, not
new leverage at this checkpoint.

In particular, local or global parity does not imply primality: odd
`Ω(m)` does not distinguish `Ω(m) = 1` from `Ω(m) = 3, 5, ...`.

## 1. Existing asset inventory

| Asset | Existing declarations | Owner and role |
|---|---|---|
| `p`-adic valuation | `DkMath.ABC.padicValNat_split`, `padicValNat_eq_zero_iff`, `Vp_ge_one_iff`, `padicValNat_one_le_of_prime_dvd`, `padicValNat_le_iff_dvd`, `padicValNat_pow` | `DkMath/ABC/PadicValNat.lean`; thin project wrappers over Mathlib valuation facts |
| Valuation readers | `ValuationProfile`, `profileOfPrime`, `diffMass`, `boundaryMass`, `beamMass` | `DkMath/NumberTheory/ValuationFlow/Basic.lean`; readers only, no parity abstraction |
| Exponent-slot specification | `NatBaseMultiplicityCompleteOn`, `FullExponentSlotChannelSet`, `FullExponentSlotCoverage` | `DkMath/NumberTheory/PrimitiveSet/FullExponentSlot.lean`; exact finite slot specification using `n.factorization p` |
| Exponent-slot bridge | `FullExponentSlotChannelSet.mem_channels_of_slot`, `exists_slot_of_mem_channels`, `fullExponentSlotCoverage_of_fullExponentSlotChannelSet` | `DkMath/NumberTheory/PrimitiveSet/FullExponentSlotBridge.lean`; proof-local `Finset.Icc 1 (n.factorization p)` is used for cardinality, not exposed as a new depth API |
| Primitive square body | `squareBody_large_prime_small_cofactor_split`, `old_prime_dvd_iff_dvd_large_prime_cofactor`, `primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody` | `DkMath/NumberTheory/Primitive/SquareBody.lean`; C001/C002 finite old-generated/fresh split |
| Legendre seat classes | `SquareAnchorCoprimeSimpleFreshSeat`, `SquareAnchorCoprimeSingletonDepthSeat`, `SquareAnchorCoprimeMultiSupportSeat`, `coprime_covered_seat_trichotomy` | `DkMath/NumberTheory/Legendre/Obstruction.lean`; exact finite support/depth classification |
| Localized frontier | `one_le_depthMultiplicity_add_pairMultiplicity_of_coprime_covered_not_simple`, `two_mul_totient_le_localDepth_add_localPair_of_fullyCovered...` | `DkMath/NumberTheory/Legendre/LocalizedObstruction.lean`; current Direction/Depth and pair ledgers |
| Two-cycle analogy | `val_succ`, `succ_succ`, `succ_succ_N` | `DkMath/Units/NPUnit.lean`; a conceptual half-phase model, not a Primitive dependency |

The NPUnit results are mathematically suggestive because two successor steps
preserve the phase, but they do not currently transfer a theorem into the
valuation or Primitive APIs.  The correct classification is therefore a
display/conceptual analogy, not a reusable dependency for PRIM-PAR.

## 2. Q1 — valuation and factorization bridge

The classification is **A: an exact theorem already exists**.

Mathlib provides, in
`.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Defs.lean`,

```lean
Nat.factorization_def (n : ℕ) {p : ℕ} (hp : p.Prime) :
  n.factorization p = padicValNat p n
```

Thus the desired orientation is obtained by symmetry, and the theorem is
stronger than the requested nonzero case: it does not require `n ≠ 0`.

The current DkMath wrapper
`DkMath.FLT.PrimeProvider.padicValNat_eq_factorization` in
`DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5Core.lean` has the reverse
orientation and adds `u ≠ 0`.  It is a FLT-specific thin wrapper and should
not become a Primitive dependency.  The canonical owner for a future bridge
is the Mathlib theorem `Nat.factorization_def`.

Related existing factorization declarations are:

- `Nat.factorization_mul`, requiring both factors to be nonzero;
- `Nat.factorization_mul_apply_of_coprime`, using `Nat.Coprime`;
- `Nat.factorization_mul_of_coprime`, the function-level coprime form;
- `Nat.factorization_pow` and `Nat.Prime.factorization_pow`.

## 3. Q2 — finite tower membership

The smallest existing chain is:

1. use `Nat.factorization_def` to replace `n.factorization p` by
   `padicValNat p n` under `Nat.Prime p`;
2. use the direct Mathlib theorem
   `padicValNat_dvd_iff_le`, whose orientation is
   `p ^ k ∣ n ↔ k ≤ padicValNat p n` and whose prime argument is supplied by
   `[Fact p.Prime]`;
3. alternatively use the DkMath wrapper
   `DkMath.ABC.padicValNat_le_iff_dvd hp hn k`, which presents the reverse
   orientation `k ≤ padicValNat p n ↔ p ^ k ∣ n` and takes `n ≠ 0` explicitly.

The lower bound `1 ≤ j` is an ordinary conjunction with the valuation bound.
The existing `FullExponentSlotChannelSet.mem_iff` already expresses the
finite tower as

```text
∃ p j, Prime p ∧ 1 ≤ j ∧ j ≤ n.factorization p ∧ q = p^j.
```

No new explicit `Finset` of local depths is justified.  The bridge module's
local `E := Finset.Icc 1 (s.1.factorization p)` is only a proof device for a
finite-cardinality lower bound; it is not missing semantic infrastructure.

## 4. Q3 — parity normal form

The required arithmetic is already available in Mathlib:

- `Nat.div_add_mod v 2` gives
  `2 * (v / 2) + v % 2 = v`; use symmetry for the requested orientation.
- `Nat.mod_lt` with the positive divisor `2` gives `v % 2 < 2`.
- `Nat.mod_two_eq_zero_or_one v` gives
  `v % 2 = 0 ∨ v % 2 = 1` directly.
- `Nat.even_iff` and `Nat.odd_iff` characterize the two residues.
- `Nat.even_or_odd` and `Nat.even_or_odd'` provide the corresponding
  disjunction or witness form.

For a fixed prime and nonzero natural, setting

```text
pairCount := padicValNat p m / 2
parityGap := padicValNat p m % 2
```

is therefore lossless.  `DkMath.ABC.padicValNat_split` is not the preferred
owner for this purpose: it is a first-layer/deep-layer `min`/`max` identity,
not a two-depth Euclidean decomposition.

A valuation-facing wrapper would add naming value for a later consumer, but
not proof power.  It should not be implemented in PRIM-PAR-000.

## 5. Q4 — local parity versus global `Ω`

Mathlib already has a finite global multiplicity function in
`.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`:

```lean
ArithmeticFunction.cardFactors
```

with scoped notation `Ω` under `ArithmeticFunction.Omega`.  The relevant
declarations are:

- `ArithmeticFunction.cardFactors_mul`, requiring both factors nonzero;
- `ArithmeticFunction.cardFactors_apply_prime`, giving `Ω p = 1` for prime
  `p`;
- `ArithmeticFunction.cardFactors_pow` and
  `cardFactors_apply_prime_pow`;
- `ArithmeticFunction.cardFactors_eq_sum_factorization`, giving
  `Ω n = n.factorization.sum (fun _ k => k)`.

There is no DkMath-specific total-`Ω` API in the audited Primitive or
ValuationFlow modules.  Since the Mathlib API is already available, a global
parity statement would be inexpensive in isolation.  Nevertheless, the
first implementation checkpoint should stop at **A: local `p`-direction
parity**.  A global `Ω` theorem has no current full-cover consumer and would
not turn odd multiplicity into primality.

## 6. Q5 — C002 fresh-split transport

For the C002 shape

```text
m = ℓ * k,
Nat.Prime ℓ,
P < ℓ,
Nat.Coprime ℓ k,
```

the existing generic transport chain is sufficient; no C002 geometry should
be reproved.

### Local valuation form

For every old prime `p ≤ P`, first use `P < ℓ` and primality to show
`p ≠ ℓ`, hence `¬ p ∣ ℓ`.  Then use
`padicValNat.eq_zero_of_not_dvd` and `padicValNat.mul` to obtain

```text
padicValNat p (ℓ * k)
  = padicValNat p ℓ + padicValNat p k
  = padicValNat p k.
```

For the fresh prime, `Nat.Coprime ℓ k` gives `¬ ℓ ∣ k`; combining
`padicValNat.mul` with `padicValNat_self` gives

```text
padicValNat ℓ (ℓ * k) = 1 + 0 = 1.
```

The nonzero hypotheses required by `padicValNat.mul` are supplied by the
positive factors in the C002 split.  The corresponding factorization route
uses `Nat.factorization_def` together with `Nat.factorization_mul` (or the
coprime form when appropriate), and is equivalent by the exact bridge in
Q1.

### Global multiplicity form

The existing Mathlib chain is:

```text
ArithmeticFunction.cardFactors_mul
ArithmeticFunction.cardFactors_apply_prime
```

and yields

```text
Ω (ℓ * k) = Ω ℓ + Ω k = 1 + Ω k.
```

Taking `% 2` gives a parity flip, but this is only a finite multiplicity
identity.  No existing DkMath theorem was found that packages this transport
specifically for `SquareBody` or `SquareOffset`.

## 7. Q6 — mapping to current Legendre obstruction classes

The L017 seat partition and the C001/C002 old-generated branch are related but
not identical layers.  The seat trichotomy applies to a covered coprime seat;
the old-generated/fresh dichotomy is the Primitive factor geometry.

| Current class | Prime-power tower interpretation | What parity retains / misses |
|---|---|---|
| `SquareAnchorCoprimeSimpleFreshSeat` | In the L022 fresh split, the selected old prime is the cofactor `k = p`; hence the selected old direction has exponent one, while the fresh `ℓ` direction also has exponent one. | Exact support/depth assumptions identify the class. A residue `v_p % 2 = 1` alone also permits depth `3,5,...` and does not exclude other directions. |
| `SquareAnchorCoprimeSingletonDepthSeat` | One old direction `p` remains and `p^2 ∣ m`, so `v_p(m) ≥ 2`; the exact exponent may be any larger value. | The parity gap separates even from odd depth, but does not reduce `v_p ≥ 2` to a fixed depth or to a prime quotient. |
| `SquareAnchorCoprimeMultiSupportSeat` | At least two distinct old prime directions occur, each with its own finite tower. | A parity vector records terminal residues but does not remove support directions or replace the pair-overlap charge. |
| `old-generated` branch | All relevant factors are generated in the finite old world; there need not be a fresh `ℓ` direction. | Local exponent parity and global `Ω` parity can both be arbitrary. They do not detect the absence of a fresh factor. |

The exact current negative result is therefore:

```text
local parity alone does not force a simple seat;
global Ω parity alone does not force a prime or a simple seat.
```

The existing exact statements remain the stronger classification interfaces:
`coprime_covered_seat_trichotomy`,
`squareAnchorCoprimeOffsets_eq_simpleFresh_union_singletonDepth_union_multi`,
and the L017/L018 ledger inequalities.

## 8. Q7 — actual leverage test for full cover

The current full-cover frontier already has:

- an exact simple/depth/multi-support partition;
- the depth ledger through
  `squareAnchorCoprimePrimeSquareDepthBudget`;
- the pair-overlap ledger through
  `squareAnchorCoprimePrimePairOverlapCount`;
- the localized inequalities
  `two_mul_totient_le_localDepth_add_localPair_of_fullyCovered...`.

The audit found no theorem of the form “full cover forces a prescribed
valuation parity distribution,” and the existing coverage hypothesis does not
make one available for free.  A parity coordinate would retain information
not represented by the current `p^2`-depth indicator, so it is not merely
mathematically empty; however, no new inequality, contradiction, or
exclusion of the old-generated branch follows from it at present.

The justified classification is therefore:

```text
Outcome B — LOSSLESS COORDINATE.
```

This is not Outcome A: no stronger full-cover constraint was found.  It is not
Outcome C: exact exponent slots and parity are not currently exposed by the
same Legendre obstruction reader, so parity could be a useful future
coordinate when a consumer is identified.

## 9. Minimal recommendation for PRIM-PAR-001

Only if a concrete consumer is accepted, the smallest justified future
surface is a thin bridge in the existing valuation-oriented area
(`DkMath.ABC.PadicValNat`), without moving theorem ownership:

```text
pairCount(v) := v / 2
parityGap(v) := v % 2

padicValNat_eq_two_mul_pairCount_add_parityGap
parityGap_lt_two
parityGap_eq_zero_or_one
```

The first theorem is just `Nat.div_add_mod` specialized to
`v = padicValNat p m`; the other two are `Nat.mod_lt` and
`Nat.mod_two_eq_zero_or_one`.  This surface is justified only as a stable
semantic vocabulary for a later tower/packet consumer.  A new explicit depth
`Finset`, a Primitive-specific valuation namespace, and a global `Ω` ledger
should wait for an actual theorem that consumes them.

The existing `padicValNat_le_iff_dvd`, `Nat.factorization_def`, and C002
factor geometry should be reused directly.  No parity theorem needs to be
added to `ValuationFlow.Basic` merely because that module reads valuations.

## 10. Dependencies explicitly not introduced

PRIM-PAR-000 introduces none of the following:

- `DkMath.Units.NPUnit` as a Primitive dependency;
- `PrimitiveBeam`, Zsigmondy, or any claim about primitive-prime origin;
- a new global `Ω` infrastructure or a new factorization abstraction;
- a new explicit finite tower `Finset`;
- changes to `FullExponentSlot` or `FullExponentSlotBridge`;
- changes to PRIM-C001/C002, PRIM-L022, or the Legendre frontier;
- analytic sieve, PNT, Mertens, RH, or CFBRC dependencies;
- a claim that parity solves the classical sieve parity problem;
- a claim that odd `Ω` implies primality;
- a Lean/Mathlib v4.33.0 upgrade.

## 11. v4.32.2 and future-v4.33.0 sensitivity

The current v4.32.2 API has the following practical elaboration points:

- `padicValNat_dvd_iff_le` uses `[Fact p.Prime]`; the DkMath wrapper
  explicitly constructs it with `Fact.mk hp`.
- `padicValNat.mul` requires both multiplicands to be nonzero.
- `Nat.factorization_def` takes an explicit `Nat.Prime p` and has no nonzero
  hypothesis on the natural being factored.
- `Ω` is scoped as `ArithmeticFunction.Omega`; a focused future module should
  import `Mathlib.NumberTheory.ArithmeticFunction.Misc` and open that scope
  only if it actually uses the notation.
- `DkMath.ABC.padicValNat_split` is project-owned and should not be mistaken
  for the Euclidean parity identity.

No v4.33.0 compatibility rewrite or upgrade was attempted.  These observations
are source-level observations against the pinned v4.32.2 environment.

## 12. Verification and stop condition

No Lean theorem file was modified and no temporary scratch file was retained.
The only working-tree change made by this checkpoint is this report.  The
required final check is `git diff --check`; a full Lean build is not required
for this read-only checkpoint.

This reconnaissance stops here.  PRIM-PAR-001 is not started automatically.
