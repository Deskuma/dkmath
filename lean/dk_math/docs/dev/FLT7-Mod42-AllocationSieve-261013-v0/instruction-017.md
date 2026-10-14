# Codex instruction-017 — source-indexed permutation-prime obstruction and first genuine missing bridge

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Previous review: `review-016.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Motivation and change of priority

Gates 006–016 have established exact arithmetic receiver
exclusions, culminating in the centered sextic's generic
permutation-prime image theorem. **Stop adding new prime
moduli or numeric core examples for now.** Return to the
actual source `p : RamifiedSignedRootRoutingPacket`,
its pre-existing inner core, and the distinction between
a logical reconstruction obligation and a constructed
new away-counterexample.

This gate has two tight tasks:
1. Formally attach gate 016's obstruction to the **actual
   source-indexed core**, with every new premise visible.
2. Locate and test the **first unsupplied implication** in
   the source → centered chart direction, using current
   Lean declarations and a precise provenance map.
Do not pretend that a conditional transport supplies
the missing implication.

## Source inventory to check, exact references

Read definitions/proofs in the current checkout:

- `SevenRamifiedFusionNestedReconstruction`:
  `internalDepthFourSeventhCore`, carrier power identity,
  positivity and 7-nondivisibility,
  `internalDepthFourSummand_nested_normal_form`.
- `SevenRamifiedFusionSixthPowerAllocationSieve`:
  `internalDepthFourReconstruction_iff_sixth_power_sieved`
  and exact sieve witness fields.
- `SevenRamifiedFusionDepthFourReconstructionAudit`:
  `internalDepthFourReconstruction_iff_finiteCharts`
  and `internalDepthFourReconstructedRoute_root_ne_innerRoot`.
- `PrimeTraceOneReconstructionFiniteChart`:
  `prescribedCarrierFiniteCharts`,
  `awayCarrierReconstruction_iff_finiteCharts`,
  and explicit required additive certificate.
- `SevenRamifiedFusionRealPairLoadAllocation` and
  `SevenRamifiedFusionLoadedBranchRecovery`:
  true existing source-side load, coprimality,
  associated-power and unit/phase statements.
- `SevenRamifiedFusionPermutationPrimeSupport`:
  the just-proved full exact-sieve exclusion.
- `source-coupling-map-005.md` (outdated only if
  new actual production theorem proves otherwise).

Use source/index search to avoid duplicate declarations
and verify imports before designing a new source facade.

## Part A — a source-indexed, genuinely conditional receiver obstruction

Build a small theorem for the SAME packet `p`,
not for an arbitrary synthetic M. Suggested shape,
adapt the namespace/signatures to the source:

```lean
theorem internalDepthFour_no_reconstruction_of_permutation_prime_core
    (p : RamifiedSignedRootRoutingPacket)
    {c ℓ n : ℕ}
    (hp : Nat.Prime ℓ)
    (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1))
    (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hcore : internalDepthFourSeventhCore p = c * ℓ ^ n) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

Proof must reuse
`internalDepthFourReconstruction_iff_sixth_power_sieved p`
and `sixthPowerSieved_smallCoefficient_permutation_prime_excluded`.
Do not introduce a new reconstruction type or interpret
an arbitrary c,ℓ,n factorization as something already
proved of p.

Then, if the exact imports permit, prove a **source-indexed
necessary constraint** as its contrapositive:

```lean
theorem reconstructed_core_ne_smallCoefficient_permutation_prime_power
    (p : RamifiedSignedRootRoutingPacket)
    (hrec : InternalDepthFourCounterexampleReconstructionObligation p)
    {c ℓ n : ℕ} (hp : Nat.Prime ℓ)
    (hodd : ℓ ≠ 2) (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1))
    (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    internalDepthFourSeventhCore p ≠ c * ℓ ^ n
```

Optional thin `finiteCharts` corollary (check actual theorem
scope): under `hcore` and prime hypotheses,

```lean
¬ (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty
```

by `internalDepthFourReconstruction_iff_finiteCharts p`.
It is a **logical corollary**, not a theorem that such
charts cannot exist for every packet.

Check small concrete specializations ℓ=11,13, c=1,3,13
*under explicit hcore*. No need for huge literal M.
Use 016's general theorem, not duplicate modular proofs.

## Part B — same-packet source→chart bridge audit (research frontier)

The actual missing existence/identification must be
documented without smuggling in what is to be proved.

Track these objects on ONE common packet p:

- `M=internalDepthFourSeventhCore p` as
  `Int.natAbs K.innerSndRoot`, actual `carrier=7^4*M^7`;
- actual `K`, inner coordinates A,B and complementary
  root N with `M*N=V*C` and `Coprime M N`;
- source real-pair core/load data and associated seventh
  powers in the real cubic ring;
- original `quotientRoot` and the possible finite
  additive `(u,v)` chart at carrier, which is
  **not** provided by bare p.

For each proposed arrow, label:
**source theorem with no further premise** /
**theorem requiring reconstruction or a supplied
CounterexamplePack** /
**conditional source theorem requiring additional
seventh-power/gcd assumptions** /
**not established**.

Crucially, verify that
`internalDepthFourSummand_nested_normal_form` needs an
actual additional counterexample pack at the chosen
carrier. Do not use it to construct that pack.
Also verify the old internal inner root cannot
simply be renamed the new away root, because the
valuation depths differ.

Aim for **one new nontrivial Lean statement only if
the source facts really supply it**, e.g. a
phase-safe equality, coprimality constraint, or
prime-support routing link using the same actual p
with no invented endpoint. Keep a precise, minimal
proof; avoid building a large wrapper API that merely
restates arbitrary assumptions.

If no such genuinely new bridge exists, write a
short ```text
source-bridge-frontier-017.md
```
with the first missing formula in both mathematical
words and Lean-proposed type, actual supporting
declarations, and why weaker existing statements
do not discharge it. It may be an Outcome B
**for the bridge subtask**, without downgrading the
correct Part A theorem.

## What is *not* authorized

- NO theorem claiming `p` alone constructs a
  `CounterexamplePack`, `prescribedCarrierFiniteCharts`
  witness or `CenteredNestedAllocationCandidate`
  unless independently proved from real source data.
- NO equality between `quotientRoot`,
  `realPairStrippedCore`/`normalizedAxis`,
  the chosen allocation r/s, and center q
  without a legitimate phase, orientation and
  natural-endpoint argument.
- NO unconditional `¬∃ p : RamifiedSignedRootRoutingPacket, ...`
  based on only the conditional hcore result.
- NO blanket claim `¬ reconstruction p` for all p,
  or unconditional FLT7.
- NO new modular sieve/prime enumeration, large scale
  Mathlib refactor or altered exact predicate.

The existing packet-to-reconstruction equivalences
remain equivalences, **not existential witnesses**.
The old phase ambiguity is a mathematical obstruction
to naïve coordinate decoding, not necessarily a
proof that every invariant natural chart is impossible.

## Acceptance / validation

**Outcome A:** source-indexed conditional obstruction
and reconstructed-core necessary exclusion Lean checked;
plus accurate same-packet source-frontier analysis,
with a genuine additional source bridge if found.

**Outcome B:** safe conditional theorem(s) and a
localized unresolved *constructive* bridge, or a
strictly narrower checked result. This is an
acceptable scientific outcome.

**Outcome C:** a proposed implication is false,
or implementation is blocked; supply precise
countermodel, missing hypothesis or failed
Lean type-check diagnostic.

Run focused build/tests and `#print axioms`
for every new production export. No `sorry`,
`admit`, `sorryAx`, fresh axioms, or unsafe
proof substitutes. Distinguish source code
inspection from a fresh independently run build.

Write `findings-017.md`, `report-017.md`,
compact `evidence/017-verification-summary.md`,
and the optional `source-bridge-frontier-017.md`
if the source audit finds no new bridge.
Keep `logs/` temporary; no bulky log archive.
Stop after gate 017 for review and strategic
reassessment.

**Codex implements, tests and reports ONLY.
Do NOT stage/add/commit/push, create a branch,
open PR or merge.**
