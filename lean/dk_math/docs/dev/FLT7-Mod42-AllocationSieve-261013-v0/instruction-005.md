# Codex instruction-005 — source–allocation–chart compatibility audit

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Basis: `review-004.md` (gate 004 Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Mission

The mod-42 cheap filter and the separate sixth-power sieve admit
unbounded abstract candidates, e.g. `M=631+42*k` at `r=1`.
An abstract candidate need not equal the core of any real
`RamifiedSignedRootRoutingPacket`.

Find the **first genuinely source-coupled constraint**, or pinpoint the
smallest missing bridge, among:

1. the *actual* ramified/normalized outer and inner carrier and its
   seventh-root core `M = internalDepthFourSeventhCore p`;
2. the *actual same packet* complementary-root/product/prime-support
   ledger;
3. the allocation divisor `r ∣ M`, its complementary factor
   `s=M/r`, and the GN/RHS or centered chart coordinates.

Do not treat a congruence sieve as a proof of an exact endpoint equation;
do not turn a conditional receiver equivalence into an inhabited receiver.

This is a **bounded source audit with optional small Lean formalization**,
not a request to solve FLT7. Explore current hypotheses afresh and
do not assume the desired bridge exists.

## Required existing-source inspection

Use the local theorem index and inspect actual declarations, hypotheses
and import provenance (not just similarly named theorems). At minimum:

- `SevenRamifiedFusionNestedReconstruction.lean`:
  `internalDepthFourSeventhCore`, positivity and seven-unit,
  actual carrier identity;
- `SevenRamifiedFusionSixthPowerAllocationSieve.lean`:
  `internalDepthFourAllocation_prime_support`,
  `internalDepthFourReconstruction_iff_sixth_power_sieved`,
  complementary-root identity;
- `SevenRamifiedFusionCenteredPolynomial.lean`:
  `CenteredNestedAllocationCandidate`,
  `internalDepthFourReconstruction_iff_centered`;
- `SevenRamifiedFusionCenteredGnomonGap.lean`:
  exact proven perfect-sixth obstruction and its hypothesis;
- `SevenRamifiedFusionRealPairLoadAllocation.lean` and
  `SevenRamifiedFusionRealPairCoprimalityNormGate.lean`:
  source packet's real-pair/axis load and root ownership;
- selected `GTail*` bridge modules only if they preserve the **same
  source coordinates** and have a genuinely relevant proven invariant.

You may examine other parts of DkMath if they supply a better bridge,
but do not duplicate existing seven-power, GTail, norm, allocation or
reconstruction APIs.

## Concrete audit questions (answer all)

**Q1 — Source data.** For a fixed `p`, list exactly what is already
kernel-proved about `M`, carrier, `N`,
`verticalGapRoot`, `compensationRoot`, prime support and relevant
root coordinates. Give full theorem identifiers and their precise
hypotheses. Identify which conclusions involve an *actual packet*,
and which are generic `M` statements.

**Q2 — Divisor-one blind spot.** The existing
`internalDepthFourAllocation_prime_support` requires
`Nat.Prime q` and `q ∣ r`.
For `r=1` there is no such `q`.
Determine whether another **proven source theorem** nonetheless
forbids `r=1` under the exact reconstruction assumptions.
If not, record the absence honestly. Do not assert that `r=1`
is realizable; its abstract cheap survival is not enough.

**Q3 — Actual chart linkage.** Is there a theorem connecting the
*same actual source packet's* norm/real-pair/prime support data to
the **chosen** `r,s` and to the centered coordinate `q`
or reconstructed endpoint `u` with a new restrictive conclusion?
Trace both directions and write the first exact missing theorem
statement (in a Markdown Lean code block if not yet proved).
Beware root phases and coordinate ambiguity; equality of norms or
ideals is not equality of oriented integer endpoint data.

**Q4 — Does the bridge do new work?** Distinguish a truly
independent source constraint from:

- mere repackaging of `M*N=V*C` with no restriction on `r,q,u`;
- a necessary condition already entailed by the same exact endpoint
  equation;
- the known `..._iff_sixth_power_sieved` /
  `..._iff_centered` equivalences;
- conditional "if all divisors have property X, then no receiver"
  where X is not established for the actual source.

As a diagnostic, the *bare abstract* product ledger
`M*N=V*C`, `Nat.Coprime M N`, `N>0`, `¬7 ∣ N`
is compatible with arbitrary `M` by choosing
`N=1, V=M, C=1`. This does **not** produce actual quadratic
roots with all packet constraints. Use this observation only to
assess the information content of a proposed generic bridge.

## Optional implementation (only if genuinely new)

If the source audit identifies a concise, nontrivial, independent
same-packet relation, implement **one small theorem** and a focused
test/audit under the existing Seven module family. Retain every
necessary source, orientation, coprimality and chart hypothesis.

If there is no demonstrable new bridge, **do not manufacture a Lean
wrapper** or weaken the success criterion. A precise failure boundary
and smallest missing statement are accepted research outcomes.

A tiny standalone Lean negative-model lemma is acceptable if it
genuinely proves why a specific *abstract subset of premises* does
not imply the claimed restriction. Label its scope carefully.

## Mandatory durable records

Write:

- `source-coupling-map-005.md` with a concise provenance table:
  source object, exact theorem, conclusion, hypotheses, attached
  packet/branch, whether it constrains `r=1`, missing arrow;
- `findings-005.md` with attempts, successful existing links,
  failed or unproven bridges, and the **next single research question**;
- `report-005.md` with Outcome A/B/C, exact proven changes (if any),
  honest gap diagnosis, and recommended next step;
- `evidence/005-verification-summary.md` only for compact relevant
  verification when formal code changes were actually made.

If implementation is performed, validate Lean focused imports/tests,
and audit any exported theorem with `#print axioms`; reject
`sorryAx` or fresh axioms. If no Lean code is added, state this
clearly; do not advertise an audit as a newly kernel-proved result.

`logs/` stays temporary, and no bulk output belongs to `evidence/`.
Build tools and computing resources are chosen by the local executor.

## Outcomes and stop condition

- **A:** a genuinely new, checked source-coupled restriction on the
  chosen allocation or chart beyond current cheap/exact restatements;
- **B:** a precise reuse map narrowing the missing theorem, with a
  checked partial bridge if justified;
- **C:** a demonstrated obstruction/insufficiency of candidate
  premises, a corrected false conjecture, or a well-localized
  unresolved frontier.

All three are legitimate; do not chase A by adding an invented premise.

Codex only investigates, implements (if warranted), tests and reports.
**No Git staging, commit, push, branch creation, PR or merge.**
Stop after gate 005 and hand results back for review.
