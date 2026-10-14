# Review 003 — Outcome A accepted / gate 004 authorized

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `c32d844e59bd7700c53139a4c45b6f00ca59cc34`

## Assessment

**ACCEPTED (Outcome A).** Production module
`DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`
implements two endpoint-independent definitions and two thin implications:

- `ModFortyTwoCheapAllocation M r`: only divisor membership, coprimality,
  size threshold, modulo 42, and disjunctive branch threshold/band.
- `HasModFortyTwoCheapAllocation M`: existential over divisors.
- `sixthPowerSieved_implies_mod42Cheap`: exact receiver conditions
  imply the necessary cheap arithmetic predicate.
- `internalDepthFourReconstruction_implies_mod42Cheap`: the actual
  reconstruction obligation implies the same necessary predicate
  at the source's internal-depth-four core.

Source inspection confirms that neither endpoint `u` nor the exact
GN/alternating residual equations occur in the new predicate definitions.
The proof transports a witness from an existing exact predicate and
uses the previously checked modulo-42 theorem; it neither creates
an exact receiver witness nor proves reconstruction empty.

The named Lean examples verify that `(554,1)` passes the old cheap
numeric guards and modulus-one sixth-power condition, but is rejected
by the new mod-42 filter. `(589,1)` passes the new filter.
**These are fixed allocations; `(554,1)` rejection alone does
not prove `¬ HasModFortyTwoCheapAllocation 554`.**

The implementer's report and compact evidence record focused build
and test exit code 0, with only
`[propext, Classical.choice, Quot.sound]` in the axiom audits for the
production theorems and named tests. The reviewer inspected GitHub source,
test, report and evidence; **no independent Lean rerun** was performed.

## New mathematical audit proposal

The filtering effect has two important boundaries, now suitable for
formal demonstration:

1. **Global arithmetic rejection at a concrete M.** For `M=554`,
   the coarse lower bound `7^3*r^7 < M` and divisor membership
   force `r=1` (all `r≥2` give `343*128 > 554`).
   As `554 ≢ 1 (mod 42)`, it follows mathematically that
   `¬ HasModFortyTwoCheapAllocation 554`.
   This is stronger than the gate-003 fixed-divisor exclusion.
2. **Infinite surviving cheap candidates.** For all `k:ℕ`,
   `M=631+42*k` and `r=1` satisfy the arithmetic filter:
   `M≡1 (mod 42)`, `343 < M`,
   `7^161 < 631^49 ≤ M^49`. Also
   `SixthPowerAllocationSieve 1 M` holds from the existing
   modulus-one lemma. The strict comparison
   `7^161 < 631^49` was independently verified by exact
   Python integer arithmetic; it still requires a Lean proof.

Thus the new necessary-only filter excludes some arithmetic cores
but allows infinitely many others. No claim is made that these cores
occur as `internalDepthFourSeventhCore p` for any packet `p`,
or that they satisfy the exact endpoint equations.

## Source-control and evidence responsibilities

- Codex: code, tests, findings, reports and compact evidence only;
  **no staging, commits, pushes, branches, PRs or merges**.
- Wise Wolf: review and publication of review/instruction documents.
- User: integration/merge authorization and overall repository decisions.
- `logs/` disposable; `evidence/` compact with provenance.

## Decision

Proceed with `instruction-004.md`: formally calibrate the global
rejection and infinite-survival boundary, compare these findings with
the existing exact reconstruction obligation, and stop for review.
Do not add an arbitrary chain of stronger residue moduli merely to
make candidate counts smaller.
