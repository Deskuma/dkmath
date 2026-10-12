# Review 002 — Accepted / Outcome A

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed revision: `113595ed721ee739212fb27fdb6b19b642914a5a`

## Decision

**ACCEPTED (Outcome A).** All three prescribed public declarations exist with their intended types:

- `nestedAllocation_mod_six` with `r ∣ M`;
- `nestedAllocation_mod_fortyTwo` with `r ∣ M`;
- `nestedAllocation_excluded_of_mod_fortyTwo` with `r ∣ M`.

Source review confirms that the GN branch transports coprimality using the divisor guard and the RHS branch uses the existing subtraction lemma. The proof derives `s^49 ≡ s (mod 6)` for all natural `s`, combines existing mod-7 with mod-6 using a Mathlib congruence lemma, and does not redefine the exact receiver predicates.

The test module records a counterexample to **unguarded coprimality transport**, not a counterexample to the entire unguarded receiver; it also demonstrates that passing the congruence is not sufficient for a receiver witness.

The implementer's focused build and test have exit status 0, with `#print axioms` listing only `[propext, Classical.choice, Quot.sound]` for each export. This review checked source, tests, report and compact evidence; **the reviewer did not independently rerun the Lean build**.

## Important mathematical boundary

`SixthPowerSievedNestedCondition M` already contains an **exact endpoint residual equation** in either branch. Therefore conjoining mod 42 with that predicate and showing equivalence is formally valid but mathematically only a repackaging: the new congruence already follows from the exact branch. It must not be advertised as progress toward proving nonexistence of all receivers.

The useful next question is whether a **pre-endpoint, independently stated arithmetic filter** can reject allocations before testing the expensive exact endpoint equations, and whether this actually excludes candidates surviving earlier cheap tests.

One concrete candidate is `r=1, M=554`: it satisfies `s=554 ≡ 1 (mod 7)`, `7^3 < 554`, and the RHS necessary size band `554^49 < 7^161 ≤ 64·554^49`, while `554 ≢ 1 (mod 42)`. The sixth-power filter modulo `r^49=1` is vacuous. These arithmetic comparisons were checked using Python integer arithmetic; they are **not yet a Lean evidence artifact**.

## Roles and source control

- **Codex:** implementation, local testing, source inspection, findings, reports and compact evidence only.
- **Wise Wolf (ChatGPT):** review and publishing the approved research instructions / review notes by committing and pushing them to this GitHub research branch.
- **User:** retains control of approval, integration/merging and the overall repository policy.
- No `git add`, `git commit`, `git push`, PR creation or merging is to be instructed to Codex.
- `logs/` is disposable; only compact provenance-labeled `evidence/` is retained.

## Authorization

Proceed to the **bounded pre-endpoint filter / discrimination audit** in `instruction-003.md`. Do not implement a new global theorem claiming an empty receiver, unconditional FLT7, or strict descent.
