# ROADMAP — FLT7 Mod-42 Allocation Sieve

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Base: `develop` (first prepared 2026-10-13).
Current status: **Gates 001–004 ACCEPTED (Outcome A); gate 005 ACCEPTED (Outcome B); gate 006 AUTHORIZED / proof pending**. See `review-001.md` through `review-005.md`.

## Goals and gates

| Gate | Scope | Exit evidence | Status |
| --- | --- | --- | --- |
| 000 | Read live existing receiver APIs; theorem-index duplicate check | Actual declarations and required hypotheses recorded | Source audit done; Codex to reconfirm |
| 001 | Primitive seventh-order residues modulo 6 | Two focused, kernel-checked lemmas for GN7 and alternating cyclotomic factor; audit | **ACCEPTED — Outcome A** |
| 002 | Divisor-aware allocation bridge to mod 42 | Both exact branches -> `M/r ≡ 1 (mod 42)`, plus exclusion lemma | **ACCEPTED — Outcome A** |
| 003 | Independent pre-endpoint arithmetic filter and discrimination audit | Necessary-only candidate filter, exact-to-cheap implication, strict screening example | **ACCEPTED — Outcome A** |
| 004 | Necessity-boundary audit | Globally exclude cheap core 554; prove an infinite cheap-survivor family; preserve exact-vs-cheap distinction | **ACCEPTED — Outcome A** |
| 005 | Same-packet source–allocation–chart audit | Inspect real carrier/norm ledger, divisor-one blind spot, missing chart bridge; optional genuinely new theorem | **ACCEPTED — Outcome B** |
| 006 | Centered integer-image bracket at M=589 | Verify strict adjacent-value bracket, exclude exact centered receiver, and if possible all eligible divisor allocations | **AUTHORIZED — instruction-006.md** |

After each gate, pause for human/Wise Wolf review before issuing the next
implementation instruction. Do not autonomously expand 001 into 003.

## Gate 001 — completed; approved in review-001.md

1. Search all relevant declarations in current `develop`-derived branch.
2. Establish the two bare arithmetic facts with correct coprimality:
   `Nat.Coprime D u -> GN 7 D u ≡ 1 (mod 6)`,
   `Nat.Coprime x y -> alternatingCyclotomicSeven x y ≡ 1 (mod 6)`.
3. Write them in one new production Lean file, with a minimal import.
4. Add focused Lean checks/tests and `#print axioms`.
5. Record exactly what was proved, which imports were used, build commands,
   error/failure attempts, and all remaining conditions.
6. Stop and hand the report back for review.

No new global FLT7 theorems in gate 001. **Implemented and reviewed**, see `report-001.md` and `evidence/001-verification-summary.md`.

## Gate 002 — implemented and accepted; review-002.md

Focused build, test applications and three axiom audits passed; see `report-002.md` and `evidence/002-verification-summary.md`. Gate 003 authorized by review-002.md; implementation not yet started.

Re-use gate-001 and existing `nestedAllocation_residue_sieve`:

- For the GN branch prove `Nat.Coprime D u` using the exact receiver's
  `Nat.Coprime u (7*M)` **and** the separate `r ∣ M`.
- For the RHS branch use `Nat.Coprime u D` and
  `Nat.Coprime u (D-u)` from its interval bound.
- From `7*s^49 ≡ 1 (mod 6)` derive `s ≡ 1 (mod 6)`,
  using `s^49 ≡ s (mod 6)`.
- Combine `s ≡ 1 (mod 6)` and `s ≡ 1 (mod 7)` into mod 42.
- Add an exclusion lemma from failure of this necessary congruence,
  retaining its divisor hypothesis.

The new theorem must **not** remove a receiver's divisibility guard simply
because an adjacent existing lemma does not need that guard modulo 7.

## Gate 003 — completed and accepted (review-003.md)

Construct a pre-endpoint arithmetic filter independent of the exact receiver predicates. Prove a correct exact-to-cheap implication and check its screening power relative to previous necessary-only guards. Do not merely append mod 42 to a predicate already containing exact endpoint equations. Do not assert that a necessary congruence is sufficient or that all receivers are empty.

Codex only implements, validates, and reports; **no commit, push, PR, or merge instructions to Codex**. Wise Wolf publishes reviewed instruction/review documents. The user makes repository integration decisions.

## Gate 004 — completed and accepted (review-004.md)

Audit the global reach and the limitations of the necessary-only arithmetic filter: show a concrete core excluded for *all* divisor allocations, and exhibit an unbounded family that passes the cheap conditions without asserting any endpoint witness. These are structural boundary certificates, not FLT7 closure. Then stop for review and identify whether a source-coupled invariant is the next target.

## Gate 005 — completed and accepted (Outcome B; review-005.md)

Locate the first source-specific condition linking the actual internal carrier and norm ledger to the **same selected allocation** and centered chart. Distinguish known source results from a new restrictive bridge. Explicitly inspect the divisor-one blind spot in the prime-support route. A documented negative result and exact missing theorem are valid outcomes; do not merely repackage existing exact receiver equivalences or add arbitrary modular filters. Codex handles implementation/audit and reporting only, with no Git operations.

## Gate 006 — authorized via instruction-006.md

An independent Python arbitrary-precision check found the centered target for M=589 and r=1 strictly between consecutive integer polynomial values. Formalize that strict bracket in Lean using the already-proved monotone-image exclusion. Then, if the proof succeeds, transport to exact receiver nonexistence at this **single core**, including the full divisor-allocation sieve via the coarse size guard. Do not infer no cheap allocation at 589 (it does pass the cheap filter), arbitrary-core emptiness, or unconditional FLT7. This is a fresh exact-image route, not a forced perfect-sixth conjecture or a repeat of the same-packet audit.

## Explicit non-goals

- No unconditional FLT7 proof or strict descent claim.
- No new inhabited `InternalDepthFourCounterexampleReconstructionObligation`.
- No diagonal arguments based solely on smaller 7-adic carrier depth.
- No redo of GTailSelection, GTailFactor, GTailTransport, GTailSeven.
- No changing existing production file proofs to conform to a new aesthetic.
- No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` as a proof
  substitute, or untracked assumptions.
- Build strategy is for the local implementing agent to decide; no hardware-dependent restrictions in instructions.

## Negative-evidence rule

A sieve can exclude local allocation candidates without showing global
impossibility. Record the surviving cases as clearly as exclusions.
In particular, for `r=1` the modulus `r^49=1` makes the existing
`SixthPowerAllocationSieve` vacuous; the new mod-42 condition is a
different necessary filter. The Python slice (`r=1, s=589`) cannot be
promoted to all `M,r`.

## Source control roles

Codex is not responsible for Git staging, publication, commits, pushes, branch creation, PRs, or merges. Review and instructions are published to the research branch by Wise Wolf (ChatGPT); integration decisions remain with the user.

## Records and logs policy

`logs/` is temporary and ignored by Git; do not commit bulk output. Store only compact, decisive, provenance-marked artifacts in `evidence/` (see `evidence/README.md`), and summarize command outcomes in the gate report. Tool/resource choices are left to the executing Codex environment.

## Deliverables per cycle

For gate N, create and update `findings-NNN.md` early, and write
`report-NNN.md` at the stable stopping point. Gate 005 additionally
requires `source-coupling-map-005.md`. Existing reports remain authoritative
for earlier gates.
Report status as:

- Outcome A: goal fully kernel-checked with correct premises.
- Outcome B: a strictly narrower correct lemma that advances the gate.
- Outcome C: blocked or falsified; give the exact counterexample / missing
  premise / compiler error, do not insert false hypotheses.

Include an inventory of touched files, commands, output, axiom list, and
one proposed next step. Stop after the gate.
