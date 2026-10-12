# ROADMAP — FLT7 Mod-42 Allocation Sieve

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Base: `develop` (first prepared 2026-10-13).
Current status: **Gate 001 ACCEPTED (Outcome A); gate 002 AUTHORIZED / implementation pending**. See `review-001.md`.

## Goals and gates

| Gate | Scope | Exit evidence | Status |
| --- | --- | --- | --- |
| 000 | Read live existing receiver APIs; theorem-index duplicate check | Actual declarations and required hypotheses recorded | Source audit done; Codex to reconfirm |
| 001 | Primitive seventh-order residues modulo 6 | Two focused, kernel-checked lemmas for GN7 and alternating cyclotomic factor; audit | **ACCEPTED — Outcome A** |
| 002 | Divisor-aware allocation bridge to mod 42 | Both exact branches -> `M/r ≡ 1 (mod 42)`, plus exclusion lemma | **AUTHORIZED — instruction-002.md** |
| 003 | Optional sieve façade and reconstruction integration | Exact conditions preserved; equivalence proof checked | REVIEW GATE |
| 004 | Math audit, test expansion, reports and PR review | No accidental FLT7 closure claim; audit and replayable logs | PENDING |

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

## Gate 002 — authorized via instruction-002.md

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

## Gate 003 — optional, requires review decision

Consider `ModFortyTwoSievedNestedCondition` and a checked equivalence
with the existing exact `SixthPowerSievedNestedCondition`. Such an equivalence
must preserve both endpoint equations, branch thresholds, coprimality and
all guard conditions; its purpose is API filtering, not new existence.

Do not introduce the sieve wrapper at all if it adds no consumer value.

## Explicit non-goals

- No unconditional FLT7 proof or strict descent claim.
- No new inhabited `InternalDepthFourCounterexampleReconstructionObligation`.
- No diagonal arguments based solely on smaller 7-adic carrier depth.
- No redo of GTailSelection, GTailFactor, GTailTransport, GTailSeven.
- No changing existing production file proofs to conform to a new aesthetic.
- No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` as a proof
  substitute, or untracked assumptions.
- No huge `lake build` across the entire repo for a focused lemma.

## Negative-evidence rule

A sieve can exclude local allocation candidates without showing global
impossibility. Record the surviving cases as clearly as exclusions.
In particular, for `r=1` the modulus `r^49=1` makes the existing
`SixthPowerAllocationSieve` vacuous; the new mod-42 condition is a
different necessary filter. The Python slice (`r=1, s=589`) cannot be
promoted to all `M,r`.

## Records and logs policy

`logs/` is temporary and ignored by Git; do not commit bulk output. Store only compact, decisive, provenance-marked artifacts in `evidence/` (see `evidence/README.md`), and summarize command outcomes in the gate report. Tool/resource choices are left to the executing Codex environment.

## Deliverables per cycle

Create `findings-001.md` early, update it before any significant proof
branch change, then `report-001.md` at the stable stopping point.
Report status as:

- Outcome A: goal fully kernel-checked with correct premises.
- Outcome B: a strictly narrower correct lemma that advances the gate.
- Outcome C: blocked or falsified; give the exact counterexample / missing
  premise / compiler error, do not insert false hypotheses.

Include an inventory of touched files, commands, output, axiom list, and
one proposed next step. Stop after the gate.
