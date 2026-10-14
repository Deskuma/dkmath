# Review 006 — Outcome A accepted; exact integer-image obstruction verified

Date: 2026-10-13
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `d7be8e796913245f4415220c3c2307f731af2a9d`

## Verdict

**ACCEPTED — Outcome A.** Reviewed the published production Lean source,
test file, `report-006.md`, `findings-006.md`, and
`evidence/006-verification-summary.md`.

The five new exported theorems are:

1. `centeredSevenSextic_589_bracket` — exact two-sided adjacent bracket;
2. `centeredSevenSextic_589_no_image` — no natural center reaches target;
3. `nestedAllocation_589_one_excluded` — exact GN and RHS branches
   are both false at `(M,r)=(589,1)`;
4. `sixthPowerSievedNestedCondition_589_excluded` — **all eligible
   divisors** at fixed `M=589` are ruled out (the size guard forces
   `r=1`);
5. `no_reconstruction_of_core_eq_589` — conditional impossibility of
   source reconstruction if an actual packet has core 589.

The bracket's exact natural-number inequalities are checked by
`decide` from the actual `centeredSevenSextic` definition; the
no-image result reuses existing
`centeredSevenSextic_no_image_of_adjacent_bracket`, whose argument
uses strict monotonicity over **all** natural centers.
`nestedAllocation_iff_centered` then gives genuine exact endpoint
exclusion; the all-divisor theorem follows from `343*r^7<589`
forcing `r=1`. No literal perfect-sixth hypothesis was introduced.

The implementer's focused Lake build/test exited successfully.
`#print axioms` lists only `[propext]` for the bracket and
`[propext, Classical.choice, Quot.sound]` for the other exports;
no `sorryAx` was reported. The reviewer inspected source and compact
evidence but **did not independently run Lean**.

The test also validates both
`HasModFortyTwoCheapAllocation 589` and
`¬ SixthPowerSievedNestedCondition 589`. Their conjunction is
**not** contradictory: the first is an endpoint-free necessary
screening predicate, the second excludes the exact receiver.

## New exploratory angle: finite-field *image* versus adjacent-image gap

The integer image can fail for different mathematical reasons.
The 589 target requires a genuine adjacent integer-value certificate.
A distinct obstruction exists for **another subfamily** of cheap
survivors, detected by the image of the *actual same centered sextic*
modulo 5. A local, independent Python exact-integer enumeration found:

- `D=7^27 ≡ 3 (mod 5)`;
- `{ centeredSevenSextic(D,q) mod 5 | q=0,1,2,3,4 } = {1,2,4}`;
- `448*s^49 ≡ 3*s (mod 5)` for every natural `s`;
- if `s≡1 (mod 5)`, target is 3 modulo 5, **not in the image**.

These are **arithmetic observations, not yet kernel-checked theorems**.
They can be tested independently from the adjacent bracket.

In particular `M_k=631+210*k` satisfies `M_k≡1 (mod 42)`,
`M_k≡1 (mod 5)`, `M_k>343`, and
`7^161 < M_k^49`. Thus the existing
`mod42Cheap_family (5*k)` proves `ModFortyTwoCheapAllocation M_k 1`,
while the proposed mod-5 image argument would exclude **that same
fixed allocation's exact centered image** for every `k`.

**Scope caution:** for arbitrarily large `M_k`, other eligible divisors
may exist. Excluding `r=1` alone does **not** show
`¬ SixthPowerSievedNestedCondition M_k`. Also, no actual
`RamifiedSignedRootRoutingPacket` is constructed by the cheap
family, and neither the mod-5 test nor one adjacent bracket proves FLT7.

Another instructive contrast: `589≡4 (mod 5)`, and its target residue
is `2`, **inside** the sextic's mod-5 image. Thus this specific
mod-5 test does not subsume the gate-006 adjacent bracket.

This is a productive comparison of **local residue image gaps** and
**integer adjacent-value gaps**. It should not become an unconstrained
hunt for arbitrary residue moduli or a false global generalization.

## Roles / gate 007

Codex only implements, verifies and reports; it must **not**
stage/commit/push, create branches, PRs or merge. Wise Wolf publishes
reviewed documents and instructions to the research branch; user
retains overall integration decisions.

Gate 007: formalize the **uniform modulo-five no-image obstruction**
and its fixed-divisor infinite cheap-survivor comparison. Reuse the
existing centered equivalence and prior cheap-family theorem; make a
bounded, honest report. No general reconstruction closure is authorized.
