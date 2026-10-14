# Codex instruction-007 — a uniform modular gap in the centered sextic's image

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewer: `review-006.md` (gate 006 Outcome A accepted)
Implementer: GPT-6.1 Sol (light)
Scope: one small proof experiment; **implementation, validation and reports
only**. Stop after this gate. No Git staging, commit, push, branch creation,
PR or merge.

## Goal

Gate 006 proved an exact adjacent-integer-value gap at fixed `M=589`,
which passes the mod-42 cheap filter. We now test a **different**
integer-image obstruction that should apply uniformly to a family,
using the existing centered sextic **modulo 5**.

Do not replace the exact centered polynomial with a generic guessed
cyclotomic identity. Verify its actual definition and reuse the
existing `nestedAllocation_iff_centered` bridge.

## Arithmetic discovery (Python checked; NOT a Lean theorem yet)

Let `D=7^27` and

```text
F(D,q) = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6.
```

An exact finite modulo-5 enumeration yields:

```text
D mod 5 = 3
F(D,q) mod 5 ∈ {1,2,4} for all q
448*s^49 mod 5 = 3*(s mod 5) for all natural s.
```

Therefore if `s ≡ 1 (mod 5)`, the target residue is 3,
which is absent from the entire centered sextic image modulo 5.

These observations are to be **proved in Lean** before any new
exported impossibility theorem is accepted.

## Required theorem scope

Prefer a small general theorem over a long list of fixed numeral
calculations. Suggested API shapes (adapt names to real source):

```lean
theorem centeredSevenSextic_fixedGap_no_image_mod_five
    {s : ℕ} (hs : Nat.ModEq 5 s 1) :
    ¬ ∃ q : ℕ,
      centeredSevenSextic (7 ^ 27) q = 448 * s ^ 49
```

Then establish a clean transport to the exact nested receiver at
**divisor one**:

```lean
theorem nestedAllocation_one_excluded_of_mod_five
    {M : ℕ} (hM5 : Nat.ModEq 5 M 1) :
    ¬ (NestedGNAllocationCondition M 1 ∨
       NestedRHSAllocationCondition M 1)
```

The second proof should use the *actual* centered scalar equation
and normalize `M/1=M`, `64*7=448`. No unjustified endpoint
inversion or hidden source premise.

The absence of a modular image implies absence of a natural
integer image, but does **not** automatically exclude all divisor
allocations `r` for an arbitrary `M`.

## Compare with an unbounded cheap-survivor family

Take `M_k = 631 + 210*k`. Verify, **for every** `k:ℕ`:

- `M_k ≡ 1 (mod 5)` and `M_k ≡ 1 (mod 42)`;
- `ModFortyTwoCheapAllocation M_k 1` by reusing
  `mod42Cheap_family (5*k)`, since
  `631+210*k = 631+42*(5*k)`;
- the separate `SixthPowerAllocationSieve 1 (M_k/1)` via
  the existing `mod42Cheap_family_sixthPower`;
- the **exact** GN/RHS receiver at `r=1` is false, by the
  uniform modulo-five no-image theorem.

A combination theorem, or short Lean applications in the test
module, can make the coexistence unambiguous:

```lean
∀ k : ℕ,
  ModFortyTwoCheapAllocation (631+210*k) 1 ∧
  SixthPowerAllocationSieve 1 ((631+210*k)/1) ∧
  ¬ (NestedGNAllocationCondition (631+210*k) 1 ∨
     NestedRHSAllocationCondition (631+210*k) 1)
```

Do **not** claim
`¬ HasModFortyTwoCheapAllocation (631+210*k)`:
this is false. Do **not** conclude
`¬ SixthPowerSievedNestedCondition (631+210*k)`
for **all** k from `r=1` exclusion alone; larger k can admit
other divisors.

An optional bounded-window corollary could exclude all divisors
when `631+210*k < 343*2^7`, because
`343*r^7<M` then forces `r=1`.
Include only if it adds value with little complexity; it must retain
that explicit bound.

## Independence comparison with gate 006

Check a minimal example that `589` is **not eliminated by this
particular modulo-five image test**:

```text
589 mod 5 = 4
448*589^49 mod 5 = 2
F(7^27,1) mod 5 = 2.
```

The target lies in the modulo-five *image*; gate 006 still proves
integer-image nonexistence by an **adjacent gap**.

This contrast matters: residue-image exclusion and archimedean
integer-image gaps are distinct mechanisms. Do not claim the
mod-five observation implies the 589 result.

## Existing modules to reuse

- `SevenRamifiedFusionCenteredPolynomial`
- `SevenRamifiedFusionCenteredGnomonGap`
- `SevenRamifiedFusionCenteredImage589` (comparison / tests only)
- `SevenRamifiedFusionModFortyTwoCheapBoundaryAudit`
- `SevenRamifiedFusionModFortyTwoCheapAllocation`

Search the theorem index for existing congruence-image results.
Inspect actual Lean API types before selecting proof tactics,
imports or module names.

Do not repeat the broad source-coupling audit from gate 005.
No FLT7 closure theorem is targeted.

## Acceptance, validation and records

Use normal source verification and focused Lean checks suitable to
the executor's environment. For each new export, audit
`#print axioms`. No `sorry`, `admit`, new axioms,
`sorryAx`, or unverified numeric computations presented as proofs.

Write:
- `findings-007.md` — existing-source reuse, exact residue
  computation, valid scope of any new lemma, attempts and limits;
- `report-007.md` — Outcome A/B/C, exact API, test results,
  mathematical comparison with the 589 bracket and next question;
- `evidence/007-verification-summary.md` — only concise material
  proof and axiom evidence, with clear provenance if warranted.

`logs/` is disposable and not committed. No large raw transcripts.
Sol decides local implementation, proof techniques and build details.

**Outcome A:** the uniform mod-five no-image theorem and an
infinite fixed-allocation cheap-but-not-exact family are Lean checked.
**Outcome B:** a correct narrower local-image theorem or justified
reduction with precise missing bridge.
**Outcome C:** false target or rigorous obstruction / incomplete proof
clearly recorded.

**Finish reports and stop without any Git operations.**
