# Codex instruction-002 — divisor-aware mod-42 allocation filter

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Implementer: GPT-6.1 Sol (light)
Authorization: `review-001.md`, after accepted instruction-001.
**Only this gate. Stop for review before gate 003.**

## Mathematical goal

Transport the TWO EXISTING general mod-6 theorems from
`SevenRamifiedFusionModSixResidues.lean` to the TWO
existing nested FLT7 allocation receivers, then combine with the
EXISTING mod-7 sieve. No novel FLT7 existence or descent theorem.

Let `D = 7^27 * r^49` and `s = M / r`.

The exact receiver predicates are:

- `NestedGNAllocationCondition M r`:
  some `u>0` with `Nat.Coprime u (7*M)` and
  `GN 7 D u = 7*s^49`.
- `NestedRHSAllocationCondition M r`:
  some `0<u<D` with `Nat.Coprime u D` and
  `alternatingCyclotomicSeven u (D-u) = 7*s^49`.

Target API **shape** (names can follow current repository conventions):

```lean
theorem nestedAllocation_mod_six {M r : ℕ}
    (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨
         NestedRHSAllocationCondition M r) :
    Nat.ModEq 6 (M / r) 1

theorem nestedAllocation_mod_fortyTwo {M r : ℕ}
    (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨
         NestedRHSAllocationCondition M r) :
    Nat.ModEq 42 (M / r) 1

theorem nestedAllocation_excluded_of_mod_fortyTwo {M r : ℕ}
    (hdiv : r ∣ M)
    (hbad : ¬ Nat.ModEq 42 (M / r) 1) :
    ¬ (NestedGNAllocationCondition M r ∨
       NestedRHSAllocationCondition M r)
```

If a shorter, weaker helper proof is needed, introduce it locally.
Do not alter the original receiver definitions or weaken the guard.
Positivity hypotheses may be added when mathematically required;
explain any such addition in `findings-002.md`.

## Proof facts to establish / reuse

1. **Power reduction modulo 6.**
   `s^49 ≡ s (mod 6)` for ALL `s : ℕ`.
   Find an existing general lemma or prove one small helper.
   Do not treat a Python sample as a general proof.

2. **GN branch: full divisor provenance is essential.**
   The receiver `Nat.Coprime u (7*M)` alone does NOT make
   `D=7^27*r^49` coprime to `u`. The hypothesis
   `r ∣ M` provides that missing transport. Prove
   `Nat.Coprime D u` via existing Nat.Coprime and divisibility
   APIs, then invoke `GN_seven_mod_six_of_coprime`.

   Counterexample to the *unguarded transport*, not to the
   receiver's full equation: `M=1, r=2, u=2` has
   `Nat.Coprime u (7*M)` but `¬ Nat.Coprime r u`.
   Keep this distinction clear.

3. **RHS branch: endpoint transport.**
   From `0<u<D` and `Nat.Coprime u D`, show
   `Nat.Coprime u (D-u)`. Invoke
   `alternatingCyclotomicSeven_mod_six_of_coprime`.
   Use the actual natural subtraction and the existing
   coprime subtraction lemmas.

4. **Recover s modulo 6.**
   Both exact residuals are `7*s^49`, and their
   primitive mod-6 residues are 1. Since `7≡1 (mod 6)`
   and `s^49≡s (mod 6)`, derive `s≡1 (mod 6)`.

5. **Combine with existing mod 7.**
   Reuse `nestedAllocation_residue_sieve`, which gives
   `s≡1 (mod 7)`, and combine coprime moduli 6 and 7
   to obtain `s≡1 (mod 42)`.

6. **Exclusion consumer.**
   A failure of the *necessary* mod-42 condition excludes
   both exact allocation branches at this **divisor-aware**
   allocation, with the guard visible in the statement.

## Existing assets to inspect and reuse

- `DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues` (gate 001).
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve`:
  `nestedAllocation_residue_sieve` and mod-7 helpers.
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold`:
  exact receiver predicates.
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`:
  existing conditional mod-3 filter; do not reimplement it.
- `Mathlib`: `Nat.Coprime`, modular powers and CRT or ModEq
  composition.

Search declarations locally and verify actual types before choosing
imports. Reuse all validated results; do not recreate a theorem
merely because it is in another module.

Suggested single new production module:

```text
DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean
```

Keep a focused test/audit module under `DkMathTest/FLT/Seven/`.
Do not create a global reworked sieve predicate in gate 002.
Do not edit existing FLT7 proof modules unless a genuine
dependency requires a narrowly documented change.

## Validation and proof boundary

Perform an appropriate focused Lean build and test using the execution
environment you actually have; tool invocations and resource choices
are for the local Codex to decide. Record commands + exit codes.

For every exported theorem, inspect actual `#print axioms` output.
Reject `sorryAx`, `sorry`, `admit`, fresh axioms, or hidden
conditions. Include at least:

- proof-level use of each exported theorem,
- a test showing that dropping `r ∣ M` from the coprimality
  *transport* is unjustified,
- explicit awareness that the mod-42 congruence is not sufficient
  to produce an allocation witness,
- any finite examples useful to check the CRT/power helper.

## Records: evidence vs disposable logs

- Start `findings-002.md` before significant proof attempts;
  update it when assumptions, approach, or validation change.
- Make `report-002.md` with outcome A/B/C, exact theorem API,
  source reuse, algebraic reasoning, test/build results,
  axiom audits, known limitations, and proposed gate 003.
- Raw output goes to disposable `logs/` if useful locally.
  It is Git-ignored and **must not be committed**.
- Only compact and decisive proof/audit artifacts belong in
  `evidence/`, with provenance (Codex-reported or independently
  checked). No giant build transcripts or large generated traces.

## Explicit limits

This is a necessary residue sieve, not a theorem stating that
`NestedGNAllocationCondition` / `NestedRHSAllocationCondition`
is always false. Do not claim unconditional FLT7, inhabited
reconstruction, or a smaller positive counterexample.
Do not claim the sieve proves more than it does. No broad
refactoring, no speculative extensions, no gate 003 without
reviewer authorization.

**Finish the gate, commit its narrow artifacts, report, and stop.**
