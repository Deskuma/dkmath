# Codex instruction-001 — primitive seventh residues modulo 6

**Target branch:** `research/FLT7-Mod42-AllocationSieve-261013-v0`  
**Implementer:** GPT-6.1 Sol (light)  
**Scope:** one tiny production module + focused tests / audit / report.  
**Stop after this instruction.** Do not run ROADMAP gate 002 without review.

## 0. Establish the current source before editing

From repository root:

```bash
git status --short --branch
git branch --show-current
cd lean/dk_math

# Check current theorem inventory; the SQLite file is intentionally ignored.
python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .
python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search --name nestedAllocation_residue_sieve --full
python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 search --name alternatingCyclotomicSeven --limit 40
rg -n 'mod_six|mod_six|mod_42|mod42|Nat.ModEq 6|alternatingCyclotomicSeven' DkMath/FLT/Seven DkMath/Lib
```

Verify symbols in the actual source and record results in
`docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-001.md`.
If an equivalent general theorem is already in production, **use it**,
do not reimplement it; a successful reuse audit is an acceptable outcome.

Read at minimum:

- `DkMath/FLT/Seven/SevenRamifiedFusionSymmetricReconstruction.lean`
  (definition / exact alternating residual);
- `DkMath/FLT/Seven/SevenRamifiedFusionAllocationThreshold.lean`
  (`NestedGNAllocationCondition` and `NestedRHSAllocationCondition`);
- `DkMath/FLT/Seven/SevenRamifiedFusionAllocationResidueSieve.lean`
  (`nestedAllocation_residue_sieve`);
- `DkMath/FLT/Seven/SevenRamifiedFusionSixthPowerAllocationSieve.lean`;
- the existing canonical `GN` definitions and seventh-degree lemmas.

## 1. Target exactly two arithmetic lemmas

Create the smallest suitable Lean module, suggested path:

```text
DkMath/FLT/Seven/SevenRamifiedFusionModSixResidues.lean
```

Its exported API should have these shapes (rename only if the existing
codebase has a genuinely better convention):

```lean
namespace DkMath.FLT.Seven
open DkMath.CosmicFormulaBinom

theorem alternatingCyclotomicSeven_mod_six_of_coprime
    {x y : ℕ} (hxy : Nat.Coprime x y) :
    Nat.ModEq 6 (alternatingCyclotomicSeven x y) 1 := by
  -- genuine proof

theorem GN_seven_mod_six_of_coprime
    {D u : ℕ} (hDu : Nat.Coprime D u) :
    Nat.ModEq 6 (GN 7 D u) 1 := by
  -- genuine proof

end DkMath.FLT.Seven
```

**These statements are conjectured implementation targets, not existing
kernel-checked results.** First inspect imported definitions/types.

Arithmetic hint: with coprime endpoints,
`S7(x,y) = Σ x^(6-j)*y^j` and
`A7(x,y) = Σ (-1)^j*x^(6-j)*y^j` both have residue 1 modulo 6.
One can prove modulo 2 and modulo 3 separately, where the possible
primitive residue classes are finite, and reassemble modulo 6.
A direct exhaustive `ZMod 6` proof is also acceptable if it is clean
and fast. Reuse existing polynomial/cyclotomic identities first.

For GN, the correct endpoints are `x=D+u` and `y=u`, so
`Nat.Coprime D u` implies `Nat.Coprime (D+u) u`.
Avoid confusing `GN 7 D u` with `GN 7 u D` unless
the exact library identity is checked.

For alternating, use its *actual Lean definition*; do not replace a
natural subtraction with an unjustified signed-integer expression.
You may prove a useful private generic lemma first, but avoid
publishing a redundant new polynomial API.

## 2. Do not silently weaken the hypotheses

In the later GN allocation receiver we only know
`Nat.Coprime u (7*M)`. To obtain coprimality with
`D = 7^27*r^49` we also need `r ∣ M`.
This divisor guard is *not* part of
`NestedGNAllocationCondition M r` by itself.

**Gate 001 does not yet assert any unconditional
`nestedGNAllocation_mod_six` or `mod_42` theorem.**
Do not accidentally ship an overgeneralized statement.

No `sorry`, `admit`, `axiom`, `unsafe`, hidden nonempty assumption
or importing an unverified FLT7 closing theorem.
Do not change the definitions of the existing receivers.

## 3. Focused verification

Suggested test module:

```text
DkMathTest/FLT/Seven/SevenRamifiedFusionModSixResidues.lean
```

Include a proof-level application to each lemma and a few concrete
sanity checks; a numerical example alone is **not** a universal proof.

Run in `lean/dk_math` (or the repository's documented equivalent):

```bash
lake build -j 1 DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues
lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModSixResidues.lean
```

Audit both exports with `#print axioms`. Explicitly record whether
`propext`, `Classical.choice`, `Quot.sound` appear, and reject
`sorryAx` or other unexpected axioms. A no-error grep is not a
replacement for checking the actual exit status and full log.

If `lake` or the Mathlib environment is unavailable, do not claim a
verified build. Record the environment limitation.

## 4. Mandatory checkpoint and report

At start, create `findings-001.md` and record source results.
At the end, write `report-001.md` with:

1. Outcome A / B / C (see ROADMAP for meanings).
2. Exact declarations proved or reused, with full module paths.
3. Why each coprimality hypothesis is sufficient.
4. Exact changed files and code differences.
5. Commands and exit statuses for focused build and tests.
6. `#print axioms` output for each exported theorem.
7. Any counterexample, missing assumption, or blocked approach.
8. Proposed gate-002 bridge; mark it **not implemented**.

Do not edit `README.md` or `ROADMAP.md` status beyond truthful
checkpoint annotation, do not merge to `develop`, do not start
a full repository build, and do not open a PR unrequested.

**Return the report and stop.** The reviewer will inspect this outcome
and then tailor instruction-002. Small, reliable iterations are the goal.
