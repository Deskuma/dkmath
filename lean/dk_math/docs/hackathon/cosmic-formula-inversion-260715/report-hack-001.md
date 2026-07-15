# Report — Checkpoint hack-001

## Status

```text
COMPLETED
```

## Session Metadata

```text
Checkpoint: hack-001
Session class: AUDIT
Model: GPT-5 Codex
Reasoning level: not recorded
Session identifier: not recorded
Start: not recorded
End: 2026-07-15 07:23 JST
Elapsed: not recorded
Starting credits: not recorded
Ending credits: not recorded
Credits consumed: not recorded
```

## Primary Goal

Audit DkMath and Mathlib for the smallest dependency route from a finite prime
set and coprime offset to a fresh prime factor, connect the arithmetic to the
Cosmic Formula square completion, and identify only the entry points for later
rational projection and DkReal work.

## Stable Documents Read

The following were read in the prescribed order:

1. `README.md`
2. `PROJECT.md`
3. `MATHEMATICAL_CONTRACT.md`
4. `ROADMAP.md`
5. `ARCHITECTURE.md`
6. `GLOSSARY.md`
7. `DECISIONS.md`
8. `RISKS_AND_STOPPING_RULES.md`
9. `EXISTING_DKMATH_MAP.md`
10. `VISUAL_STORYBOARD.md`
11. `DEMO_CONTRACT.md`
12. `CHECKPOINTS.md`
13. `CODEX_PLAN.md`
14. `__next_Instructions.md`

`1st_PLAN.md` was treated as historical context and the empty UUID tracking
anchor was not inspected.

## Repository Instructions Read

- `/home/deskuma/develop/lean/dkmath/README.md`
- `/home/deskuma/develop/lean/dkmath/AGENT.md`
- `/home/deskuma/develop/lean/dkmath/lean/dk_math/README.md`
- `/home/deskuma/develop/lean/dkmath/lean/dk_math/notes/chatgpt_projects/cosmic_formula_lean/SUMMARY.md`

The repository rule relevant here is the one-way dependency path from research
code toward stable library surfaces. The hackathon facade must remain
downstream of existing DkMath and Mathlib.

## Search Sources

- Lean source root: `/home/deskuma/develop/lean/dkmath/lean/dk_math`
- DkMath module root: `/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath`
- theorem heading index:
  `/home/deskuma/develop/lean/dkmath/logs/summary_report/__theorems-heading.txt`
- compressed source database:
  `/home/deskuma/develop/lean/dkmath/logs/__dkmath-all.lean.txt.gz`
- second located compressed source database:
  `/home/deskuma/develop/lean/dkmath/lean/dk_math/logs/__dkmath-all.lean.txt.gz`
- summary archive:
  `/home/deskuma/develop/lean/dkmath/logs/__summary_report_data.tar.gz`
- Mathlib source:
  `/home/deskuma/develop/lean/dkmath/lean/dk_math/.lake/packages/mathlib/Mathlib`
- direct DkMath modules listed below

The compressed database was searched in place; it was not unpacked or
duplicated. The summary archive was listed without bulk extraction.

## Modules Inspected

- `DkMath.Hackathon.FinitePrimeEscape`
- `DkMath.Hackathon.CosmicCompletion`
- `DkMath.Hackathon.Demo`
- `DkMath.Samples.Prime.A`
- `DkMath.Samples.Prime.B`
- `DkMath.CosmicFormula.Defs`
- `DkMath.CosmicFormula.CosmicFormulaBinom`
- `DkMath.CosmicFormula.CoreBeamGap`
- `DkMath.NumberTheory.PrimitiveSet.Basic`
- `DkMath.Petal.PrimitiveBridge`
- `DkMath.Petal.BezoutBridge`
- `DkMath.Samples.Projection`
- `DkMath.Analysis.DkReal.Interval`
- `DkMath.Analysis.DkReal.Basic`
- `DkMath.Analysis.DkReal.Semantic`
- relevant DkReal arithmetic, order, and CF2D search hits
- Mathlib Finset product, Nat gcd, Nat prime, and divisibility sources

## Finite Prime Route

The exact proposed path remains entirely in `ℕ`:

```text
q ∈ S
→ Finset.dvd_prod_of_mem
→ q ∣ P
q ∣ P + u and q ∣ P
→ dvd_add_right
→ q ∣ u
q ∣ P and q ∣ u
→ Nat.dvd_gcd
Nat.Coprime P u
→ Nat.gcd P u = 1
Nat.Prime q
→ q ∤ 1
→ contradiction
→ q ∉ S
```

For existence, `1 < P + u` implies `P + u ≠ 1`, so
`Nat.ne_one_iff_exists_prime_dvd` supplies a prime divisor. Applying the
supplied-divisor exclusion theorem produces a fresh prime factor.

Explicit answers:

- No matching `FreshPrimeFactor` predicate exists.
- No completed exact supplied-divisor exclusion theorem with the requested
  Coprime surface exists.
- No completed exact fresh-prime existence theorem with the requested
  hypotheses exists.
- Primality of every member of `S` is not logically required for exclusion.
- `S.Nonempty` is not required.
- `0 < u` is not required for exclusion or for existence when `1 < P + u` is
  supplied separately.
- `Nat.ne_one_iff_exists_prime_dvd` is the exact prime-divisor existence API.

## Cosmic Formula Route

The generic structure exists:

```text
DkMath.CosmicFormulaBinom.big_is_body_and_gap
Big d x u = Body d x u + Gap d u
```

and `CoreBeamGap.big_eq_body_add_gap` gives a generic subtraction-free
semiring route. At `d = 2`, these specialize mathematically to the desired
square. However, the exact public Nat identity

```lean
P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

is not exposed by a narrow stable theorem. `cosmic_identity_ring` in
`DkMath.Samples.Prime.B` is a subtraction-equals-zero near match, but importing
that broad sample module would also import unrelated and unfinished material.
The recommended implementation is therefore a thin local theorem proved by
`ring`. GN/GZ need not appear in the public MVP facade.

## Projection Entry Points

No existing DkMath definition matches either candidate projection:

```text
unsigned: P / (P + u), image [0,1)
signed:  -P / (P + u), image (-1,0]
```

No exact inverse theorem was found. The future rational formulas are
`u*x/(1-x)` and `-u*x/(1+x)`, with nonzero-denominator conditions. The unsigned
convention is architecturally preferable for a first bridge because the
current DkReal arithmetic is nonnegative; this is a recommendation, not an
implementation decision. `DkMath.Samples.Projection` and CF2D inverse actions
have different semantics and are rejected as reuse candidates.

## DkReal Entry Points

The primary carrier is `DkMath.Analysis.DkReal`, a nested sequence of rational
`GapInterval`s with widths tending to zero. `GapInterval` has rational
endpoints, validity, width, singleton, addition, nonnegative multiplication,
natural-power images, and separation. Relevant direct theorems include
`interval_succ_subset`, `interval_subset_of_le`, `tendsto_width_zero`, and
`GapInterval.width_nonneg`; `DkReal.ofRat` supplies exact rational embedding.

No compatible fractional-linear interval-map operation, inverse width
transport theorem, or packaged width-less-than-one integer uniqueness theorem
was found. The first likely representation bridge is an inverse-projection
endpoint map producing a valid `GapInterval` and transporting membership.

## Confirmed Reusable Declarations

### `Finset.dvd_prod_of_mem`

- Module: `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`
- Type: `(ha : a ∈ s) → f a ∣ ∏ i ∈ s, f i`
- Classification: DIRECT
- Intended role: a member of `S` divides its product.

### `dvd_add_right`

- Module: `Mathlib.Algebra.Ring.Divisibility.Basic`
- Type: `(h : a ∣ b) → (a ∣ b + c ↔ a ∣ c)`
- Classification: DIRECT
- Intended role: derive `q ∣ u` from `q ∣ P` and `q ∣ P + u`.

### `Nat.dvd_gcd` and `Nat.coprime_iff_gcd_eq_one`

- Module: Mathlib Nat gcd API
- Types: common divisibility implies divisibility of `Nat.gcd`; Coprime is
  equivalent to gcd one.
- Classification: DIRECT
- Intended role: contradict a prime common divisor.

### `Nat.Prime.not_dvd_one`

- Module: Mathlib Nat prime API
- Type: `Nat.Prime q → ¬ q ∣ 1`
- Classification: DIRECT
- Intended role: final contradiction.

### `Nat.ne_one_iff_exists_prime_dvd`

- Module: `Mathlib.Data.Nat.Prime.Basic`
- Type: `n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n`
- Classification: DIRECT
- Intended role: prime-divisor existence from `1 < n`.

### `DkMath.CosmicFormulaBinom.big_is_body_and_gap`

- Module: `DkMath.CosmicFormula.CosmicFormulaBinom`
- Type: for a `CommRing R`,
  `Big d x u = Body d x u + Gap d u`
- Classification: DIRECT for generic Cosmic semantics; BRIDGE for the Nat
  public square formula.
- Intended role: confirm that the local square identity matches existing
  Big/Body/Gap architecture.

### DkReal interval declarations

- Modules: `DkMath.Analysis.DkReal.Interval` and `.Basic`
- Declarations: `GapInterval.width`, `DkReal.interval_subset_of_le`,
  `DkReal.tendsto_width_zero`, `DkReal.ofRat`
- Classification: DIRECT entry points
- Intended role: later nested-interval reconstruction, not this MVP.

## Rejected Near Matches

- `exists_prime_not_mem_dvd_prod_add_unit` in `DkMath.Samples.Prime.B` uses
  positivity and per-member nondivisibility rather than the requested Coprime
  theorem surface. It is a useful proof precedent, not the chosen dependency.
- `exists_prime_not_mem_dvd_prod_add_unit_of_coprime'` has the desired surface
  but its proof is `sorry`; it cannot be reused.
- `DkMath.CosmicFormula.exists_prime_not_mem_dvd_prod_succ` is specialized to
  offset `1`, not arbitrary coprime `u`.
- `PrimitiveOn`, `PrimitivePrimeFactorOfDiffPow`, Petal primitive bridges, and
  Zsigmondy predicates have divisibility-antichain or sequence-relative
  meanings. They are not finite-set freshness.
- `cosmic_identity_ring` is mathematically suitable but lives in a broad
  sample module with unfinished declarations.
- `DkMath.Samples.Projection` and CF2D inverse kernels are semantically
  unrelated to the candidate rational projection.

## Dangerous Dependencies

- Importing `DkMath.Samples.Prime.B` would couple the facade to global sample
  declarations and unfinished proofs.
- PrimitiveSet/Petal/Zsigmondy imports are broad and would misstate the
  semantics as primitive-divisor theory.
- KUS, Units, and CF2D imports would add unrelated abstraction and risk reverse
  architectural pressure.
- Existing `DkMath.CosmicFormula.Defs` uses real-only Big/Body/Gap definitions;
  forcing the Nat MVP through them adds coercions and hides a trivial identity.

## Genuinely Missing Lemmas

The smallest missing MVP theorem is:

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

The first later DkReal obstruction is an interval map for the selected
fractional-linear inverse, including endpoint order and membership transport.

## Proposed `hack-002` Implementation Surface

- Exact file permitted to change:
  `lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean`
- Proposed imports: narrow Mathlib Finset product, Nat gcd, and Nat prime
  modules; `import Mathlib` is acceptable initially if narrowing is deferred.
- Proposed definition: hackathon-local `FreshPrimeFactor S n q :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S`, since no exact predicate exists.
- Proposed theorems:
  `prime_dvd_product_add_coprime_not_mem`,
  `exists_fresh_prime_factor`, and optionally a universal wrapper.
- Required build commands from `lean/dk_math`:
  `lake build DkMath.Hackathon.FinitePrimeEscape`, followed by
  `lake build` if the checkpoint requires full regression.

No change to `CosmicCompletion.lean` or `Demo.lean` belongs in `hack-002` unless
a later instruction explicitly expands that checkpoint.

## Assumption Audit

| Assumption | Exclusion | Existence | Reason |
|---|---:|---:|---|
| all members of `S` prime | not needed | not needed logically | only validates the phrase finite prime set |
| `S.Nonempty` | not needed | not needed | empty product is `1` |
| `0 < u` | not needed | not needed with `1 < P + u` | no subtraction or positivity route required |
| `0 < P` | not needed | not needed with `1 < P + u` | boundary hypothesis is sufficient |
| `Nat.Coprime P u` | required | required for freshness | excludes common divisors |
| `1 < P + u` | not needed | required | supplies a prime divisor |
| `Nat.Prime q` | required | supplied by existence theorem | excludes `q ∣ 1` |
| `q ∣ P + u` | required | supplied by existence theorem | boundary divisor premise |

## Files Changed

- `EXISTING_DKMATH_MAP.md`
- `report-hack-001.md`

## No-Source-Edit Confirmation

```text
No Lean source file was edited.
```

## First Genuine Obstruction

None for completing this audit. The first missing MVP theorem is the small
supplied-divisor exclusion lemma stated above; its absence is a normal audit
finding, not a checkpoint obstruction.

## Out-of-Scope Routes Not Taken

- no Lean theorem or predicate was implemented;
- no scaffold source was edited;
- no projection convention was formalized;
- no DkReal interval map or width theorem was implemented;
- no Euclidean geometry or Manim work was begun;
- no primitive-divisor theorem was repurposed;
- no later checkpoint was started;
- no build was run merely to simulate progress.

## Next Permitted Action

Wise Wolf review of checkpoint hack-001.

## Stop Confirmation

```text
The checkpoint stopped after the audit report.
No Lean implementation was begun.
No later checkpoint work was begun.
```
