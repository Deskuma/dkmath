# Codex autonomous implementation directive — DHNT Cosmic-Square Analytic Scaling

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Primary integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`
Target phase: Phase I — analytic DHNT / Cosmic-square dynamic scaling

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration after completed Phases A--H by connecting the coordinate-level radial scaling kernel to one bounded analytic Cosmic Formula example.

The target picture is the square-case transformation

```text
F(y) = sqrt(1 + y) - 1
```

with dynamic logarithmic scale

```text
kappa(y) = log(F(y)) / log(y),
```

and the exact reconstruction contract

```text
y ^ kappa(y) = F(y)
```

under explicit domain hypotheses.

Then feed `kappa(y)` into the already-built Phase-H real prime-coordinate radial scaling:

```text
natural prime valuations of n
        ↓ cast to ℝ
realPrimeExponentCoordinates n
        ↓ radial scale by kappa(y)
dynamic scaled prime-coordinate image
```

The immediate goal is **not** a theory of prime factorization in `ℝ`, not a new analytic foundation, and not a global claim that the map `y ↦ F(y)` is multiplicative. The goal is to certify one exact analytic scalar reconstruction and one real-coordinate structural specialization.

This is an autonomous Lean implementation task. Inspect the actual branch state, existing DkMath definitions, and installed Mathlib theorem signatures before editing. The repository and successful Lean builds are the source of truth. Adapt theorem names and proof routes when current APIs make a smaller correct implementation possible.

---

## 1. Repository-first preflight — mandatory

Before editing, inspect the worktree and current branch:

```bash
git status -sb
git branch --show-current
git rev-parse HEAD
git log --oneline --decorate -20
git merge-base HEAD develop
git diff --stat develop...HEAD
```

Do not reset, stash, overwrite, or stage unrelated user changes.

Read the complete current StructuralArithmetic public tower, especially:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
DkMath/NumberTheory/StructuralArithmetic/PowerGauge.lean
DkMath/NumberTheory/StructuralArithmetic/PrimeCoordinates.lean
DkMath/NumberTheory/StructuralArithmetic/InterPeriod.lean
DkMath/NumberTheory/StructuralArithmetic/KUSObservation.lean
DkMath/NumberTheory/StructuralArithmetic/PrimitiveDirection.lean
DkMath/NumberTheory/StructuralArithmetic/FinitePrimeEscapeBridge.lean
DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean
DkMath/NumberTheory/StructuralArithmetic/GoldenUnitBridge.lean
DkMath/NumberTheory/StructuralArithmetic/RadialScaling.lean

docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/DHNT-RADIAL-SCALING-IMPLEMENTATION-REPORT-260820.md
```

Inspect relevant existing DHNT and analytic infrastructure before creating helpers:

```text
DkMath/DHNT/DHNT_Base.lean
DkMath/DHNT/UnitNatLayers.lean
DkMath/ABC/RpowExtras.lean
DkMath/ABC/ABCFinalRealExpFactorizationLog.lean
```

Search the repository and Mathlib for existing equivalents before inventing declarations:

```bash
rg -n "sqrt.*1.*\+|sqrt.*\+.*1|Real\.sqrt" DkMath/DHNT DkMath/CosmicFormula DkMath/NumberTheory DkMath/Analysis
rg -n "log.*\/.*log|Real\.log.*\/.*Real\.log|logb" DkMath
rg -n "rpow.*log|log.*rpow|rpow_def|exp_log|rpow_log" DkMath .lake/packages/mathlib/Mathlib
rg -n "radialScalePrimeCoordinates|realPrimeExponentCoordinates|radialScaleCoordinates" DkMath/NumberTheory/StructuralArithmetic
rg -n "sqrt_pos|one_lt_sqrt|sqrt_lt|sq_sqrt|sqrt_sq" .lake/packages/mathlib/Mathlib
```

Do not infer theorem signatures from memory. Use `#check` in a scratch Lean file if useful.

Baseline-build Phase A--H before editing:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GNBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge
lake build DkMath.NumberTheory.StructuralArithmetic.RadialScaling
lake build DkMath.NumberTheory.StructuralArithmetic
```

If the baseline fails, diagnose the failure first. Do not build Phase I on a broken baseline.

---

## 2. Certified semantic starting point

Phase H already proves that for a fixed real coordinate vector `v : ι → ℝ`:

```text
radialScaleCoordinates k v = (fun i => k * v i)
```

and for `k ≠ 0`:

```text
radialScaleCoordinates k v i = 0 ↔ v i = 0
Function.support (radialScaleCoordinates k v) = Function.support v
```

It also exposes:

```text
realPrimeExponentCoordinates (n : ℕ) : PrimeIndex → ℝ
radialScalePrimeCoordinates (k : ℝ) (n : ℕ) : PrimeIndex → ℝ
```

Do not duplicate these APIs.

Existing DkMath DHNT code already has positive-real unit structures, real logarithmic coordinates, and square-unit transformations. Existing ABC code already uses `Real.rpow`, `Real.log`, `Real.exp`, and related helper lemmas. Reuse current Mathlib / DkMath APIs when they shorten the proof.

---

## 3. Critical semantic boundaries — mandatory

### 3.1 Analytic reconstruction is not real prime factorization

The equality

```text
y ^ kappa = x
```

is a scalar analytic identity in positive reals.

The vector

```text
radialScalePrimeCoordinates kappa n
```

is a real-valued image of the integer valuation coordinates of `n`.

Do **not** claim that this vector is an ordinary unique prime factorization of the real number `x`.

Allowed terminology:

```text
real-valued prime-exponent coordinates
radially scaled prime-coordinate image
analytic scalar reconstruction
```

Avoid:

```text
prime factorization of x in ℝ
real primes
unique factorization of arbitrary positive reals
```

### 3.2 Dynamic scaling is not KUS transport/rebase

`kappa(y)` will be a dynamically selected scalar used by `radialScaleCoordinates` on a fixed index type.

It is not `DkMath.KUS.ScaleSpec`, which transports typed unit / blueprint support.

Do not add an unconditional equivalence or commuting theorem between these two operations.

### 3.3 Dynamic scaling is not PowerGauge projection

`radialScaleCoordinates` multiplies real coordinates.

`projectExponent` / `projectPrimeCoordinates` reduce natural exponents modulo a gauge period.

Do not identify them.

### 3.4 Cosmic Formula degree is not this dynamic exponent

The square in `sqrt(1+y)` comes from solving the square-case relation

```text
N + 1 = (P + 1)^2
```

for the positive branch `P = sqrt(N+1) - 1`.

The dynamic real scalar `kappa(y)` is not the Cosmic Formula polynomial degree `2`.

---

## 4. Recommended bounded module

Prefer one focused module such as:

```text
DkMath.NumberTheory.StructuralArithmetic.DynamicScaling
```

or

```text
DkMath.NumberTheory.StructuralArithmetic.CosmicSquareScaling
```

Choose a conflict-free repository-consistent name after search.

The module should import Phase H and only the light analytic dependencies needed for `Real.sqrt`, `Real.log`, and `Real.rpow`.

Do not import all of `DkMath.ABC` merely to access one lemma if direct Mathlib imports make the module substantially lighter. Conversely, reuse a small existing helper if doing so is clearly cleaner.

All public declarations added in this phase must have Lean docstrings.

---

## 5. Required bridge A — name the square-case image

Introduce the exact positive-branch square image, unless an equivalent definition already exists and can be reused directly.

Suggested definition:

```lean
noncomputable def cosmicSquareImage (y : ℝ) : ℝ :=
  Real.sqrt (1 + y) - 1
```

The name is only a suggestion.

Prove the essential positivity theorem under the smallest natural hypothesis, expected to be:

```lean
theorem cosmicSquareImage_pos {y : ℝ} (hy : 0 < y) :
    0 < cosmicSquareImage y
```

Mathematical reason:

```text
1 < 1 + y
sqrt 1 < sqrt (1+y)
1 < sqrt (1+y)
```

Use current Mathlib `sqrt` monotonicity / square-root API rather than squaring inequalities manually if a direct theorem exists.

Also expose, if cheap and stable, the square reconstruction:

```lean
theorem cosmicSquareImage_add_one_sq {y : ℝ} (hy : 0 ≤ y) :
    (cosmicSquareImage y + 1)^2 = 1 + y
```

or the equivalent orientation.

This theorem is useful provenance but is secondary to positivity and rpow reconstruction. Do not spend excessive effort if Mathlib simplification makes it awkward.

---

## 6. Required bridge B — dynamic logarithmic scale

Introduce the scale exponent only after the image is named.

Suggested definition:

```lean
noncomputable def cosmicSquareScale (y : ℝ) : ℝ :=
  Real.log (cosmicSquareImage y) / Real.log y
```

or `cosmicSquareScaleExponent` if clearer.

Do not hide domain failures inside the definition; Lean's total `Real.log` makes the definition total, while theorems must state the hypotheses under which it has the intended inverse meaning.

Expose a generic log-ratio reconstruction theorem if one does not already exist and if it improves reuse:

```lean
theorem rpow_log_ratio
    {base target : ℝ}
    (hbase : 0 < base)
    (hbase1 : base ≠ 1)
    (htarget : 0 < target) :
    Real.rpow base (Real.log target / Real.log base) = target
```

Adapt theorem spelling and orientation to the installed Mathlib API.

The proof should use existing `Real.rpow` / `Real.exp` / `Real.log` theorems. Do not reimplement transcendental analysis.

A likely proof route is algebraically:

```text
base^(log target / log base)
= exp((log target / log base) * log base)
= exp(log target)
= target
```

but prefer a direct Mathlib theorem if available.

The hypothesis `base ≠ 1` is load-bearing because it ensures `log base ≠ 0` under `base > 0`.

---

## 7. Required bridge C — Cosmic-square analytic reconstruction

Consume the positivity theorem and the generic log-ratio theorem to prove the square-case reconstruction.

Preferred theorem shape:

```lean
theorem cosmicSquareImage_rpow_scale
    {y : ℝ}
    (hy : 0 < y)
    (hy1 : y ≠ 1) :
    Real.rpow y (cosmicSquareScale y) = cosmicSquareImage y
```

or equivalent notation using `y ^ cosmicSquareScale y` if repository style and typeclass inference are stable.

This is the main analytic theorem of Phase I.

Do not strengthen it to a global theorem for all real `y` unless the extra cases are intentionally and correctly characterized.

---

## 8. Required boundary theorem — the `y = 3` collapse point

The earlier DHNT numerical exploration found an exact structural boundary:

```text
cosmicSquareImage 3 = 1
```

because `sqrt 4 - 1 = 1`.

Prove this exact statement if not already trivial by `norm_num` / sqrt simplification:

```lean
@[simp] theorem cosmicSquareImage_three :
    cosmicSquareImage 3 = 1
```

Then prove:

```lean
@[simp] theorem cosmicSquareScale_three :
    cosmicSquareScale 3 = 0
```

This is important because Phase H proves support preservation only for a **nonzero** radial scale. At `y = 3`, the dynamically selected scale is exactly zero, so the coordinate image deliberately collapses.

If the exact second theorem is difficult only because of rewriting `Real.log 1 = 0`, use the smallest direct proof. Do not omit this boundary merely to present a falsely uniform support-preservation story.

---

## 9. Required bridge D — dynamic prime-coordinate image

Reuse Phase H directly.

Suggested definition:

```lean
noncomputable def dynamicPrimeCoordinates
    (y : ℝ) (n : ℕ) : PrimeIndex → ℝ :=
  radialScalePrimeCoordinates (cosmicSquareScale y) n
```

Choose a more explicit name such as `cosmicSquareRadialPrimeCoordinates` if needed.

Expose its definitional connection to `radialScalePrimeCoordinates` if useful.

Then prove support / zero-pattern preservation under an explicit nonzero-scale hypothesis:

```lean
theorem dynamicPrimeCoordinates_eq_zero_iff
    {y : ℝ}
    (hk : cosmicSquareScale y ≠ 0)
    (n : ℕ) (p : PrimeIndex) :
    dynamicPrimeCoordinates y n p = 0 ↔
      realPrimeExponentCoordinates n p = 0
```

and preferably:

```lean
theorem support_dynamicPrimeCoordinates
    {y : ℝ}
    (hk : cosmicSquareScale y ≠ 0)
    (n : ℕ) :
    Function.support (dynamicPrimeCoordinates y n) =
      Function.support (realPrimeExponentCoordinates n)
```

These must be thin corollaries of Phase H; do not reprove coordinate support algebra.

---

## 10. Preferred domain theorem — characterize the nonzero-scale condition

If it is cheap with current Mathlib APIs, prove a theorem that explains when the dynamic scalar vanishes.

A particularly useful square-case statement under `y > 0`, `y ≠ 1` is expected to be equivalent to:

```text
cosmicSquareScale y = 0 ↔ cosmicSquareImage y = 1
```

and, if manageable,

```text
cosmicSquareImage y = 1 ↔ y = 3
```

under the suitable nonnegative / positive hypothesis.

This would yield:

```text
cosmicSquareScale y ≠ 0 ↔ y ≠ 3
```

for the intended positive domain with the separate denominator boundary `y ≠ 1` already handled.

However, this characterization is **preferred, not mandatory** if proving it requires a disproportionate amount of square-root order machinery.

The mandatory boundary is the exact `y = 3` collapse theorem from section 8 and support preservation under an explicit `kappa ≠ 0` hypothesis.

---

## 11. Required concrete checkpoint — the `y = 30` example

The original motivating numerical observation used:

```text
y = 30
F(30) = sqrt(31) - 1
k = log(F(30)) / log(30)
```

and numerically observed `k ≈ 0.446614...`.

Phase I should certify the **exact symbolic statement**, not the decimal approximation.

Required theorem equivalent to:

```lean
theorem cosmicSquareImage_thirty :
    cosmicSquareImage 30 = Real.sqrt 31 - 1
```

and the main exact reconstruction:

```lean
theorem thirty_rpow_cosmicSquareScale :
    Real.rpow 30 (cosmicSquareScale 30) = Real.sqrt 31 - 1
```

This should be obtained by specializing the generic theorem and simplifying; do not create a numerical-analysis proof.

Also prove that the scale is nonzero if this follows cheaply, for example from `cosmicSquareImage 30 ≠ 1`:

```lean
cosmicSquareScale 30 ≠ 0
```

Then obtain a concrete Phase-H structural corollary:

```text
support of dynamic prime coordinates at scale y=30
= support of the original real prime-exponent coordinates of n
```

At minimum instantiate this for `n = 30` if the theorem is easy:

```lean
Function.support (dynamicPrimeCoordinates 30 30) =
  Function.support (realPrimeExponentCoordinates 30)
```

Do not require explicit evaluation of the support as exactly `{2,3,5}` unless existing valuation simplification makes that nearly free. The load-bearing point is that the dynamic analytic scalar feeds the already-certified radial support theorem.

---

## 12. Do not claim a multiplicative homomorphism for the dynamic map

For fixed `k`, positive-real rpow is multiplicative under appropriate positivity hypotheses.

But here `kappa(y)` depends on `y`.

Therefore do not claim:

```text
F(ab) = F(a) * F(b)
```

or that

```text
y ↦ y ^ kappa(y)
```

is a multiplicative homomorphism merely because each point reconstructs `F(y)`.

The Phase-I theorem is pointwise analytic reconstruction.

---

## 13. Do not overconnect to generic Cosmic Formula GN

The square-image formula is provenance from the square Cosmic Formula relation, while Phase F already handles generic polynomial `GN` / `GN5` arithmetic.

Phase I need not prove a new theorem about generic `GN d`.

If an existing theorem directly identifies the square-case `P` solution with `sqrt(1+y)-1`, reuse it. Otherwise keep the bridge local and explicitly document the square-case interpretation.

Do not make this phase a general `d`-th-root / log scaling theory.

---

## 14. Import and dependency discipline

Prefer a light import path.

A good target shape is approximately:

```lean
import DkMath.NumberTheory.StructuralArithmetic.RadialScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
```

but inspect the installed Mathlib paths first and use whatever is actually needed.

Do not import the full FLT5 or RH towers.

Do not modify `DkMath.DHNT.DHNT_Base` unless a tiny existing theorem genuinely belongs there and avoids duplication. Prefer a bridge-local implementation.

---

## 15. Public aggregate and documentation

If a new Phase-I module is added, export it from:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
```

Update the aggregate module docstring so Phase I is represented accurately.

Update:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

Mark Phase I completed only after successful builds.

Write a focused implementation report such as:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/DHNT-COSMIC-SQUARE-ANALYTIC-SCALING-IMPLEMENTATION-REPORT-260820.md
```

The report must record:

- exact baseline HEAD;
- files changed;
- exact new theorem names;
- domain hypotheses used by the reconstruction theorem;
- treatment of `y = 1` and `y = 3`;
- whether a generic `rpow_log_ratio` theorem was added or reused;
- whether the exact `y = 30` reconstruction was certified;
- whether dynamic prime-coordinate support preservation was connected;
- explicit statement that no real prime-factorization theorem is claimed;
- build commands and results;
- axiom audit results;
- any pre-existing warnings.

---

## 16. Verification requirements

At minimum run:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.<PhaseIModule>
lake build DkMath.NumberTheory.StructuralArithmetic.RadialScaling
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic

git diff --check
```

Also re-run any directly touched DHNT module if you edit it.

Search new Phase-I source for forbidden placeholders:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b" \
  DkMath/NumberTheory/StructuralArithmetic/<PhaseIModule>.lean
```

No new `sorry`, `admit`, project-specific axiom, or `unsafe` escape hatch.

Use `#print axioms` on at least:

- the generic or square-specific rpow reconstruction theorem;
- the `y = 3` collapse theorem;
- the dynamic prime-coordinate support theorem;
- the exact `y = 30` reconstruction theorem.

Inherited standard Lean/Mathlib axioms are acceptable; report them accurately.

---

## 17. Anti-maze rules

Do not turn Phase I into any of the following:

- a generic theory of logarithmic coordinates on all groups;
- a generic quotient/category framework;
- a theory of factorization of arbitrary real numbers;
- a general `d`-th-root Cosmic Formula solver;
- a new DHNT unit hierarchy replacing existing `DkMath.DHNT`;
- an RH or zeta argument;
- a refactor of Phase A--H;
- numerical approximation infrastructure for the decimal value of `kappa(30)`.

A successful Phase I is small and load-bearing:

```text
square image F(y)
        ↓ positivity
log-ratio dynamic scale kappa(y)
        ↓ exact Real.rpow reconstruction
F(y) = y ^ kappa(y)
        ↓
Phase-H radial prime-coordinate image
        ↓
nonzero kappa ⇒ support preserved
```

plus the exact boundary:

```text
y = 3 ⇒ F(y)=1 ⇒ kappa(y)=0 ⇒ radial collapse boundary
```

and the exact symbolic example:

```text
y = 30 ⇒ 30 ^ kappa(30) = sqrt(31) - 1
```

---

## 18. Autonomous decision rule

During repository inspection you may discover that some proposed declarations already exist or that current Mathlib has a better direct theorem.

Use this priority:

1. reuse an existing theorem exactly;
2. add a thin bridge theorem;
3. add a small local helper;
4. only then add a new definition.

If a proposed optional theorem becomes disproportionately difficult, do not expand scope. Preserve the mandatory load-bearing chain and document the omitted optional result.

Do not stop merely because one suggested theorem spelling is unavailable. Find the current API and complete the mathematical contract.

---

## 19. Completion criteria

Phase I is complete only if all of the following hold:

1. A square-image function equivalent to `sqrt(1+y)-1` is reused or introduced.
2. Its positivity is certified on the intended positive domain.
3. A log-ratio dynamic scale is reused or introduced.
4. An exact `Real.rpow` reconstruction theorem is certified with explicit domain hypotheses.
5. `y = 3` is explicitly certified as the zero-scale collapse boundary.
6. The dynamic scale is fed into Phase-H `radialScalePrimeCoordinates` through a reusable API.
7. A zero-pattern/support theorem for the dynamic prime-coordinate image is proved under explicit nonzero-scale hypothesis.
8. The exact symbolic `y = 30` reconstruction `30^kappa = sqrt(31)-1` is theorem-level.
9. The public StructuralArithmetic aggregate imports the module.
10. README and a focused implementation report are updated.
11. Focused builds and aggregate build succeed.
12. `git diff --check` succeeds.
13. No new placeholder / project-specific axiom / unsafe declaration is introduced.
14. The implementation does not claim real prime factorization or dynamic multiplicativity.
15. Commit the completed implementation to the current branch and push it.
16. Do not merge to `develop` and do not open/merge a PR unless explicitly requested by the user.

After completion, report the exact branch, baseline and final HEADs, theorem list, build commands, axiom audit, and the next genuinely unclosed StructuralArithmetic gap.