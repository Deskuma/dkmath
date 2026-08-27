# Codex autonomous implementation directive — DHNT Radial Scaling / Rebase Distinction

Date: 2026-08-20
Repository: `Deskuma/dkmath`
Expected working branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Primary integration area: `lean/dk_math/DkMath/NumberTheory/StructuralArithmetic/`
Target phase: Phase H — DHNT-style radial scaling / rebase distinction

## 0. Mission

Continue the Structural Arithmetic / Red Ribbon integration after completed Phases A--G by formalizing the remaining load-bearing distinction between:

1. **radial scaling** of an already chosen structural coordinate direction; and
2. **rebase / support transport**, where the chosen structural support or basis itself may change.

The motivating DHNT-style picture is:

```text
raw structural coordinates v
        |
        +---- radial scale by k ----> k * v
        |                              same zero-pattern/support when k != 0
        |
        `---- rebase / transport ----> a possibly different support/basis
```

The immediate goal is **not** to formalize the full analytic formula

```text
k = log(x) / log(y)
x = y^k
```

and not to introduce a theory of real prime factorization. The first goal is to make the structural distinction theorem-level with the smallest stable coordinate API, then connect it to the already-existing prime valuation coordinates.

This is an autonomous Lean implementation task. Inspect the actual repository state and Mathlib APIs first. Use the repository and successful builds as the source of truth. Do not treat this directive as a fixed patch recipe if a smaller correct implementation is already available.

---

## 1. Repository-first preflight — mandatory

Before editing, inspect the actual branch/worktree state:

```bash
git status -sb
git branch --show-current
git rev-parse HEAD
git log --oneline --decorate -20
git merge-base HEAD develop
git diff --stat develop...HEAD
```

Do not reset, stash, overwrite, or stage unrelated user changes.

Read the complete current StructuralArithmetic tower:

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

docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/GOLDEN-UNIT-RED-RIBBON-BRIDGE-IMPLEMENTATION-REPORT-260820.md
```

Inspect the existing KUS transport vocabulary carefully:

```text
DkMath/KUS/Scale.lean
DkMath/KUS/Transport.lean
DkMath/KUS/Bridge.lean
DkMath/KUS/CosmicBridge.lean
```

Search the repository before introducing any new definition/theorem:

```bash
rg -n "ScaleSpec|scaleUS|scaleGKUS|HarmonizeSpec|DecodeSpec" DkMath/KUS DkMath/NumberTheory/StructuralArithmetic
rg -n "radial|scaleCoordinates|scaledCoordinates|coordinate.*scale|support.*scale" DkMath
rg -n "Real\.rpow|Real\.log|rpow|log.*rpow" DkMath
rg -n "primeExponentCoordinates|projectPrimeCoordinates|padicValNat" DkMath/NumberTheory DkMath/ABC
rg -n "Function\.support|support.*fun|Set.*support" DkMath
```

Note that `Real.rpow` infrastructure already exists elsewhere in DkMath (for example under ABC). Inspect it only if needed; Phase H should not import a heavy analytic tower merely to prove the coordinate kernel.

Baseline-build A--G before editing:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.InterPeriod
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
lake build DkMath.NumberTheory.StructuralArithmetic.PrimitiveDirection
lake build DkMath.NumberTheory.StructuralArithmetic.FinitePrimeEscapeBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GNBridge
lake build DkMath.NumberTheory.StructuralArithmetic.GoldenUnitBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

If baseline build fails, diagnose it first. Do not build Phase H on a broken baseline.

---

## 2. Critical naming boundary — KUS `ScaleSpec` is not DHNT radial scaling

The repository already has:

```lean
DkMath.KUS.ScaleSpec
```

with semantics approximately:

```text
mapUnit : U -> V
mapBlueprint : Blueprint u -> Blueprint' (mapUnit u)
```

and `scaleUS`, `scaleKUS`, `scaleGKUS` transport supports/blueprints while preserving the visible coefficient.

This operation is a **typed support/unit transport**. In the StructuralArithmetic story it belongs conceptually to the rebase/transport side, even though its historical API is named `ScaleSpec`.

Do not reuse the bare name `scaleCoordinates` if it risks implying that KUS transport and DHNT radial scaling are the same operation.

Prefer an explicit name such as:

```text
radialScaleCoordinates
radialScalePrimeCoordinates
```

or a repository-consistent equivalent discovered during inspection.

Do not rename the mature KUS API in this phase.

Do not claim that every KUS `ScaleSpec` changes support, either: identity and observation-compatible transports exist. The required distinction is only that **radial scaling is pointwise scalar multiplication on fixed coordinates**, whereas KUS transport is a different typed operation that may change the support interpretation.

---

## 3. Mathematical contract for Phase H

For a real coordinate vector

```text
v : ι -> ℝ
```

and scalar `k : ℝ`, define radial scaling by

```text
(radialScale k v)(i) = k * v(i).
```

The essential laws are:

```text
radialScale 1 v = v
radialScale a (radialScale b v) = radialScale (a*b) v
radialScale 0 v = 0
```

and, critically, for `k != 0`:

```text
radialScale k v i = 0  <->  v i = 0
```

Hence the zero-pattern / structural support is preserved:

```text
support (radialScale k v) = support v    when k != 0.
```

This is the theorem-level statement behind:

> a nonzero radial scale changes magnitude but preserves structural direction/support.

The zero scalar is the deliberate collapse boundary and must not be silently excluded from the API itself.

---

## 4. Recommended minimal module

Prefer one focused module, for example:

```text
DkMath.NumberTheory.StructuralArithmetic.RadialScaling
```

The exact name may change after conflict search, but keep it in the StructuralArithmetic layer.

A minimal implementation may specialize directly to `ℝ` to avoid a generic algebra abstraction project.

Candidate definition:

```lean
def radialScaleCoordinates
    (k : ℝ) (v : ι -> ℝ) : ι -> ℝ :=
  fun i => k * v i
```

A more generic scalar type is acceptable only if it makes the file strictly smaller and the zero-pattern theorem remains clean. Do not open a general module/semiring hierarchy merely for elegance.

All public declarations added in this phase must have Lean docstrings.

---

## 5. Required bridge A — basic radial-scale algebra

Provide the smallest useful laws for the coordinate operation.

Expected theorem shapes include equivalents of:

```lean
@[simp] theorem radialScaleCoordinates_one (v : ι -> ℝ) :
  radialScaleCoordinates 1 v = v

@[simp] theorem radialScaleCoordinates_zero (v : ι -> ℝ) :
  radialScaleCoordinates 0 v = fun _ => 0

theorem radialScaleCoordinates_mul
    (a b : ℝ) (v : ι -> ℝ) :
  radialScaleCoordinates a (radialScaleCoordinates b v) =
    radialScaleCoordinates (a * b) v
```

Orient multiplication according to the definition and commutativity simplification actually used by Lean. The mathematical content matters, not the exact spelling above.

Do not add a category/action abstraction unless an existing Mathlib action instance makes the implementation smaller.

---

## 6. Required bridge B — zero-pattern / support preservation

This is the load-bearing theorem of Phase H.

Prove pointwise preservation under nonzero scale:

```lean
theorem radialScaleCoordinates_eq_zero_iff
    {k : ℝ} (hk : k != 0) (v : ι -> ℝ) (i : ι) :
    radialScaleCoordinates k v i = 0 <-> v i = 0
```

Adapt syntax to Lean (`≠`, etc.).

Then expose a structural support theorem if `Function.support` or another existing support API is lightweight:

```lean
theorem support_radialScaleCoordinates
    {k : ℝ} (hk : k ≠ 0) (v : ι -> ℝ) :
    Function.support (radialScaleCoordinates k v) = Function.support v
```

If `Function.support` introduces undesirable dependencies, define no new support object solely for aesthetics. A pointwise nonzero equivalence is sufficient only if accompanied by a small reusable relation showing the whole zero-pattern is equal.

A small predicate such as

```lean
SameZeroPattern v w := ∀ i, v i = 0 ↔ w i = 0
```

is acceptable if no equivalent already exists and if it genuinely improves reuse.

Do not confuse this support with:

- `Nat.factorization.support`;
- KUS support / blueprint;
- `Finset` of known prime scales.

The theorem is about zero coordinates of a vector.

---

## 7. Required bridge C — natural prime valuations embedded into real radial coordinates

Reuse Phase B rather than creating a second prime-coordinate source.

Current raw source is:

```lean
primeExponentCoordinates (n : ℕ) : PrimeIndex -> ℕ
```

Introduce only the thin real-valued view needed for DHNT-style radial scaling, for example:

```lean
def realPrimeExponentCoordinates (n : ℕ) : PrimeIndex -> ℝ :=
  fun p => (primeExponentCoordinates n p : ℝ)
```

and:

```lean
def radialScalePrimeCoordinates (k : ℝ) (n : ℕ) : PrimeIndex -> ℝ :=
  radialScaleCoordinates k (realPrimeExponentCoordinates n)
```

Names may be adapted after search.

Required theorem:

```text
for k != 0, radialScalePrimeCoordinates k n has exactly the same zero-pattern as realPrimeExponentCoordinates n.
```

This is the concrete prime-valuation specialization of the generic support-preservation law.

Do not claim that the scaled vector is itself the ordinary prime factorization of a real number. It is a **real-valued image of the integer valuation coordinates**.

Preferred docstring terminology:

```text
real-valued prime-exponent coordinates
scaled prime-coordinate image
```

Avoid calling it “prime factorization in ℝ”.

---

## 8. Required bridge D — theorem-level separation from rebase / target support change

Phase H must not stop at `k * v` algebra. Add one theorem that makes the scaling-vs-rebase distinction usable.

A generic theorem shape is sufficient:

```lean
theorem radialScale_ne_of_source_nonzero_target_zero
    {k : ℝ} (hk : k ≠ 0)
    {v w : ι -> ℝ} {i : ι}
    (hvi : v i ≠ 0)
    (hwi : w i = 0) :
    radialScaleCoordinates k v ≠ w
```

Mathematical meaning:

> a nonzero radial scale cannot erase an existing structural coordinate. Therefore any representation whose support drops that coordinate cannot be the result of pure radial scaling.

This theorem is the safe formal core of the `30` versus `6` discussion without hard-coding that numerical example.

If repository APIs make a concrete prime example cheap and robust, add one as a smoke test / theorem, for example showing that a nonzero radial scale of the prime-coordinate direction of `30` cannot equal the unscaled prime-coordinate vector of `6` because the `5`-coordinate is present in `30` and absent in `6`.

However:

- do not spend the phase fighting computation of `padicValNat` merely for this example;
- the generic support-difference theorem is mandatory and sufficient;
- the concrete `30`/`6` theorem is optional if it is genuinely cheap.

---

## 9. KUS connection — semantic documentation and only thin theorem-level links

Inspect `DkMath.KUS.ScaleSpec` and `KUSObservation.ObservationCompatible`.

Phase H should explicitly document in Lean module comments that:

```text
radialScaleCoordinates
```

is fixed-index scalar multiplication, whereas:

```text
KUS.ScaleSpec
```

is support/unit/blueprint transport.

Do not create an unconditional theorem claiming they commute or are equivalent.

If a tiny useful bridge is available, it may state that an observation-compatible `ScaleSpec` leaves the existing natural observation unchanged, but that theorem already exists in Phase D:

```text
rawObservation_scaleGKUS_of_compatible
observePeriod_scaleGKUS_of_compatible
```

Reuse/reference those results in documentation rather than duplicating them.

The conceptual table should remain:

```text
Radial scale:
  fixed coordinate index
  v -> k*v
  nonzero k preserves zero-pattern

KUS transport / rebase:
  may change unit/blueprint type
  requires explicit ObservationCompatible to preserve a chosen observation
```

Do not rename `ScaleSpec` to `RebaseSpec` in this phase.

---

## 10. Explicit non-goals — do not drift into Phase I

The following are **not required in Phase H**:

```text
F(y) = sqrt(1+y) - 1
k_F(y) = log(F(y)) / log(y)
F(y) = y^(k_F(y))
2^k * 3^k * 5^k
finite products of Real.rpow over factorization support
```

Do not introduce `Real.log` / `Real.rpow` unless a tiny local lemma is genuinely necessary for a required Phase-H theorem. It should not be necessary.

In particular, do not attempt to prove a global identity like

```text
x = product p^(k * v_p(n))
```

in this phase. That analytic reconstruction belongs to a later bounded phase after the structural scale kernel is stable.

Also do not:

- define nonzero reals as prime-factorization objects;
- call arbitrary real powers “ring-theoretic primes”;
- refactor KUS;
- modify completed FLT5 modules;
- create a generic projective-space or ray quotient hierarchy;
- identify PowerGauge projection with radial scaling;
- identify Golden fifth-power sectors with radial scaling.

Scaling, transport/rebase, and projection remain distinct operations.

---

## 11. Interaction with PowerGauge — keep operations distinct

Phase A/B already formalize:

```text
project / quotient:
  exponent e -> e % d
```

Phase H adds:

```text
radial scale:
  real coordinate a -> k*a
```

These do not generally commute in any meaningful direct sense because `% d` is defined on natural exponent coordinates while radial scaling is real-valued.

Do not force a theorem connecting them by coercions.

The correct architecture is:

```text
Nat raw prime valuations
        |
        +---- PowerGauge projection ----> Nat residue coordinates
        |
        `---- cast to ℝ ----> real raw coordinates ----> radial scaling
```

Both operations consume the same conceptual source direction but produce different observations.

---

## 12. Verification requirements

At minimum, after implementation run:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.RadialScaling
lake build DkMath.NumberTheory.StructuralArithmetic
```

If the actual module name differs, use the correct target.

Also rerun directly affected dependencies as appropriate, especially:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic.KUSObservation
```

Run:

```bash
git diff --check
```

Audit the new source:

```bash
rg -n "sorry|admit|axiom|unsafe" DkMath/NumberTheory/StructuralArithmetic/<new-module>.lean
```

Use `#print axioms` on the load-bearing support-preservation theorem and the prime-coordinate specialization. No new project-specific axiom is acceptable.

Pre-existing transitive warnings are not Phase-H failures, but report them accurately.

---

## 13. Documentation requirements

Update:

```text
docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md
```

Add Phase H as completed only after focused builds succeed.

The README must state clearly:

```text
radial scaling != KUS ScaleSpec transport
radial scaling != PowerGauge projection
nonzero radial scaling preserves coordinate zero-pattern/support
```

Add an implementation report, suggested name:

```text
DHNT-RADIAL-SCALING-IMPLEMENTATION-REPORT-260820.md
```

Record:

- baseline HEAD;
- exact representation chosen;
- theorem list;
- how prime coordinates are reused;
- whether `Function.support` or a custom zero-pattern relation was used;
- why no `Real.log` / `Real.rpow` reconstruction was attempted;
- build results;
- axiom audit;
- next bounded gap.

Update the public aggregate:

```text
DkMath/NumberTheory/StructuralArithmetic.lean
```

only after the new module is stable and build-checked.

---

## 14. Success criteria

Phase H is complete only if all of the following are true:

1. A distinct radial coordinate-scaling API exists.
2. Identity, zero, and composition laws are exposed at useful theorem level.
3. For nonzero scale, zero-pattern/support preservation is formally proved.
4. Existing `primeExponentCoordinates` are reused and embedded into the real-valued coordinate view.
5. The prime-coordinate radial specialization inherits support preservation.
6. A theorem states that pure nonzero radial scaling cannot equal a target that erases a nonzero source coordinate.
7. KUS `ScaleSpec` is documented as a separate typed transport/rebase operation; no false equivalence is introduced.
8. PowerGauge projection remains separate.
9. No real-prime-factorization claim is introduced.
10. No unnecessary `Real.log` / `Real.rpow` analytic reconstruction is introduced.
11. New public declarations have Lean docstrings.
12. Focused builds and aggregate build pass.
13. `git diff --check` passes.
14. No new `sorry`, `admit`, `axiom`, or `unsafe` appears in new source.
15. README and implementation report reflect the actual compiled state.

A module containing only a scalar-multiplication definition without the zero-pattern theorem is **not** sufficient.

A prose-only statement that scaling differs from rebasing is **not** sufficient.

At least one theorem must make support preservation / support-loss impossibility explicit.

---

## 15. Autonomous decision rule

After repository inspection, choose the smallest implementation that closes the contract above.

If an equivalent radial-scaling/support theorem already exists elsewhere in DkMath or Mathlib:

- reuse it;
- add only the thin StructuralArithmetic bridge;
- do not duplicate it.

If `Function.support` is awkward but a pointwise zero-pattern theorem is clean:

- prefer the clean theorem;
- add the minimum relation needed to state whole-vector support preservation.

If a generic scalar type causes typeclass friction:

- specialize to `ℝ`.

If a concrete `30` versus `6` prime-coordinate theorem is cheap:

- add it as a useful witness.

If it is not cheap:

- do not stall; the generic support-difference theorem closes the conceptual gap.

Do not ask for approval between routine implementation steps. Investigate, implement, build, document, commit, and push the completed Phase-H checkpoint to the current working branch.

Do **not** merge to `develop` and do **not** open a PR unless explicitly requested later.

---

## 16. Expected conceptual result

After Phase H, the StructuralArithmetic vocabulary should support all three distinct operations:

```text
RAW STRUCTURE
    |
    +---- transport / rebase ----> RAW STRUCTURE'
    |       KUS ScaleSpec / explicit compatibility
    |
    +---- radial scale ----------> REAL COORDINATE RAY
    |       k * v, support preserved when k != 0
    |
    `---- project ---------------> LOSSY PERIOD VIEW
            exponent mod d
```

Together with the completed A--G bridges, this gives the intended separation:

```text
preserve / transport
observe
project / coarsen
primitive-direction escape
GN / GN5 specialization
golden fifth-power gauge
radial scaling
```

The next phase, only after this compiles, may introduce the analytic DHNT/Cosmic Formula scaling example using `Real.log` and `Real.rpow`.
