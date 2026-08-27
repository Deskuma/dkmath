# GWSS-003H2 critical-mirror multiplicity / orbit-mass closure — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0046-GWSS-003H-critical-mirror-paired-dominance-equality-feasibility-report.md`

## 0. Mission

GWSS-003H closed the finite geometric part of the critical-mirror audit:

```text
centered mirror z ↦ -conj z
zero-disk closure
squared-orbit conjugation q ↦ conj q
existential mirror Fin index
exact filtered zero-fibre image
```

and stopped at the first weighted obstruction:

```text
MIRROR-ORBIT-MASS-API-GAP
```

The current squared-orbit mass is multiplicity weighted:

```text
pascalCenteredXiSquaredOrbitMass R q
  = ∑ z in (pascalCenteredXiZeroDiskFinset R).filter (fun z => z ^ 2 = q),
      (pascalCenteredXiZeroMultiplicity z : ℂ)
```

The missing finite theorem is therefore not another carrier bijection. It is multiplicity preservation under the centered critical mirror:

```text
pascalCenteredXiZeroMultiplicity (pascalCenteredXiCriticalMirror z)
  = pascalCenteredXiZeroMultiplicity z
```

for actual centered Xi zeros.

GWSS-003H2 must close only this local analytic-order transport and, if successful, immediately discharge the conjugate-orbit mass equality. Stop there.

Do not proceed to extractor-row transport, coefficient-row oddness, shifted-energy oddness, P1, GWSS-004, classical Guinand--Weil, Weil positivity, Li criterion, infinite height, or an RH deduction.

## 1. Required files to inspect first

Read the current branch versions of at least:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMultiplicityLocalChargeBridge.lean
DkMath/RH/CFBRC/PascalZetaZeroMultiplicityBridge.lean
DkMath/RH/CFBRC/CriticalMirrorZeroBridge.lean
DkMath/RH/CFBRC/PascalCanonicalXiFixedObservableBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
```

Also inspect the pinned Mathlib APIs actually available in this checkout before choosing the proof route, especially:

```text
Mathlib.Analysis.Analytic.Order
Mathlib.Analysis.Calculus.Deriv.Star
Mathlib.NumberTheory.Harmonic.ZetaAsymp
```

Known useful existing ingredients include:

```text
analyticOrderAt_comp_of_deriv_ne_zero
riemannZeta_conj
criticalMirror_nontrivialRiemannZetaZero
pascalRiemannXiKernel_one_sub
pascalCenteredRiemannXiKernel_neg
pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
```

Do not assume a theorem such as `analyticOrderAt_conj_conj` exists in the pinned Mathlib. Search first. If absent, build the smallest local lemma needed from the analytic local-factorization API.

## 2. Mathematical target

For an actual centered zero `z`, write

```text
rho = criticalLineCenter + z
mirror z = -conj z
criticalMirror rho = criticalLineCenter + mirror z
```

The desired theorem is

```text
pascalCenteredXiZeroMultiplicity (pascalCenteredXiCriticalMirror z)
  = pascalCenteredXiZeroMultiplicity z
```

under a hypothesis such as

```text
z ∈ pascalCenteredXiZeros
```

or the stronger actual finite-window membership if that is more convenient.

Once this is available, combine it with the already proved exact fibre image

```text
image_pascalCenteredXiCriticalMirror_filter_sq
```

to prove

```text
pascalCenteredXiSquaredOrbitMass R (conj q)
  = pascalCenteredXiSquaredOrbitMass R q
```

at least for occupied `q`, and preferably for all `q : ℂ` if the finite-sum proof naturally gives the unconditional statement.

The all-`q` form is allowed because both sides are explicit finite sums and the fibre-image identity is already unconditional.

## 3. Preferred proof architecture

There are two acceptable routes. Use the shorter one that is supported by the pinned APIs.

### Route A — zeta multiplicity transport

This route reuses the established bridge

```text
pascalCenteredXiZeroMultiplicity_sub_center_eq_riemannZetaZeroMultiplicity
```

and proves critical-mirror invariance for `riemannZetaZeroMultiplicity`.

Suggested decomposition:

```text
rho
  ↦ 1 - rho
  ↦ conj (1 - rho) = criticalMirror rho
```

#### A1. Functional-equation reflection preserves analytic order

Prove a theorem of the shape

```text
riemannZetaZeroMultiplicity (1 - rho)
  = riemannZetaZeroMultiplicity rho
```

for a nontrivial zero `rho`.

Do not infer this merely from equality of zero predicates.

A valid route may pass through `completedRiemannZeta` or the fixed Xi kernel:

```text
analytic order of zeta at a nontrivial zero
  = analytic order of completed zeta
functional equation under s ↦ 1 - s
analyticOrderAt_comp_of_deriv_ne_zero for the affine involution
```

The affine map has derivative `-1`, hence nonzero.

If a direct already-proved order theorem exists, reuse it rather than rebuilding the functional equation layer.

#### A2. Conjugation preserves analytic order

Prove a theorem of the shape

```text
riemannZetaZeroMultiplicity (conj rho)
  = riemannZetaZeroMultiplicity rho
```

for the relevant nontrivial zeros.

Again, zero-set conjugation alone is insufficient.

Use the exact analytic symmetry

```text
riemannZeta (conj s) = conj (riemannZeta s)
```

and transport the local analytic factorization.

If the pinned Mathlib has a suitable generic analytic-order conjugation theorem, use it.

Otherwise prove a small local helper from the finite-order factorization:

```text
f(w) = (w - rho)^m * g(w)
```

near `rho`, then conjugate both input and output to obtain a factorization near `conj rho`:

```text
(conj ∘ f ∘ conj)(w)
  = (w - conj rho)^m * (conj ∘ g ∘ conj)(w)
```

with the transformed regular factor analytic and nonzero at `conj rho`.

Use the pinned star/conjugation calculus API to prove analyticity of the transformed regular factor. Do not treat raw `conj` as a holomorphic map by itself.

Then use `riemannZeta_conj` to identify the transformed function with `riemannZeta`.

#### A3. Compose the two invariances

Since

```text
criticalMirror rho = conj (1 - rho)
```

obtain

```text
riemannZetaZeroMultiplicity (criticalMirror rho)
  = riemannZetaZeroMultiplicity rho
```

and transport back to centered Xi multiplicity.

### Route B — centered Xi multiplicity directly

This is acceptable only if it is genuinely shorter.

The centered Xi kernel already satisfies

```text
pascalCenteredRiemannXiKernel (-z)
  = pascalCenteredRiemannXiKernel z
```

so negation-order invariance should be a direct use of
`analyticOrderAt_comp_of_deriv_ne_zero` with `z ↦ -z`.

For conjugation, however, an exact real-symmetry theorem for the fixed centered Xi kernel must first be proved from existing completed-zeta conjugation APIs. Do not assume it from real coefficients informally.

Only use this route if the required exact kernel conjugation identity is straightforward in the current API.

## 4. Required H4a theorem: point multiplicity preservation

Export a theorem with a clear project-level name, preferably one of these shapes:

```text
pascalCenteredXiZeroMultiplicity_criticalMirror
pascalCenteredXiZeroMultiplicity_pascalCenteredXiCriticalMirror
```

Suggested contract:

```lean
{z : ℂ} (hz : z ∈ pascalCenteredXiZeros) :
  pascalCenteredXiZeroMultiplicity (pascalCenteredXiCriticalMirror z) =
    pascalCenteredXiZeroMultiplicity z
```

If the proof naturally requires finite-window membership instead, that is acceptable, but prefer the global centered-zero statement because multiplicity is intrinsically local and the mirror zero theorem is global.

Also export any load-bearing zeta-level intermediate theorem if it is mathematically reusable, for example:

```text
riemannZetaZeroMultiplicity_criticalMirror
```

Do not expose large amounts of proof scaffolding unnecessarily.

## 5. Required H4b theorem: conjugate squared-orbit mass equality

Use the existing theorem

```text
image_pascalCenteredXiCriticalMirror_filter_sq
```

and point multiplicity preservation to prove the finite weighted-sum equality.

Target:

```lean
pascalCenteredXiSquaredOrbitMass R (conj q) =
  pascalCenteredXiSquaredOrbitMass R q
```

or its symmetric orientation.

The proof must use an actual finite-sum reindexing / image argument with injectivity of the mirror involution. Do not replace the fibre by an assumed two-point set.

Useful facts already proved:

```text
pascalCenteredXiCriticalMirror_involutive
pascalCenteredXiCriticalMirror_mem_zeroDiskFinset_iff
image_pascalCenteredXiCriticalMirror_filter_sq
```

Because the mirror is involutive, injectivity is immediate and can be packaged locally if needed.

## 6. Optional H4c theorem: mass-vector mirror transport

Only if H4b closes cleanly, add a bounded `Fin`-index corollary using the existing existential mirror index:

```text
exists_pascalCenteredXiSquaredOrbitMirrorIndex
```

Desired shape:

```text
∃ jMirror,
  pascalCenteredXiSquaredOrbitCoordinate R jMirror =
    conj (pascalCenteredXiSquaredOrbitCoordinate R j)
  ∧
  pascalCenteredXiSquaredOrbitMassVec R jMirror =
    pascalCenteredXiSquaredOrbitMassVec R j
```

This is only a mass-vector statement.

Do not infer any matrix-column symmetry, inverse-row relation, coefficient-row relation, or shifted-energy oddness from it in this stage.

## 7. Firewalls

### F1. Zero symmetry is not multiplicity symmetry

A theorem saying

```text
riemannZeta (criticalMirror rho) = 0
```

is not enough. The analytic order must be transported.

### F2. Conjugation is anti-holomorphic

Do not apply `analyticOrderAt_comp_of_deriv_ne_zero` directly to raw complex conjugation as though it were holomorphic.

The valid analytic object is of the form

```text
conj ∘ f ∘ conj
```

or an equivalent local power-series/factorization construction.

### F3. Do not assume simple zeros

No multiplicity-one assumption is allowed.

All theorems must preserve arbitrary positive analytic order.

### F4. Do not collapse the squared fibre

The fibre

```text
(zeroDisk R).filter (fun z => z ^ 2 = q)
```

may contain however many representatives the current finite model permits. Use the exact image theorem, not an informal `{z,-z}` description.

### F5. No P0/P1/P2 source claim

Mass equality is a symmetry transport, not a positivity provider and not an independent source rank.

### F6. No extractor work yet

Even after mass equality is closed, stop before H5.

In particular do not prove or assume:

```text
mirror inverse row = original row
mirror coefficient row = - original row
mirror shifted-energy difference = - original difference
```

### F7. No asymptotics

No `T → ∞`, `X → ∞`, `ε → 0`, limit exchange, or finite-RHS/finite-approximant identification.

### F8. No RH-equivalent shortcut

No RH assumption, Li criterion, Weil positivity criterion, or equivalent off-critical exclusion theorem.

## 8. Classification

Use exactly one primary classification.

If point multiplicity and orbit mass both close:

```text
MIRROR-ORBIT-MASS-TRANSPORT-CLOSED
```

If zeta/centered multiplicity closes but the finite weighted-sum API itself blocks mass equality:

```text
MIRROR-MULTIPLICITY-CLOSED-FINITE-MASS-SUM-API-GAP
```

If the obstruction is specifically conjugation of analytic order:

```text
ANALYTIC-ORDER-CONJUGATION-API-GAP
```

If functional-equation reflection order cannot be transported with current APIs:

```text
FUNCTIONAL-EQUATION-MULTIPLICITY-TRANSPORT-GAP
```

If a more precise first load-bearing API gap is found, state it explicitly in the report and stop.

Secondary classification should remain:

```text
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

## 9. Verification

Run focused Lean verification on every new/modified load-bearing module.

At minimum:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
```

If multiplicity transport is implemented in a separate focused module, build that module directly as well.

Also run:

```text
git diff --check
```

Audit the main new declarations with `#print axioms`.

Required result:

```text
no sorry
no admit
no native_decide
no new axiom
```

Standard baseline axioms such as

```text
propext
Classical.choice
Quot.sound
```

are acceptable.

## 10. Implementation placement

Prefer one of these bounded approaches:

1. Extend `PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean` with H4 closure if the new proof is short and tightly local.
2. Create a focused module such as

```text
PascalCenteredXiCriticalMirrorMultiplicityTransportAudit.lean
```

and let `PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean` import it if the analytic-order proof needs substantial scaffolding.

Do not enlarge unrelated Mellin/source modules.

## 11. Required report

Create:

```text
0048-GWSS-003H2-critical-mirror-multiplicity-mass-closure-report.md
```

The report must state:

1. exact files changed;
2. whether the proof used zeta-level or centered-Xi-level multiplicity transport;
3. the exact analytic-order theorem(s) used or added;
4. whether conjugation transport required a new generic helper;
5. whether point multiplicity preservation closed;
6. whether squared-orbit mass equality closed;
7. whether the optional mass-vector mirror corollary closed;
8. first remaining gap after H4;
9. primary and secondary classification;
10. focused build, diff check, and axiom-audit results.

If `MIRROR-ORBIT-MASS-TRANSPORT-CLOSED` is achieved, explicitly stop before H5 and recommend the next bounded stage as an **Mellin matrix / extractor mirror transport audit**. Do not implement H5 in the same change.
