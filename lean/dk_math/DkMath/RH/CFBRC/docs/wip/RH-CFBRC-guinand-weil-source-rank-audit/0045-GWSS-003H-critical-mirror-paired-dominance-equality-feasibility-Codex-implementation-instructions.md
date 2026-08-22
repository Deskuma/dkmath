# GWSS-003H critical-mirror paired dominance/equality feasibility audit — Codex implementation instructions

Date: 2026-08-22
Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`
Predecessor: `0044-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-report.md`

## 0. Mission

GWSS-003G closed the actual finite shifted-energy representation layer and established the exact readouts

```text
E1+ - E1- = 4 * WholeSource.re = 2 * FiniteApprox.im
EI+ - EI- = 4 * WholeSource.im = -2 * FiniteApprox.re
```

for the exact synthesized nonzero-`tau` whole feature, together with `q.im`-linear transport of both shifted-energy differences.

Its final classification was

```text
ACTUAL-SHIFTED-ENERGY-POLARIZATION-FOUND-DOMINANCE-GAP
```

The next bounded question is **not** to search blindly for another positivity theorem.

Instead audit whether the centered critical-mirror symmetry supplies a paired sign reversal at the level of the **actual target-dependent finite witness**, and whether a same-orientation P1 dominance statement on a mirror pair would collapse to P2 equality.

The main danger is a false identification:

```text
original target coefficients = q.im * c0
mirror target coefficients   = -q.im * c0
```

This is NOT currently established. The mirror squared orbit can occupy a different `Fin` index, and its Mellin inverse extractor row can differ. GWSS-003H must audit this relation rather than assume it.

Do not start GWSS-004, classical Guinand--Weil, Weil positivity, Li criterion, an infinite-height argument, or an RH deduction.

## 1. Required existing files to inspect first

At minimum inspect:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinOffCriticalWitnessAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
```

Also search the full `DkMath/RH/CFBRC` tree for existing declarations concerning:

```text
critical mirror
1 - conjugate
-conj
conjugate zero
centered zero symmetry
zero-disk closure
zero multiplicity under conjugation / functional equation
squared-orbit conjugation
orbit mass conjugation
Mellin weight conjugation
Mellin evaluation matrix conjugation
inverse row / coordinate extractor
```

Reuse existing APIs whenever possible. Do not create a parallel mirror vocabulary if one already exists.

## 2. Stage H1 — exact centered mirror geometry

Identify the exact centered critical-mirror map already used by the project. If the existing project convention is the expected centered map

```text
z ↦ -conj z
```

then prove or reuse the finite algebraic identities needed below. If the project uses a differently named but equivalent map, follow the existing convention.

Target geometry, stated without assuming any zero theorem:

```text
mirror(z)^2 = conj(z^2)
(mirror(z)^2).re = (z^2).re
(mirror(z)^2).im = -(z^2).im
```

Also record the elementary square identity already available from GWSS-002:

```text
(z^2).im = 2 * z.re * z.im
```

Do not treat these elementary identities as new source rank.

## 3. Stage H2 — actual finite zero-window mirror closure

Audit whether the current API proves that an actual centered Xi zero in the finite disk remains in the same finite disk under the centered critical mirror.

Desired shape, names flexible:

```text
z ∈ pascalCenteredXiZeroDiskFinset R
→ mirror z ∈ pascalCenteredXiZeroDiskFinset R
```

This must come from already-proved zeta/Xi zero symmetry plus radius preservation. Do not assume RH.

If the required zero-symmetry or multiplicity theorem is missing, stop this substage with a precise API gap and classify it. Do not prove a large new functional-equation framework here.

## 4. Stage H3 — squared-orbit conjugation closure

Assuming H2 is available, prove or reuse that an occupied squared orbit is closed under complex conjugation:

```text
q ∈ pascalCenteredXiSquaredOrbitFinset R
→ conj q ∈ pascalCenteredXiSquaredOrbitFinset R
```

Then establish existence of a mirror index for every actual squared-orbit index:

```text
∀ j,
  ∃ jMirror,
    pascalCenteredXiSquaredOrbitCoordinate R jMirror =
      conj (pascalCenteredXiSquaredOrbitCoordinate R j)
```

Do not require a canonical involution on `Fin` unless it is naturally easy to construct from the existing finite equivalence. Existence is enough for this audit.

If a canonical involution is implemented, verify the twofold property only from injectivity of the coordinate presentation:

```text
mirrorIndex (mirrorIndex j) = j
```

No arbitrary `Classical.choose` equality may be used as mathematical content unless its choice-independence is explicitly proved.

## 5. Stage H4 — orbit mass under the mirror

Audit the exact relation between

```text
pascalCenteredXiSquaredOrbitMass R q
pascalCenteredXiSquaredOrbitMass R (conj q)
```

The expected relation is equality because the centered zero multiset should be stable under the critical mirror and multiplicity should be preserved, but this is **not authorized as an assumption**.

Preferred theorem shape:

```text
pascalCenteredXiSquaredOrbitMass R (conj q) =
  pascalCenteredXiSquaredOrbitMass R q
```

for occupied actual orbits, or an equivalent `MassVec` statement after choosing `jMirror`.

A proof must explicitly account for the filtered zero fibers and multiplicity preservation. Do not silently replace a fiber by a two-element set; the existing mass definition intentionally does not assume exactly two representatives.

If multiplicity preservation under the mirror is absent from the current API, classify the exact missing theorem and stop this substage rather than introducing a broad analytic detour.

## 6. Stage H5 — Mellin evaluation/extractor mirror relation

This is the load-bearing feasibility test.

Recall the actual evaluation matrix

```text
H i j = pascalCenteredXiMellinSecondDifferenceWeight ε (tau i)
          (pascalCenteredXiSquaredOrbitRepresentativeFin R j)
```

and the coordinate extractor row used by GWSS-002.

First audit the scalar kernel relation under centered critical mirror / conjugation. For real `ε` and real `tau`, determine the exact theorem actually true for the current Mellin second-difference weight, for example one of:

```text
w (mirror z) = w z
w (mirror z) = conj (w z)
w (conj z) = conj (w z)
```

Do not guess which relation holds. Prove the exact relation from the definition.

Then determine whether the mirror target column is related to the original target column by equality, conjugation, or only by a permutation/conjugation combination.

Next inspect the extractor implementation. `exists_matrix_coordinate_extractor` currently proves existence by using the inverse row. A mirror-target relation is not allowed to rely on unspecified existential choices.

If useful, introduce a small canonical helper such as the actual inverse row

```text
extractorRow H j i := H⁻¹ j i
```

and prove its coordinate extraction theorem under `det H ≠ 0`.

Only then audit whether a theorem of one of these strengths is available:

```text
extractorRow H jMirror = extractorRow H j
extractorRow H jMirror = fun i => conj (extractorRow H j i)
extractorRow H jMirror = explicit permutation/conjugation transform of extractorRow H j
```

If no such relation follows from the actual matrix symmetry, say so precisely.

## 7. Stage H6 — actual off-critical coefficient-row mirror transport

Let `q_j` denote the squared-orbit coordinate and let the GWSS-002 off-critical row be conceptually

```text
cOff(j) = q_j.im * extractorRow(j)
```

with the scalar interpreted in `ℂ` as in the existing code.

For a mirror index `jMirror` satisfying

```text
q_jMirror = conj q_j
```

we automatically have

```text
q_jMirror.im = - q_j.im
```

but that alone is insufficient.

Derive the **exact** coefficient relation that the actual extractor symmetry permits. Possible outcomes include:

```text
cOff(jMirror) = -cOff(j)
```

or

```text
cOff(jMirror) = -conj(cOff(j))
```

or a permutation/conjugation variant, or no usable relation.

Do not force the first form if the matrix only gives the second.

## 8. Stage H7 — whole-feature / shifted-difference mirror transport

Only after H6 is established, transport the exact coefficient relation through the already-proved finite linear APIs.

The target is an exact theorem relating the 003G shifted-energy differences for mirror-target synthesized witnesses.

Define audit abbreviations locally if they improve readability:

```text
D1(c) := E1Plus(c) - E1Minus(c)
DI(c) := EIPlus(c) - EIMinus(c)
```

Determine what is actually provable for the mirror coefficient row. Candidate forms:

```text
D1(cMirror) = -D1(c)
DI(cMirror) = -DI(c)
```

or a channel-swapping / conjugation-derived relation such as

```text
D1(cMirror) = ± D1(c)
DI(cMirror) = ± DI(c)
```

with signs established exactly from the WholeSource / FiniteApprox transformation.

Do not infer energy-difference sign reversal merely from `q.im` sign reversal unless the base extractor/source feature has first been identified on the same object.

## 9. Stage H8 — paired P1 ⇒ P2 collapse theorem

If H7 produces a genuine odd mirror relation

```text
D(cMirror) = -D(c)
```

prove the purely ordered-algebra consequence:

```text
0 ≤ D(c)
→ 0 ≤ D(cMirror)
→ D(c) = 0
```

or equivalently with the actual shifted-energy order statements:

```text
EMinus(c) ≤ EPlus(c)
→ EMinus(cMirror) ≤ EPlus(cMirror)
→ EMinus(c) = EPlus(c)
```

This theorem is **conditional on paired P1 hypotheses**. It is not itself a P1 provider.

If both `1` and `I` channels have the needed odd relation, record the two-channel collapse separately.

Do not claim that P0 nonnegativity of individual energies supplies these P1 hypotheses.

## 10. Stage H9 — detector consequence and same-object firewall

If a paired P1 collapse reaches

```text
D1(cOff(j)) = 0
```

or

```text
DI(cOff(j)) = 0
```

use the exact 003G readout to identify what finite arithmetic coordinate vanishes.

Then audit whether this is enough to imply vanishing of the original GWSS-002 off-critical detector

```text
q_j.im * pascalCenteredXiSquaredOrbitMassVec R j
```

on the **same finite object**.

This is not automatic.

In particular, keep separate:

```text
pascalCenteredXiFiniteArithmeticApproximant ... W X
```

and

```text
pascalCenteredXiFiniteArithmeticRHS ... W
```

The existing exact zero-moment / mass identity for the full finite arithmetic RHS must not be substituted for a finite-`X` approximant without an already-proved equality.

Explicitly classify whether the current API provides a finite-`X` same-object bridge strong enough to combine:

```text
paired P1 collapse
+ 003G finite approximant readout
+ GWSS-002 nonzero orbit detector
```

to force `q_j.im = 0`.

If not, identify the minimal missing theorem shape. Do not cross an unproved `X → ∞` limit.

## 11. Required firewalls

### Firewall A — no coefficient-universal positivity illusion

Because WholeSource and the shifted-energy differences are first-order in coefficient scaling, a theorem claiming the same sign for every coefficient row is immediately suspect under `c ↦ -c`.

If a proposed P1 provider is coefficient-universal, explicitly test it against `-c`. If it implies both `D(c) ≥ 0` and `-D(c) ≥ 0`, classify it as an equality-only statement, not independent positivity.

### Firewall B — mirror index is not the same index by default

Never rewrite `jMirror = j` unless the squared coordinate is actually real and injectivity proves it.

For an off-axis squared orbit, `q` and `conj q` are generally distinct.

### Firewall C — existential extractor choices are not canonical

A relation between two `∃ c, ...` witnesses does not follow from existence alone. Use the actual inverse-row construction or prove choice-independence.

### Firewall D — P0 ≠ P1

The four 003G energies are nonnegative individually. This does not order a plus/minus pair.

### Firewall E — no RH-equivalent assumptions

Do not import or assume:

```text
RiemannHypothesis
Li criterion positivity
full Weil positivity criterion
an RH-equivalent raw-ratio boundedness hypothesis
all-zero critical-line assumption
```

### Firewall F — finite stage only

No new theorem may require an unproved exchange or passage involving:

```text
T → ∞
X → ∞
epsilon → 0
```

### Firewall G — no symmetry-as-independent-rank claim

Critical-mirror, conjugation, functional-equation, and index-permutation transports do not by themselves create independent source rank. They are symmetry constraints. Label them accordingly.

## 12. Preferred implementation structure

If the audit produces enough finite theorems to justify a new module, prefer a focused module such as

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessCriticalMirrorPairAudit.lean
```

Keep helper lemmas local/private unless they clearly form reusable public API.

If the audit stops at an API gap before meaningful new Lean declarations exist, a report-only result is acceptable. Do not manufacture a large module merely to satisfy the stage number.

## 13. Required classifications

End the report with exactly one primary classification from the following list, adding a secondary classification if useful:

```text
MIRROR-PAIRED-SHIFTED-DIFFERENCE-ODDNESS-FOUND
MIRROR-PAIRED-P1-COLLAPSES-TO-P2-EQUALITY
MIRROR-ORBIT-MASS-API-GAP
MIRROR-EXTRACTOR-ROW-RELATION-GAP
MIRROR-WHOLE-FEATURE-TRANSPORT-GAP
PAIRED-EQUALITY-FOUND-FINITE-DETECTOR-BRIDGE-GAP
PAIRED-EQUALITY-FOUND-OFF-CRITICAL-EXCLUSION-FINITE
MIRROR-SYMMETRY-NOT-INDEPENDENT-PROVIDER
```

`PAIRED-EQUALITY-FOUND-OFF-CRITICAL-EXCLUSION-FINITE` is authorized only if the exact same finite object chain really forces the GWSS-002 nonzero detector to vanish with no hidden limit or RH-equivalent assumption.

If the mirror relation is weaker than oddness, state the exact relation and classify the first failing layer.

## 14. Expected report

Create:

```text
0046-GWSS-003H-critical-mirror-paired-dominance-equality-feasibility-report.md
```

The report must include:

1. branch and starting HEAD;
2. files changed;
3. exact centered mirror convention used;
4. zero-window mirror closure status;
5. squared-orbit conjugation status;
6. orbit-mass relation status;
7. canonical/existential extractor distinction;
8. exact coefficient-row mirror relation;
9. exact WholeSource / FiniteApprox / shifted-difference mirror relation;
10. whether paired P1 collapses to P2;
11. same-object finite detector bridge status;
12. primary classification;
13. focused build and `git diff --check` results;
14. axiom audit for load-bearing new declarations;
15. explicit statement that GWSS-004 was not started.

## 15. Verification

Run at minimum:

```text
lake env lean DkMath/RH/CFBRC/<new-focused-module>.lean

git diff --check
```

If no new module is created, build the nearest load-bearing existing module touched by the audit.

Audit load-bearing theorem axioms with `#print axioms` or the project-standard equivalent. The acceptable standard baseline is the usual Mathlib logical axioms already seen in previous stages; report anything stronger explicitly.

No `sorry`, `admit`, `native_decide`, or new axiom.

## 16. Decision rule after GWSS-003H

Do not automatically proceed to full Guinand--Weil after this audit.

The next stage depends on the first genuine gap found:

- if mirror oddness itself fails because extractor/source transport is absent, isolate that finite algebraic/API problem;
- if mirror oddness and paired P1⇒P2 are closed but no P1 provider exists, the remaining need is a **minimal source-derived paired P1 theorem**, not generic positivity;
- if paired equality is obtained but finite approximant cannot connect to the nonzero orbit detector, isolate the **same-object finite detector bridge**;
- only if the current finite API is exhausted and the missing provider is demonstrably a bounded classical explicit-formula positivity fragment should a GWSS-004 preflight be considered.

The purpose of GWSS-003H is to determine which of these boundaries is real before importing any larger classical theory.
