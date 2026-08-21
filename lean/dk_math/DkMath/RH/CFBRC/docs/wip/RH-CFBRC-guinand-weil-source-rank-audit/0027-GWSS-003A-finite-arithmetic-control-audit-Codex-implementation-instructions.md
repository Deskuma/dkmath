# GWSS-003A finite arithmetic control audit — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only after GWSS-002D has been corrected and closed.

Trusted frontier:

```text
GWSS-001
  canonical Mellin source rank CLOSED

GWSS-002
  exact off-critical Mellin detector CLOSED

current missing bridge
  MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP
```

Implement and audit only the first bounded GWSS-003 stage:

```text
GWSS-003A-1  substitute the corrected admissible Mellin witness into the existing finite arithmetic explicit formula
GWSS-003A-2  expose the exact finite arithmetic RHS and its phase forced by the off-critical detector
GWSS-003A-3  prove finite-linearity bridges needed to see how the synthesized witness propagates through the arithmetic surface
GWSS-003A-4  audit existing independent control for prime / archimedean / elementary / top-horizontal terms
GWSS-003A-5  classify the exact next analytic/control gap without importing zero-side information back into the provider
```

Do **not** start:

```text
GWSS-004 classical Guinand--Weil infrastructure
T -> infinity horizontal-term removal
new zero-avoidance-height theory
new Xi growth theory
Weil positivity
Li criterion
RH deduction
DkReal shrinking-window uniqueness
new source-rank construction
```

This assignment is primarily an **arithmetic-independence audit**.  Do not turn it into a large analytic development merely because one term lacks a bound.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0024 corrected report read
0025 correction instructions read
0026 correction report read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
PascalCenteredXiFiniteArithmeticExplicitFormula.lean read
PascalCenteredXiExplicitFormulaHorizontalPairing.lean read
global objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-003A
```

Load-bearing provider boundary:

```text
Zero-side fact already established:
  an off-critical actual centered zero yields a target-dependent admissible
  finite Mellin witness h with

  zeroMoment(h)
    = ((z^2).im : ℂ) * orbitMass(z^2)
    != 0.

Independent arithmetic control must come from the arithmetic / contour side
for the already-constructed admissible h.  It must not be obtained by rewriting
that same nonzero zeroMoment through the explicit formula and then reading the
result back as a new provider.
```

Forbidden providers:

```text
RH
classical Weil positivity
Li criterion
functional-equation reflection as a new source
criticalMirror / conjugation as a new source
fixed-Xi defect vanishing
unproved T -> infinity horizontal decay
unproved exchange of limits
reverse Cauchy--Schwarz / reverse triangle / Gram positivity
an arithmetic bound whose proof simply rewrites the already-known zero-side moment
```

## 2. Existing finite arithmetic surface that must be preserved

For every differentiable even `h` and residue transport window `W`, the repository already proves the exact finite identity

```text
-(2*pi*i) * zeroMoment(h, W.R)
  = 2 * ordinary-zeta-right-edge(h)
  + 2 * archimedean-right-edge(h)
  + 2 * elementary-right-edge(h)
  + 2 * top-horizontal(h).
```

The specialized Mellin module also proves, for fixed `ε > 0`, `τ`, and `W`, arithmetic cutoff convergence as `X -> infinity` and an exact finite von Mangoldt expansion.

Preserve the following distinctions:

```text
X -> infinity at fixed finite residue window: already proved
T -> infinity: not proved
weight-only decay: not full horizontal-integrand decay
same-zero-set fixed R window: cannot automatically be extended to arbitrary T
```

The top-horizontal contribution remains part of every finite identity in this assignment.

## 3. GWSS-003A-1 — exact witness substitution

### A1. General synthesized-witness finite formula

For the existing

```lean
pascalCenteredXiMellinWitnessWeight ε τ c
```

prove a focused theorem applying the generic finite explicit formula.

Preferred semantic shape:

```lean
theorem pascalCenteredXiMellinWitnessFiniteExplicitFormula
    {ε : ℝ} (hε : 0 < ε)
    (τ : Fin n -> ℝ) (c : Fin n -> ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c) W.R =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution
          (pascalCenteredXiMellinWitnessWeight ε τ c)
          W.toContourTransportWindow := by
  ...
```

Use only the already-proved differentiability/evenness of the synthesized witness plus the generic finite formula.

Do not reprove the contour formula.

### A2. Named finite arithmetic RHS

If useful, define one small name for the four-term finite RHS, for example:

```lean
noncomputable def pascalCenteredXiFiniteArithmeticRHS
    (h : ℂ -> ℂ) (W : PascalCenteredXiResidueTransportWindow) : ℂ :=
  ...
```

or a witness-specialized variant.

This is optional, but a named RHS is encouraged if it makes the phase/control audit precise.

Do not hide or combine away the top-horizontal term in the definition.

## 4. GWSS-003A-2 — exact phase forced by the corrected detector

For the corrected global witness from GWSS-002, the zero-side value is

```text
D := ((z^2).im : ℂ) * orbitMass(z^2).
```

Both factors are real-valued after the natural cast and `D != 0` for the off-critical target.

Therefore the finite arithmetic RHS is exactly

```text
-(2*pi*i) * D.
```

Expose the most useful exact consequence.

Preferred theorem package, if compact:

```text
RHS = -(2*pi*i) * D
RHS.re = 0
RHS.im != 0
```

Equivalent normalization is acceptable.

The purpose is **not** to claim an arithmetic contradiction.  The purpose is to identify the precise phase that any independent arithmetic-control theorem would have to exclude.

Important firewall:

```text
A theorem `RHS.im != 0` proved by rewriting the zero-side detector through the
explicit formula is NOT independent arithmetic control.  It is only a
bookkeeping consequence of the already-known zero-side witness.
```

Document that distinction in the module and report.

## 5. GWSS-003A-3 — finite linearity of the synthesized witness

The witness is a finite linear combination

```text
h = sum_i c_i * H_{ε,τ_i}.
```

Audit whether the current API already makes each finite arithmetic term visibly linear in `h`.

At minimum try to prove compact bridges of the form

```text
ordinaryZeta(witness) = sum_i c_i * ordinaryZeta(H_i)
archimedean(witness) = sum_i c_i * archimedean(H_i)
elementary(witness) = sum_i c_i * elementary(H_i)
topHorizontal(witness) = sum_i c_i * topHorizontal(H_i)
```

and/or the combined statement

```text
finiteArithmeticRHS(witness)
  = sum_i c_i * finiteArithmeticRHS(H_i).
```

For the cutoff approximant, a compact theorem of the form

```text
finiteArithmeticApproximant(witness, X)
  = sum_i c_i * MellinFiniteArithmeticApproximant(ε, τ_i, X)
```

is useful if it closes by finite-sum/integral linearity without broad new infrastructure.

This finite-linearity audit serves two purposes:

1. it confirms that the synthesized witness introduces no hidden new arithmetic source;
2. it exposes exactly where target-dependent coefficients `c` enter any future estimate.

### Bounded stop rule

If one of the individual linearity lemmas is awkward only because of interval-integral API details, prefer a combined RHS theorem or document the omitted convenience lemma.  Do not spend the assignment building a general functional-linear-algebra framework.

## 6. GWSS-003A-4 — independent-control inventory

This section is mandatory even if no new estimate is proved.

Search the repository for existing theorems that control, for arbitrary differentiable/even weights or for the canonical Mellin family, any of:

```text
prime / von-Mangoldt cutoff term
ordinary-zeta right-edge integral
archimedean correction
 elementary correction
top-horizontal contribution
combined four-term RHS
```

For every candidate, record:

```text
exact theorem name
hypotheses
whether it is finite-height or asymptotic
whether it is a norm bound, sign theorem, phase theorem, vanishing theorem, or mere identity
whether it depends on zero data / same-zero-set window / functional-equation transport
whether it is strong enough to contradict RHS = -(2*pi*i) * D with D != 0
```

Do not count the following as independent arithmetic control:

```text
the finite explicit formula identity itself
convergence to the zero-side endpoint when the endpoint is identified using the zero-side theorem
an eventual nonzero theorem deduced because the limit is the nonzero zero-side endpoint
carrier-dependent interpolation / inverse-matrix reconstruction
functional-equation reindexing
```

## 7. Mandatory top-horizontal audit

The existing horizontal-pairing module explicitly states:

```text
weight-only decay is not decay of the Xi-weighted horizontal integrand
```

and contains the fixed-window localization obstruction showing that a same-zero-set fixed `R` window cannot automatically be transported to arbitrary heights.

Therefore classify separately whether the repository currently has any theorem giving one of:

```text
A. exact top-horizontal vanishing at the existing finite W
B. a finite bound with a useful phase/sign consequence
C. a T -> infinity decay theorem for the full weighted Xi horizontal integrand
D. zero-avoidance heights plus Xi growth sufficient to prove C
```

If none exists, say so explicitly.

Do not infer C from the existing `PascalCenteredXiMellinWeightVerticalDecayProvider`; that provider concerns the weight only.

## 8. Target-dependent coefficient audit

The coefficients `c` are obtained from a row of the inverse actual-window Mellin matrix and scaled by the target factor `q0.im`.

Any quantitative arithmetic estimate that contains quantities such as

```text
sum_i |c_i|
max_i |c_i|
||H^{-1}||
condition number of the evaluation matrix
selected τ_i
selected ε
```

must be classified carefully.

A bound is still independent in principle if it is a theorem uniform for arbitrary parameters and is proved entirely on the arithmetic/analytic side.  However, it is not yet useful for RH unless it combines with the detector lower side strongly enough to exclude every nonzero horizontal displacement.

In particular, do not silently assume:

```text
uniform boundedness of inverse-matrix coefficients
uniform separation of actual squared orbits
uniform lower bound on |q0.im|
uniform conditioning of the Mellin evaluation matrix
```

If the first genuinely missing theorem is such a quantitative conditioning/control statement, classify it precisely rather than calling it a generic arithmetic gap.

## 9. Minimal contradiction-provider audit

At the end of the assignment, state what additional theorem would actually contradict an off-critical witness.

Examples of semantically sufficient provider shapes include, depending on the exact phase normalization:

```text
finiteArithmeticRHS(witness, W).im = 0
```

or

```text
finiteArithmeticRHS(witness, W) = 0
```

or a quantitative estimate forcing the RHS to zero in a justified limit while the detector remains fixed nonzero.

Do **not** assert that any such provider is true.

For each plausible provider shape, classify whether current evidence says:

```text
AVAILABLE
MISSING
REQUIRES-TOP-HORIZONTAL-CONTROL
REQUIRES-TARGET-COEFFICIENT-CONTROL
REQUIRES-NEW-PRIME-SIDE-SIGN/PHASE-THEOREM
RH-EQUIVALENT / WEIL-POSITIVITY-EQUIVALENT
UNRESOLVED
```

If proving the provider would immediately imply the relevant off-critical exclusion through the already-established exact explicit formula, that alone does not make it circular; however, if the only known justification for the provider is RH/Weil positivity or the zero-side detector itself, classify it as unavailable.

## 10. Preferred focused Lean output

Prefer one focused audit module such as:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessArithmeticControlAudit.lean
```

The module should contain only compact exact identities / linearity / phase lemmas that are genuinely useful for locating the control boundary.

Do not create a chain of analytic modules in this assignment.

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0028-GWSS-003A-finite-arithmetic-control-audit-report.md
```

## 11. Success / stop classifications

End with exactly one primary classification from this list:

```text
MELLIN-WITNESS-INDEPENDENT-ARITHMETIC-CONTROL-FOUND
MELLIN-WITNESS-FINITE-ARITHMETIC-IDENTITY-FOUND-CONTROL-GAP
TOP-HORIZONTAL-CONTROL-GAP
TARGET-DEPENDENT-COEFFICIENT-CONTROL-GAP
PRIME-SIDE-SIGN-PHASE-CONTROL-GAP
RH-EQUIVALENT-PROVIDER
GWSS-003A-IMPLEMENTATION-API-GAP
```

Guidance:

- Use `MELLIN-WITNESS-INDEPENDENT-ARITHMETIC-CONTROL-FOUND` only if an already-proved or newly short, unconditional arithmetic/analytic theorem excludes the nonzero detector without reusing the zero-side conclusion.
- Use `MELLIN-WITNESS-FINITE-ARITHMETIC-IDENTITY-FOUND-CONTROL-GAP` if exact substitution/phase/linearity are closed but no single sharper obstruction has yet been isolated.
- Use one of the more specific `...-GAP` classifications if the audit identifies one first load-bearing missing theorem.
- Use `RH-EQUIVALENT-PROVIDER` only after tracing an apparently sufficient provider to RH, Weil positivity, Li, or an equivalent assumption; do not use it merely because the theorem would be powerful.

GWSS-004 remains unauthorized in every outcome except that the report may recommend it as the next stage if and only if this audit identifies a precise classical Guinand--Weil fragment as the minimal missing theorem.

## 12. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessArithmeticControlAudit
git diff --check
```

Inspect `#print axioms` for all load-bearing public theorems.

Requirements:

```text
NO sorry
NO admit
NO native_decide proof shortcut
NO new axiom
```

Expected axiom footprint remains the standard branch set:

```text
propext
Classical.choice
Quot.sound
```

Report any deviation.

## 13. Mandatory report orientation

The 0028 report must state explicitly:

```text
global objective
current GWSS stage
load-bearing provider boundary
exact witness arithmetic identity status
phase theorem status
finite-linearity status
prime/von-Mangoldt control status
archimedean control status
elementary control status
top-horizontal control status
target-dependent coefficient/conditioning status
whether any claimed control is independent of the zero-side witness
primary classification
next unresolved Gap
GWSS-004 authorization status
verification
```

If the result is only an identity plus an inventory of missing controls, say exactly that.  Do not upgrade an identity into an arithmetic provider.
