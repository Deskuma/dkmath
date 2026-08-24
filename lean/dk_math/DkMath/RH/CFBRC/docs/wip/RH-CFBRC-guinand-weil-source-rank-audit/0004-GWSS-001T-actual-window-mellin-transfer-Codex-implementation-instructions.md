# GWSS-001T actual-window / Mellin source-rank transfer — Codex implementation instructions

Date: 2026-08-20

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Implement and audit only the inserted transfer stage:

```text
GWSS-001T-A  actual finite Xi zero-window even-polynomial orbit separation
GWSS-001T-B  existing Mellin second-difference family transfer audit
```

Do **not** start GWSS-002 in this assignment.

GWSS-000 established:

```text
VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT
```

GWSS-001 established only:

```text
VARIABLE-WEIGHT-RANK-UNRESOLVED
```

The existing abstract countermodel proves that fixed quadratic/radial/horizontal observables do not determine every even weighted moment, but it is deliberately not a theorem about the actual Xi zero window.

This assignment closes exactly that transfer gap as far as the current finite API allows.

## 1. Mandatory orientation before editing

Before making changes, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
GWSS roadmap / reports read
global objective
current GWSS stage
load-bearing boundary
next unresolved Gap
```

The global objective remains:

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
GWSS-001T
```

Load-bearing boundary:

```text
NO classical Weil positivity
NO RH assumption
NO fixed-Xi defect vanishing provider
NO T -> infinity horizontal decay provider
NO limit exchange
NO prime-side sign assumption
NO claim that an abstract countermodel consists of actual zeta zeros
```

## 2. Trusted results — do not re-prove

Read and reuse the checked-out implementations of at least:

```text
DkMath.RH.CFBRC.PascalCenteredXiVariableWeightSourceRankAudit
DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
DkMath.Analysis.MellinMultiplicativeApproxIdentity
```

Also trace the exact definitions of:

```text
pascalCenteredXiZeroDiskFinset
pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiZeroMultiplicity
PascalCenteredEvenWeight
pascalCenteredXiMellinSecondDifferenceWeight
centeredMellinSpectralWeight
centeredMellinBoxApprox
```

Do not infer carrier symmetry or multiplicity behavior from names.

## 3. Critical mathematical distinction

The GWSS-001 countermodel proves only:

```text
fixed second-order observables
  do not recover
all even polynomial moments
```

It does **not** prove:

```text
existing Mellin second-difference family
  does not recover
all even polynomial moments.
```

In fact, for nonzero `τ`, the existing source exposes the exact pointwise factor

```text
(exp (τ z) - 2 + exp (-τ z)) / τ^2
```

multiplying the centered Mellin spectral weight.  Formally, its local expansion is expected to contain

```text
z^2
z^4
z^6
...
```

through the even `τ`-jet.

Therefore do not claim that `z^4` is independent of the full Mellin family merely because it is independent of fixed quadratic geometry.

This distinction is load-bearing.

# Part A — actual finite Xi zero-window transfer

## 4. Goal A

Move from the abstract two-orbit model to the **actual finite Xi zero carrier**.

For a fixed radius `R`, let the actual carrier be the checked-out finset underlying

```text
pascalCenteredXiZeroDiskWeightedMoment h R.
```

The desired theorem family should show that admissible even polynomials can isolate the actual carrier modulo the unavoidable symmetry

```text
z ~ -z.
```

Do not assume the finset is already quotiented by this relation.

## 5. Preferred construction: squared-orbit selector polynomial

For a finite carrier `S : Finset ℂ` and a target `z ∈ S`, use a finite even polynomial depending only on `w^2`.

A preferred unnormalized shape is

```text
U_{S,z}(w)
  = product over a in S with a^2 != z^2 of (w^2 - a^2).
```

Then prove on carrier points `w ∈ S`:

```text
w^2 != z^2  -> U_{S,z}(w) = 0
w^2 = z^2   -> U_{S,z}(w) = U_{S,z}(z)
U_{S,z}(z) != 0
```

Normalize only after the denominator nonvanishing theorem is available:

```text
L_{S,z}(w) = U_{S,z}(w) / U_{S,z}(z).
```

Expected carrier behavior:

```text
w ∈ S ->
  L_{S,z}(w) = 1  if w^2 = z^2
  L_{S,z}(w) = 0  if w^2 != z^2.
```

The selector must be proved:

```text
even
Differentiable ℂ
```

Do not introduce quotient types unless they materially simplify the proof.  The squared-orbit predicate is sufficient.

## 6. Keep the orbit statement exact

Over `ℂ`, if useful, prove or reuse the algebraic fact

```text
w^2 = z^2 <-> w = z or w = -z.
```

But the main actual-window theorem may remain phrased using equality of squares if that avoids unnecessary symmetry API work.

Do not assume that both `z` and `-z` occur in the actual carrier unless an existing Xi-zero symmetry theorem and radius invariance prove it.

## 7. Desired actual-window weighted-moment theorem

Specialize the selector to the actual Xi zero-disk finset and prove a theorem of the schematic form

```text
pascalCenteredXiZeroDiskWeightedMoment
    (actualSquaredOrbitSelector R z) R
  = sum over a in actual zero finset with a^2 = z^2
      (pascalCenteredXiZeroMultiplicity a : ℂ).
```

Exact names and casts must follow the repository API.

This theorem is the preferred actual-window source-rank transfer certificate.

It says the variable even-weight evaluation map can recover the multiplicity mass of each squared orbit in the actual finite carrier.

This is **not** RH and does not assert where those orbits lie.

## 8. Stronger but optional finite-rank theorem

If it follows naturally, prove that the family of squared-orbit selectors separates any two finite multiplicity configurations on the same finite carrier whenever their squared-orbit multiplicity masses differ.

A generic finite theorem is acceptable if it is then instantiated to the actual Xi zero-disk carrier.

Do not build a general polynomial interpolation library beyond what this audit needs.

## 9. Part A classification

Choose exactly one:

```text
ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND
ACTUAL-WINDOW-TRANSFER-API-GAP
ACTUAL-WINDOW-SYMMETRY-OBSTRUCTION
```

For `FOUND`, name the exact Lean theorem that evaluates the selector-weighted actual Xi moment.

If Part A is not `FOUND`, stop the mathematical implementation after documenting the exact obstruction.  Do not force Part B to compensate for a missing actual-window transfer.

# Part B — Mellin family transfer audit

## 10. Start Part B only after Part A succeeds

The question is now narrower:

```text
Does the already-existing parameterized Mellin second-difference family
carry the actual finite squared-orbit rank found in Part A?
```

Do not compare the Mellin family merely against the old quadratic scalar.

## 11. Exact Mellin source surface

Verify the checked-out theorem exposing, for `τ != 0`,

```text
pascalCenteredXiMellinSecondDifferenceWeight ε τ z
  = ((exp (τ z) - 2 + exp (-τ z)) / τ^2)
      * centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z.
```

Also verify the patched `τ = 0` theorem and the positive-`ε` pointwise limit

```text
centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z -> 1
```

as `ε -> 0+`.

Do not replace these exact source theorems with a heuristic Taylor series.

## 12. Finite-window nonvanishing of the spectral factor

Because the actual zero window is finite, attempt to prove an eventual simultaneous nonvanishing theorem:

```text
for a fixed finite Xi zero window S,
for all sufficiently small positive ε,
for every z in S,
  centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z != 0.
```

Use only the existing pointwise convergence to `1` plus finite intersection of eventual statements.

This theorem is finite and does not involve `T -> infinity`.

It is useful as a diagonal invertibility fact, but **by itself it does not prove that the Mellin `τ`-family spans all even polynomial weights**.  Do not overclaim this step.

## 13. Audit the `τ`-family rank

Investigate the smallest rigorous route from the exact exponential second-difference family to the finite squared-orbit evaluation rank.

Allowed approaches include:

```text
A. finite τ-jet at τ = 0
B. derivatives in τ recovering even powers
C. finite evaluation matrix at finitely many τ-values
D. analytic-function separation on distinct squared orbits
E. a finite Vandermonde-type reduction after exact derivative formulas
```

Prefer the smallest theorem that actually transfers rank.

Do not implement an infinite-dimensional function-space theory.

### 13.1 If using a τ-jet

The formal coefficient pattern expected from ordinary mathematics is

```text
(exp (τ z) - 2 + exp (-τ z)) / τ^2
  = z^2 + τ^2 * z^4 / 12 + τ^4 * z^6 / 360 + ...
```

But this expansion is **not** a provider until formalized from exact derivative/Taylor theorems.

If the required derivative machinery becomes substantially larger than the source-rank theorem itself, stop and record `MELLIN-FAMILY-RANK-UNRESOLVED` rather than opening a long analytic subproject.

### 13.2 If using finite τ-values

It is enough to prove invertibility/separation on the **actual finite squared-orbit set**.  Do not prove a global theorem on all of `ℂ` unless it is easier.

## 14. Part B classification

Choose exactly one:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-RANK-TRANSFER-FOUND
MELLIN-FAMILY-RANK-UNRESOLVED
MELLIN-FAMILY-REDUNDANT-TO-FIXED-OBSERVABLES
```

`FOUND` requires an exact finite theorem, not just a Taylor heuristic.

`REDUNDANT` requires an exact finite/invertible reduction to the old fixed observables.

Otherwise use `UNRESOLVED` and name the smallest missing theorem.

# GWSS-002 authorization gate

## 15. Do not start the off-critical witness stage automatically

GWSS-002 remains forbidden during this assignment.

At the end, report whether it would be mathematically authorized next.

Authorization requires at least:

```text
Part A = ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND
```

and a precise statement of which source family will be used for the witness.

Preferred stronger authorization is:

```text
Part B = MELLIN-FAMILY-ACTUAL-WINDOW-RANK-TRANSFER-FOUND.
```

If only Part A succeeds while Part B remains unresolved, classify the generic variable-weight source as high-rank but keep the Mellin-specialized route unresolved.  Do not silently conflate the two.

## 16. What GWSS-002 would still need later

Even after source-rank transfer, the next chain is only:

```text
high-rank finite zero source
  -> choose an off-critical squared-orbit witness
  -> finite explicit formula
  -> von Mangoldt term
     + archimedean term
     + elementary term
     + top-horizontal term
  -> independent arithmetic control ?
```

No correction term may be discarded.

The existing arithmetic cutoff theorem is `X -> infinity` at fixed finite window.  It is not a `T -> infinity` theorem.

# Implementation discipline

## 17. Preferred module structure

If Part A requires a new module, prefer one focused file such as

```text
DkMath.RH.CFBRC.PascalCenteredXiActualWindowVariableWeightRankTransfer
```

If Part B requires only a few theorems, keep them in the same audit module or one clearly named Mellin transfer module.

Avoid A-Z module proliferation.

Do not modify the public `DkMath.RH` import surface unless an actual reusable theorem is completed and root export is clearly warranted.  If public export is changed, run the root build.

## 18. Required reports

Create:

```text
0005-GWSS-001T-actual-window-transfer-report.md
```

and, if Part B is actually attempted after Part A succeeds:

```text
0006-GWSS-001T-Mellin-family-transfer-report.md
```

The reports must distinguish theorem-proved facts from mathematical heuristics.

## 19. Verification

For every new or modified Lean module, run focused builds:

```text
lake build <module>
```

If the root public import surface changes, also run:

```text
lake build DkMath.RH
```

Always run:

```text
git diff --check
```

Check new Lean source for:

```text
sorry
admit
new axiom placeholders
```

Use `#print axioms` on each new load-bearing transfer theorem.

Accepted ordinary axiom footprint remains the usual Mathlib foundations such as:

```text
propext
Classical.choice
Quot.sound
```

Do not treat those as new mathematical assumptions.

## 20. Final response format

Begin the implementation report with exactly these four orientation items:

```text
Global objective:
Current GWSS stage:
Load-bearing boundary:
Next unresolved Gap:
```

Then report separately:

```text
GWSS-001T-A classification
GWSS-001T-B classification, or NOT STARTED with reason
exact new theorem names
changed files
focused build results
axiom audit
git diff --check
whether GWSS-002 is authorized next
```

Do not claim RH progress from source-rank alone.  A named obstruction is an acceptable successful audit result.
