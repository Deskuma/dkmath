# IPSM-059 — CS35 closeout and CS36 mirror-paired functional-equation completion audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS35 verdict: **Green-B**.

CS35 has now proved, entirely at fixed finite `ε`, `W`, and `X`:

- the top-edge mirror `u ↦ 1-u`,
- centered-coordinate conjugate reflection,
- Mellin-weight mirror conjugation and real/imaginary parity,
- nonvanishing of the mirror-paired finite Euler-renormalized residual on the safe top interval,
- a positive-real center basepoint at `u = 1/2`,
- the paired residual ODE,
- the paired rate decomposition into amplitude difference and phase sum,
- mirror cancellation of the scalar density,
- exact compression of the full top interval to a center-based half interval,
- branch-free center displacement and a unit-norm paired phase carrier.

No sign estimate, infinite Euler product, prime-series continuation across the strip, limit exchange, zero-side positivity provider, or RH conclusion has been introduced.

The remaining substantive frontier is still the independent finite weighted-displacement / reach estimate.

## 1. CS36 goal

Do **not** introduce another abstract reach provider.

CS36 should identify the exact analytic object carried by the CS35 mirror pair and determine how much of the remaining finite rectangle background is already forced by the completed-zeta functional equation.

The key finite object is

```text
PairF_X(u) = F_X(u) * conj(F_X(1-u)),
```

where

```text
F_X(u) = R_X(u+iT),
R_X(s) = ζ(s) * exp(-A_X(s)).
```

For

```text
s(u) = u + iT,
m(u) = 1-u + iT,
```

we have

```text
conj(m(u)) = 1 - s(u).
```

The expected ordinary-coordinate factorization is therefore

```text
PairF_X(u)
  = ζ(s) * ζ(1-s) * exp(-(A_X(s) + A_X(1-s))).
```

This must be proved from finite conjugation identities. It must not be inserted as a simplification assumption.

## 2. Proposed implementation module

Suggested module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedFunctionalEquationAudit
```

Import the minimum required finite residual / CS35 modules and Mathlib completed-zeta functionality.

Avoid importing RH-closing bridge APIs merely to obtain a standard functional-equation identity when Mathlib already provides that identity directly.

In particular, do not use `riemannHypothesis_of_*`, standard-zeta-to-CFBRC zero bridges, fixed-defect nonnegativity, or any zero-locus provider as a sign source.

## 3. CS36-A — ordinary-coordinate mirror geometry

Define or expose compact aliases for the top point and its mirror:

```lean
s_X? u := pascalSymmetricRectangleTopEdge u W.rectangle.T
m_X? u := pascalSymmetricRectangleTopEdge (1-u) W.rectangle.T
```

Prove exactly:

```text
conj(m(u)) = 1 - s(u).
```

Reuse the CS35 top-edge mirror theorem rather than rebuilding the coordinate algebra.

Also transport the existing safe-top contract from `m(u)` to `1-s(u)` as needed.

## 4. CS36-B — finite Euler-potential conjugation

The finite Euler log potential is a finite sum over the canonical prime-power support. Prove its conjugation law directly from the finite summands:

```text
conj(A_X(z)) = A_X(conj z).
```

Equivalently on the mirror top edge:

```text
conj(A_X(m(u))) = A_X(1-s(u)).
```

Do the same for the finite compensator:

```text
conj(exp(-A_X(m(u)))) = exp(-A_X(1-s(u))).
```

No infinite Euler product is permitted.

If a repository theorem already supplies the required finite `cpow` conjugation for positive natural bases, reuse it. Otherwise prove only the finite local lemma needed here.

## 5. CS36-C — zeta conjugation bridge

Locate and use the Mathlib conjugation theorem for `riemannZeta` if available. If the exact theorem name differs, adapt to the installed Mathlib version rather than inventing an API.

Target:

```text
conj(ζ(m(u))) = ζ(1-s(u)).
```

The proof must be a standard conjugation property of zeta, not an RH or zero-set argument.

Then prove the finite residual conjugation theorem:

```text
conj(R_X(m(u)))
  = ζ(1-s(u)) * exp(-A_X(1-s(u))).
```

## 6. CS36-D — exact paired residual factorization

Define the symmetric finite Euler potential

```text
A_sym,X(s) := A_X(s) + A_X(1-s).
```

Prove the exact factorization

```text
PairF_X(u)
  = ζ(s(u)) * ζ(1-s(u)) * exp(-A_sym,X(s(u))).
```

Useful follow-up facts:

- `A_sym,X(1-s) = A_sym,X(s)`.
- the exponential factor is everywhere nonzero.
- on the safe top interval, both zeta factors are nonzero.
- therefore the factorization itself supplies another proof of paired-residual nonvanishing.

This is a finite factorization theorem, not a convergence statement.

## 7. CS36-E — completed-zeta fold

On the safe top interval, the ordinary factors exclude `s = 0`, `s = 1`, zeta zeros, and the relevant Gamma-factor zeros. Use only those already available factor-safety facts.

Mathlib provides the completed-zeta functional equation

```text
completedRiemannZeta (1-s) = completedRiemannZeta s.
```

Derive the exact safe-point rewriting of

```text
ζ(s) * ζ(1-s)
```

in terms of a **single completed-zeta value squared** and the explicit Gamma factors.

The expected schematic form is

```text
ζ(s) ζ(1-s)
  = completedRiemannZeta(s)^2 / explicitGammaPair(s),
```

but **do not hard-code this normalization from the roadmap**. Read the installed Mathlib definitions / `riemannZeta_def_of_ne_zero`, let Lean determine the exact multiplication order and factors, and record the theorem actually proved.

Then rewrite `PairF_X` as

```text
completed-factor-square
× explicit Gamma/elementary factor
× finite symmetric Euler compensator.
```

No positivity is inferred from the square: the completed-zeta value is complex on the top edge.

## 8. CS36-F — optional centered-Xi factor bridge

If an existing exact theorem relates the centered fixed-Xi kernel at

```text
z = s - 1/2
```

to `completedRiemannZeta s` by explicit nonzero polynomial factors, expose a safe-point paired residual rewriting through that theorem.

Requirements:

- derive every coefficient and factor from the existing theorem;
- keep `s(s-1)` / Gamma factors explicit;
- do not use a zero-locus equivalence or RH-sufficient factor bridge;
- do not infer sign from a complex square.

If the exact value bridge is not already available in the imported dependency graph, skip this gate rather than rebuilding an RH-closing bridge.

## 9. CS36-G — paired log-rate functional-equation ledger

The CS35 paired rate is

```text
PairQ_X(u) = q_X(u) - conj(q_X(1-u)).
```

Use the finite pair factorization to derive an exact log-rate decomposition.

Conceptually it should separate into:

1. a completed-zeta / fixed completed factor rate,
2. an explicit Gamma / elementary symmetric-factor rate,
3. a finite symmetric Euler-potential rate.

Derive all signs by differentiation in Lean. Do not transcribe a guessed formula.

The finite Euler part should be expressible through the already proved derivative

```text
A'_X = -PHZ_X.
```

The completed part should use the ordinary completed-zeta functional equation only; no zero-side residue positivity is allowed.

## 10. CS36-H — compare against the CS30 rectangle background

This is the load-bearing audit.

Substitute the CS36 paired-rate ledger into the CS35 half-interval scalar representation, then compare its explicit Gamma / elementary pieces with the finite rectangle background already defined in CS30.

Ask Lean whether any of these pieces **cancel exactly**.

Do not assume cancellation merely because both came from completed-zeta factorization.

Possible outcomes:

### H1 — exact source cancellation

A nontrivial archimedean / elementary / boundary component of the CS30 background cancels against the corresponding completed-functional-equation contribution of the CS35 half-interval ledger.

This is genuine progress. State the reduced reach target explicitly.

### H2 — no exact cancellation, but a smaller exact mismatch

Define only the irreducible remaining finite quantity, for example a named paired functional-equation remainder. Prove its exact relation to the old background / reach target.

This is Green-B if the remainder is structurally narrower than the old weighted-displacement frontier.

### H3 — algebraically equivalent renaming

If the proposed new remainder is exactly the old reach inequality with no new cancellation or source restriction, do not count it as progress and do not delete the previous gap.

## 11. Center basepoint audit

Use the CS35 theorem

```text
PairF_X(1/2) = normSq(F_X(1/2)) > 0
```

as a consistency condition for the completed-factor representation.

At `u=1/2`, the completed/Gamma/Euler factorization must simplify to the same positive-real value.

This is an excellent normalization check. It is not itself a reach provider.

Likewise retain

```text
PairPhaseCarrier_X(1/2) = 1.
```

Do not introduce `Complex.arg`.

## 12. Firewall

CS36 must remain finite and source-level.

Forbidden shortcuts:

- no infinite Euler product;
- no infinite prime series on the top edge;
- no `X → ∞` interchange;
- no `ε → 0` interchange;
- no zero-side fixed-defect nonnegativity as provider;
- no horizontal-energy / RH equivalence as provider;
- no universal mode / ray positivity;
- no assumption that a complex square is nonnegative;
- no use of RH-closing CFBRC zero-map / factorization theorems;
- no declaration of the desired paired reach inequality as a provider hypothesis and then counting it as progress.

## 13. Expected verdicts

### Green

The functional-equation factorization produces a genuinely source-derived inequality or exact cancellation sufficient to advance the finite reach target without importing the target sign.

### Green-B

The paired residual and paired rate are exactly rewritten through completed zeta / explicit factors / finite symmetric Euler potential, and a nontrivial narrower remainder or structural cancellation is exposed, but no independent reach estimate is yet proved.

### Yellow

The finite ordinary pair factorization closes, but a required standard conjugation / completed-factor derivative bridge is missing from the current Mathlib surface and remains an explicit local analytic contract.

### Red

The implementation uses an infinite Euler product in the critical strip, imports zero-side positivity as a prime-side provider, silently assumes a complex-square sign, or derives RH through an existing zero-map bridge.

## 14. Named frontier

If CS36 closes only the functional-equation representation, retain the old weighted-displacement reach frontier and add a narrower marker only if it describes a genuinely new unresolved source estimate, for example:

```lean
inductive PascalCenteredXiPrimeSideFiniteResidualMirrorFunctionalEquationReachGap : Prop
  | no_independent_paired_functional_equation_reach_estimate
```

Do not remove the earlier reach gap merely because it has been rewritten.

## 15. Validation

Run at least:

```text
lake env lean <CS36 file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 16. Research interpretation

The chain is now:

```text
finite prime interaction
→ phase boundary
→ holomorphic finite potential
→ finite Euler-renormalized zeta residual
→ phase/amplitude transport
→ weighted displacement
→ mirror-paired half interval
→ completed functional-equation pair.
```

CS35 supplied the canonical center `u=1/2` and removed the duplicated left/right top-edge information. CS36 should determine whether the remaining paired transport is already partly accounted for by the completed-zeta functional equation, leaving only a genuinely finite symmetric Euler displacement as the new arithmetic frontier.
