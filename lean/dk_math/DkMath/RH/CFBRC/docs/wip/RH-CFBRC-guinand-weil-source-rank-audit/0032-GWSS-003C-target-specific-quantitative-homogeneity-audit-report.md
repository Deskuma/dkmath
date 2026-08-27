# GWSS-003C target-specific quantitative homogeneity audit — implementation report

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 1. Orientation and bounded objective

The global objective remains

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

The current stage is `GWSS-003C`.  The load-bearing boundary is the
target-dependent GWSS-002 witness: its coefficient row is obtained from an
unscaled coordinate extractor by multiplying by

```text
qIm := ((pascalCenteredXiSquaredOrbitCoordinate R j0).im : ℂ).
```

The finite arithmetic RHS is already complex-linear in the weight.  This
stage asks whether first-order quantitative control can retain information
about `qIm`, or whether the factor cancels structurally.

The implementation was performed on branch
`wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`, at HEAD
`86a6895770da9817a895c5424baec748ec26810f`, with the working tree clean
before the edit and Lean 4.32.2 (`leanprover/lean4:v4.32.2`).  The 0029
instructions, 0030 report, and the off-critical witness, arithmetic-control,
phase-no-go, and prime-side transport modules were read before editing.

The corrected 0030 hierarchy is:

```text
Primary classification:
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED

Secondary findings:
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
CONJUGATION-SYMMETRY-API-GAP
```

## 2. Implemented witness factorization

The focused module is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean`.

* `exists_pascalCenteredXiMellinMassWitness_of_full_rank_target` exposes an
  admissible unscaled mass extractor from the existing inverse-matrix row.  It
  uses only full rank and positive window width; it does not use
  `qIm ≠ 0`.
* `pascalCenteredXiMellinWitnessWeight_scaled_coefficients` proves the exact
  finite-sum identity

  ```text
  witness (fun i => qIm * c0 i) = fun z => qIm * witness c0 z.
  ```

* `exists_pascalCenteredXiMellinMassAndOffCriticalWitness` packages the mass
  witness, the scaled off-critical witness, both admissibility contracts, the
  two zero-moment identities, nonzero detector mass, and the exact function
  factorization.

Therefore the off-critical displacement is not merely a moment-level scalar;
it is an overall scalar of the synthesized function.

## 3. Finite arithmetic transport and normalization

The following exact first-order identities are proved:

```text
pascalCenteredXiMellinWitnessOrdinaryZetaRightEdgeIntegral_const_mul
pascalCenteredXiMellinWitnessArchimedeanRightEdgeIntegral_const_mul
pascalCenteredXiMellinWitnessElementaryRightEdgeIntegral_const_mul
pascalCenteredXiMellinWitnessTopHorizontalContribution_const_mul
pascalCenteredXiMellinWitnessFiniteArithmeticRHS_const_mul
```

The top-horizontal identity is finite-height only; no horizontal decay or
`T -> infinity` passage is used.

The theorem
`pascalCenteredXiFiniteArithmeticRHS_mass_identity_of_scaled_witness` proves
the normalized cancellation statement.  From a nonzero `q`, the exact scaled
off-critical RHS identity, and the finite explicit formula, cancellation gives

```text
F(h_mass) = -(2 * pi * I) * mass.
```

This is the occupied-orbit mass identity after removing the target scalar.  It
is not a contradiction and is not an independent arithmetic provider.

## 4. Prime-side majorant and norm cancellation

The existing theorem
`norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant` was reused.
The new declarations

```text
pascalPrimePowerRightEdgeCutoffIntegrand_witness_const_mul
norm_pascalPrimePowerRightEdgeCutoffIntegrand_witness_le_scaled_majorant
norm_pascalCenteredXiMellinWitness_mul_majorant_const_mul
```

show respectively that the finite prime cutoff integrand scales by `qIm`,
that its majorant remains valid with the same `‖qIm‖` factor, and that the
majorant's weight side itself has exact absolute scalar homogeneity.  The
underlying vertical majorant is uniform in `X` and `t`, but still multiplies
the target-dependent weight norm.

The generic theorem
`norm_mul_le_norm_mul_iff_of_ne_zero` formalizes the key cancellation:

```text
q ≠ 0 -> (‖q * w‖ ≤ ‖q‖ * B ↔ ‖w‖ ≤ B).
```

Consequently every audited bound assembled only from linearity, triangle
inequality, componentwise norm estimates, coefficient absolute values, basis
weight norms, or linear integral bounds inherits the same `‖qIm‖` factor.

## 5. Information-content audit: H1, H0, HS

The audited provider types are:

```text
H1  first-order homogeneous: B(q*h) = |q| * B(h)
H0  nonhomogeneous:          B(q*h) <= C independent of |q|
HS  strictly sublinear:      B(q*h) = o(|q|), or an independently justified
                             vanishing-scale estimate
```

For the current construction:

* H1 is formally present and cancels exactly.  It cannot force `qIm = 0`.
* H0 is not provided by the current API.  Even if supplied as a finite bound,
  it would generally bound the size of `qIm`; it would force `qIm = 0` only if
  the independent bound were itself forced to zero.
* HS is not present.  It could in principle contradict a fixed nonzero
  detector, but would require new analytic information, a parameter, or a
  justified vanishing sequence.  No such limit, decay, or estimate is assumed
  here.

The normalized mass identity also blocks a false finite strict inequality for
the same data: an unconditional bound strictly below the exact norm of
`F(h_mass)` would contradict the already-proved finite identity.  A viable
future provider must add genuinely new structure, such as an independent
vanishing parameter, a nonlinear positivity observable, a surviving restricted
real structure, or another independent arithmetic observable.  None is
implemented in GWSS-003C.

## 6. Classification and next unresolved Gap

The exact primary classification is:

```text
OFF-CRITICAL-SCALAR-HOMOGENEITY-OBSTRUCTION
```

Secondary findings are:

```text
unscaled mass witness:                 FOUND
off-critical scalar factorization:     FOUND
finite arithmetic RHS scaling:         FOUND
four-term component scaling:           FOUND
finite prime majorant scaling:         FOUND
first-order homogeneous cancellation:  FOUND
```

The next unresolved Gap is an independent nonhomogeneous or vanishing-scale
quantitative theorem, or a separately justified nonlinear/real-structure
provider.  The current finite linear and homogeneous norm-control route cannot
extract `q0.im = 0` because its scalar factor cancels exactly.

GWSS-004, classical Guinand--Weil infrastructure, Weil positivity, Li, RH,
horizontal limits, new zero-avoidance theory, and new source families remain
unauthorized by this stage.

## 7. Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean
```

The required wrapper target and `git diff --check` were also run.  A temporary
axiom-audit file checked the load-bearing theorems; the reported footprint was
only:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `native_decide`, new axiom, unproved limit exchange,
positivity shortcut, or RH-equivalent provider was introduced.  Commit, push,
CI, and downstream GWSS-004 work were not performed.
