# GWSS-003B complex-linear phase no-go audit — implementation report

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 1. Bounded result

This stage implements only GWSS-003B.  It continues the GWSS-003A frontier

```text
MELLIN-WITNESS-FINITE-ARITHMETIC-IDENTITY-FOUND-CONTROL-GAP
```

and does not start classical Guinand--Weil infrastructure, Weil positivity,
Li, a horizontal `T -> infinity` argument, new zero-avoidance theory, a new
source-rank family, or an RH deduction.

The implementation is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean`.
It proves the finite algebraic obstruction for the current complex-linear
admissible class and records, separately, the unresolved compatibility of the
canonical Mellin witness with a smaller conjugation-real class.

## 2. Orientation and load-bearing boundary

The working tree was clean before this stage.  The implementation was checked
on branch
`wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`, at HEAD
`c97d35a06077132669d24998485ec75f29a39262`, with Lean 4.32.2
(`leanprover/lean4:v4.32.2`).

The relevant 0027/0028 instructions and reports, together with the arithmetic
control, off-critical witness, specialization, finite explicit-formula,
prime-side transport, and horizontal-pairing modules, were read before the
edit.  The load-bearing boundary remains the target-dependent off-critical
weight `h` with a nonzero pure-imaginary detector value supplied by the
zero-side identity.  A new contradiction must therefore use an independent
property of `h` or of a restricted admissible class; it may not be obtained by
rewriting the already-known zero moment.

## 3. Implemented finite algebra

The following declarations provide the GWSS-003B-1 and -2 API:

* `pascalCenteredEvenWeight_const_mul` and
  `pascalCenteredXiDifferentiable_const_mul` show closure of the current
  differentiable/even class under arbitrary complex scalar multiplication.
* `pascalCenteredXiZeroDiskWeightedMoment_const_mul` records the corresponding
  comparison identity for the finite zero moment.
* `pascalCenteredXiFiniteArithmeticRHS_const_mul` proves directly that
  `pascalCenteredXiFiniteArithmeticRHS h W` is complex-linear in `h`.  The proof
  distributes the scalar through all four finite interval-integral terms,
  including the top-horizontal contribution; it does not use the zero-side
  explicit formula as a source of arithmetic linearity.
* `complex_eq_zero_of_im_eq_zero_and_I_mul_im_eq_zero` proves the two-coordinate
  complex algebra used by the phase audit.
* `pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_im_zero_on_h_and_I_mul`
  proves the local no-go: if the RHS and the RHS of `I * h` both have zero
  imaginary part, then the RHS at `h` is zero.
* `pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_universal_im_zero` proves
  that a universal real-axis phase theorem on the full current class forces the
  RHS to vanish on that class.
* `pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_universal_re_zero` proves the
  analogous statement for a universal imaginary-axis phase theorem.

Thus the universal complex-linear phase-provider route is formally closed
unless the finite RHS is identically zero on the relevant class.

## 4. Smaller real/conjugation-compatible class

The module defines the audit predicate

```lean
PascalCenteredXiConjugationRealWeight h :=
  ∀ z, h (starRingEnd ℂ z) = starRingEnd ℂ (h z)
```

The theorem
`pascalCenteredXiConjugationRealWeight_I_mul_eq_zero_of_conjugationReal`
shows that if both `h` and `I * h` satisfy this predicate, then `h = 0`.
This identifies the structural escape from the full complex-linear no-go: a
real form is not closed under multiplication by `I`.

No theorem was added asserting that the canonical Mellin family, the
inverse-matrix coefficient family, or the current off-critical detector lies
in this real form.  In the present GWSS API, the required simultaneous
conjugation theorem for the actual Mellin coefficients, window, multiplicity,
and squared-orbit detector has not been established.  Consequently this stage
does not claim either a real-structure witness or a detector cancellation
theorem.

## 5. Correction to the finite norm-control inventory

The earlier broad statement that no finite norm control exists is too strong.
`PascalCenteredXiPrimeRightEdgeTransport.lean` already contains

```lean
norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
```

under `hσ : 1 < σ`, uniformly in the finite cutoff `X` and height `t`, with
majorant `pascalVonMangoldtVerticalMajorant σ`.  The associated integrand
bound has the form

```text
‖h(centeredRightEdge)‖ * pascalVonMangoldtVerticalMajorant σ.
```

This is genuine unconditional finite prime-side norm control.  It does not,
however, force a phase, vanishing, or smallness: the bound still depends on
the target-dependent weight `h`, and it supplies no estimate comparing that
weight norm with the fixed nonzero detector.  The top-horizontal term remains
part of the finite RHS and has not been removed by an unproved limit argument.

## 6. Provider classification

The 003B classification hierarchy is:

```text
Primary classification:
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED

Secondary findings:
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
CONJUGATION-SYMMETRY-API-GAP
```

The first label is proved by the new finite algebra.  The second records that
the needed actual Mellin/conjugation compatibility is not available in the
current witness API.  The primary next provider is therefore target-specific
quantitative control: the first missing quantity is an independent bound on
the target-dependent coefficient/basis-weight right-edge norm (and, if the
finite identity is used at the same level, a compatible bound for the
top-horizontal contribution).  The existing vertical majorant is an input to
such a bound, not that bound itself.

No nonlinear positivity provider is imported or asserted here.  If a future
stage chooses that route, it must provide a separate theorem rather than
repackage a norm inequality as positivity.

## 7. Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean
```

No `sorry`, `admit`, new axiom, `native_decide`, functional-equation upgrade,
or RH-equivalent provider was introduced.  Commit, push, CI, and downstream
GWSS-004 work are outside this bounded stage.
