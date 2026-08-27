# GWSS-003D surviving-provider decision audit — implementation report

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 1. Orientation and boundary

The global objective remains

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

The current stage is `GWSS-003D`.  The audit was started at HEAD
`0f33ea7227f1264542a86475cf6b5b7a72b3bc3f`, on the named branch, with a
clean working tree and Lean 4.32.2 (`leanprover/lean4:v4.32.2`).  The 0029,
0030, 0031, and 0032 instructions/reports and the off-critical witness,
arithmetic-control, phase-no-go, quantitative-homogeneity, arithmetic
specialization, prime-transport, and horizontal-pairing modules were read.
Relevant conjugation and quadraticization modules were also inventoried.

The load-bearing boundary is the GWSS-002 target-dependent finite Mellin
witness.  GWSS-003C proved that its off-critical factor `q0.im` is an overall
scalar and therefore cancels from all currently available first-order linear
norm/majorant estimates.  A surviving provider must add information that is
not equivalent to this scalar rescaling.

## 2. Implemented decision certificates

The focused module is
`DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessProviderDecisionAudit.lean`.

* `false_of_tendsto_zero_and_tendsto_fixed_nonzero` records the minimal
  logical shape of an independent vanishing-scale contradiction.
* `complex_sq_conj_eq_conj_sq` records the finite squared-coordinate symmetry.
* `conjugation_pair_imaginary_detector_cancel` proves in an abstract equal-mass
  two-orbit model that the `q.im` detector cancels against the conjugate orbit.
  This is not asserted as a theorem about the current finite zero carrier.
* `complex_normSq_mul_eq_normSq_mul_normSq` records that a quadratic norm
  observable scales by the square of the scalar norm.

These certificates are deliberately small.  They do not add a zero-carrier
conjugation theorem, a Mellin coefficient selector theorem, or a positivity
bridge to the target-dependent witness.

## 3. Provider A — independent vanishing scale

### Existing inventory

The current Mellin box theorem
`tendsto_centeredMellinBoxApprox_quadraticWeight` converges the spectral
factor to `1` as `ε -> 0+`.  This is a nonvanishing/full-rank normalization,
not a vanishing arithmetic provider.

The prime transport theorems
`tendsto_pascalPrimePowerRightEdgeCutoffIntegrand`,
`tendsto_pascalPrimePowerRightEdgeCutoffIntegral`, and the specialization
`tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula` converge to
the ordinary-zeta right-edge integrand, right-edge integral, or the already
known finite Xi endpoint.  They do not converge to zero for the required
target witness.

`PascalCenteredXiMellinWeightVerticalDecayProvider` is explicitly a
weight-only decay contract.  It does not provide decay of the full
Xi-weighted horizontal integrand or the top-horizontal contribution.
The fixed-window API contains no compatible `T -> infinity` theorem.

### Verdict

```text
independent vanishing-scale provider: NOT FOUND
```

The new limit certificate only shows what a future independent provider would
have to prove.  No current limit survives the 003C scalar normalization with
an independently vanishing arithmetic quantity.

## 4. Provider B — restricted real/conjugation structure

The existing theorem
`nontrivialRiemannZetaZero_conj` in
`EtaCriticalMirrorPairedFrameConjugationAsymptoticAudit.lean` closes the
unshifted nontrivial-zero predicate under conjugation.  The current centered
finite zero-window API does not expose the needed combined theorem for:

```text
centered zero-window membership
finite multiplicity equality
squared-orbit carrier closure
squared-orbit mass equality
```

The current inverse-matrix extractor also supplies no real, conjugate-paired,
or involution-fixed coefficient structure.  Determinant nonvanishing alone is
insufficient.

For the canonical Mellin basis, a private tau-zero conjugation proof appears in
`PascalCenteredXiPrimeSideSignedTailPairingAudit.lean` as
`pascalCenteredXiMellinSecondDifferenceWeight_conj`; it is not a public
all-`τ` compatibility API for the current witness family.  The actual
Mellin-coefficient real form therefore remains an API gap.

The abstract certificate
`conjugation_pair_imaginary_detector_cancel` shows the main risk: equal-mass
conjugate pairs cancel the present single-orbit `q.im` detector.  Whether a
restricted real witness can preserve a nonzero detector while retaining the
required actual carrier information is not established.

```text
canonical Mellin conjugation-realness: API GAP
actual zero-window conjugation symmetry: API GAP
synthesized coefficient real structure: NOT FOUND
detector survival under real structure: UNRESOLVED, with pair-cancellation
                                       obstruction in the abstract model
```

Provider B is not classified as open.

## 5. Provider C — nonlinear positivity / quadratic observables

There is a genuine source-side quadratic candidate in
`PascalCenteredXiPrimeSideQuadraticizationAudit.lean`:

```text
pascalCenteredXiPrimeSideQuadraticization_source_ledger
pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation_eq_normSq
pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy_nonneg
```

The input is a finite prime/archimedean/elementary/top source aggregate at
fixed `ε`, `W`, and `X`.  The output is a nonnegative integral of
`Complex.normSq` and is not merely the zero-side finite explicit formula
rewritten.  The smallest exact candidate is therefore the finite continuous
Gram energy and its source-autocorrelation identity.

However, this candidate has no current bridge to the GWSS-002 target-dependent
Mellin witness, its squared-orbit mass, or `q0.im`.  The source ledger is
one-index linear while the Gram energy is two-index quadratic.  Moreover, the
new `complex_normSq_mul_eq_normSq_mul_normSq` certificate shows that bare
quadratic scaling carries `|q0.im|^2`; positivity alone supplies no independent
asymmetric comparison that would force `q0.im = 0`.

Thus the candidate is genuinely nonlinear and independent as an observable,
but it is not yet a surviving provider for the current detector.

```text
independent nonlinear positivity: FOUND as a source-side candidate
bridge to synthesized witness: GAP
off-critical discrimination: not established
RH-equivalent input: not used by the candidate itself
```

## 6. Provider comparison ledger

| provider class | current exact theorem/API | independent of zeroMoment rewrite? | survives scalar obstruction? | compatible with synthesized witness? | `T -> infinity` | RH-equivalent input? | status |
|---|---|---:|---:|---:|---:|---:|---|
| vanishing-scale / HS | no current zero-limit theorem; only Mellin-to-`1` and cutoff-to-endpoint limits | yes, if found | unknown in principle | gap | not required in abstract form | no current input | NOT FOUND |
| restricted real/conjugation | `nontrivialRiemannZetaZero_conj`; private tau-zero Mellin conjugation proof | yes | unknown | API gap; pair cancellation certificate | no | no current input | API GAP / UNRESOLVED |
| nonlinear positivity | finite source Gram energy and `...ContinuousGramEnergy_nonneg` | yes | not by bare scaling; bridge required | gap | no at finite `X`, but no current detector bridge | no current input | CANDIDATE, DECISION REQUIRED |
| finite prime majorant | `norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant` | yes as arithmetic bound | no; H1-only | yes only as a homogeneous bound | no | no | FOUND, already closed by 003C |
| horizontal weight decay | `PascalCenteredXiMellinWeightVerticalDecayProvider` | yes as a contract | insufficient for full term | gap | would need a new compatible theorem | no | INSUFFICIENT |

The universal full complex-class phase route is closed by GWSS-003B, and the
finite H1 norm route is closed by GWSS-003C.  The finite prime majorant remains
valid but does not change either conclusion.

## 7. Primary classification and next Gap

Exactly one primary classification is selected:

```text
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
```

Secondary findings:

```text
independent vanishing-scale provider: NOT FOUND
canonical Mellin conjugation-realness: API GAP
actual zero-window conjugation symmetry: API GAP
synthesized coefficient real structure: NOT FOUND
detector survival under real structure: UNRESOLVED / pair-cancellation obstruction
independent nonlinear positivity: FOUND as candidate, not bridged provider
```

The next unresolved Gap is a bounded bridge decision for the finite source Gram
energy: prove an independent relation between that energy/polarization and the
current target-dependent Mellin witness, or close the candidate as
non-discriminating.  No such bridge is assumed here.

GWSS-004 remains unauthorized.  In particular, this classification does not
authorize importing the classical Guinand--Weil theorem, the full Weil
criterion, Li, a horizontal limit, new zero-avoidance theory, DkReal, or RH.

## 8. Verification

Focused verification passed:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessProviderDecisionAudit.lean
```

The new certificate declarations use no `sorry`, `admit`, `native_decide`, or
new axiom.  Axiom audit is expected to remain within:

```text
propext
Classical.choice
Quot.sound
```

Commit, push, CI, and downstream GWSS-004 work were not performed.
