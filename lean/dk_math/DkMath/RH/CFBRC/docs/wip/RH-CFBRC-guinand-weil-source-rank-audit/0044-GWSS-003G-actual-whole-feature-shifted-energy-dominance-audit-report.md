# GWSS-003G actual whole-feature shifted-energy dominance audit

Date: 2026-08-22
Branch: wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0
Starting HEAD: 76eb512e6661ecf4e87e7316da8e681f7d0c0429

## Scope and classification

This report implements only GWSS-003G from
0043-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-Codex-implementation-instructions.md.
GWSS-003F3 is reused as a trusted finite representation layer. No limit,
classical Guinand--Weil theorem, Weil positivity criterion, Li criterion, or
RH claim is introduced.

Primary classification:

~~~text
ACTUAL-SHIFTED-ENERGY-POLARIZATION-FOUND-DOMINANCE-GAP
~~~

The actual finite shifted-energy/polarization API is closed, but no
independent source-derived P1/P2/P3 provider exists for the exact synthesized
nonzero-tau whole feature.

## Files changed

~~~text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/0044-GWSS-003G-actual-whole-feature-shifted-energy-dominance-audit-report.md
~~~

The new Lean module imports
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean; F3 itself
was not enlarged.

## Actual shifted energies and integrability

For

~~~text
Phi(u) = pascalCenteredXiMellinGeneralTauWitnessWholeBoxFeature tau c W X u
~~~

the module defines four real finite-window energies with the exact F3
normalization:

~~~text
E1+ = (2*epsilon)^-1 * integral normSq (Phi + 1)
E1- = (2*epsilon)^-1 * integral normSq (Phi - 1)
EI+ = (2*epsilon)^-1 * integral normSq (Phi + I)
EI- = (2*epsilon)^-1 * integral normSq (Phi - I)
~~~

Definitions:

~~~text
pascalCenteredXiMellinWitnessWholeShiftedPlusEnergy
pascalCenteredXiMellinWitnessWholeShiftedMinusEnergy
pascalCenteredXiMellinWitnessWholeShiftedIPlusEnergy
pascalCenteredXiMellinWitnessWholeShiftedIMinusEnergy
~~~

All four shifted normSq integrands are IntervalIntegrable on
[-epsilon, epsilon]. The proof uses the F3 restricted-product rectangle
certificates and a local dominated-continuity adapter for finite coefficient
sums, combining the actual vertical aggregate with - I * the top aggregate.
No totalized integral is used as an integrability assumption.

Exported certificates:

~~~text
pascalCenteredXiMellinWitnessWholeShiftedPlus_intervalIntegrable
pascalCenteredXiMellinWitnessWholeShiftedMinus_intervalIntegrable
pascalCenteredXiMellinWitnessWholeShiftedIPlus_intervalIntegrable
pascalCenteredXiMellinWitnessWholeShiftedIMinus_intervalIntegrable
~~~

## Polarization, WholeSource, and FiniteApprox readouts

The integrated polarization identities are:

~~~text
E1+ - E1- = 4 * (((2*epsilon)^-1 : C) * integral Phi).re
EI+ - EI- = 4 * (((2*epsilon)^-1 : C) * integral Phi).im
~~~

Using the unconditional F3 whole-source representation:

~~~text
E1+ - E1- = 4 * (WholeSource epsilon tau c W X).re
EI+ - EI- = 4 * (WholeSource epsilon tau c W X).im
~~~

Writing A for the finite arithmetic approximant and using
A = 2 * I * WholeSource, the exact finite readouts are:

~~~text
E1+ - E1- =  2 * A.im
EI+ - EI- = -2 * A.re
~~~

The declarations are:

~~~text
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_normalizedIntegral_re
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_four_mul_normalizedIntegral_im
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_four_mul_wholeSource_re
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_four_mul_wholeSource_im
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_eq_two_mul_finiteApproximant_im
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_eq_neg_two_mul_finiteApproximant_re
~~~

The historical neg_four name is retained for the requested I-channel
interface; its displayed equality is the exact positive 4 * imaginary
coordinate readout. All statements remain finite in epsilon, tau, W, and X;
no zero-moment rewrite or limit is used.

## q.im transport and P0/P1/P2/P3 firewall

For c_off i = (q.im : C) * c i, the fixed-reference differences transport
real-linearly:

~~~text
diff_1(q.im * c) = q.im * diff_1(c)
diff_I(q.im * c) = q.im * diff_I(c)
~~~

Declarations:

~~~text
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_one_qIm_const_mul
pascalCenteredXiMellinWitnessWholeShiftedEnergyDifference_I_qIm_const_mul
~~~

The module proves P0 only:

~~~text
0 <= E1+, 0 <= E1-, 0 <= EI+, 0 <= EI-
~~~

The exact P1 equivalences are:

~~~text
E1- <= E1+  <->  0 <= WholeSource.re
EI- <= EI+  <->  0 <= WholeSource.im
~~~

Equivalently, the finite approximant coordinates satisfy
E1- <= E1+ <-> 0 <= A.im and EI- <= EI+ <-> A.re <= 0. These are audit
readouts, not independent sign providers. No P2 equality or P3 controlled
asymmetry theorem was found.

## Bounded provider inventory

The required files and the DkMath/RH/CFBRC source tree were searched for
shifted energy, whole shifted, sign/order, dominance, polarization, Gram,
autocorrelation, excess/defect, and source-surface declarations.

| Candidate | Exact actual synthesized nonzero-tau feature? | Result |
|---|---:|---|
| PascalCenteredXiPrimeSideQuadraticizationAudit.lean | No; fixed tau = 0 feature. | P0 and algebraic order equivalences only. |
| PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean | No; fixed prime-side scalar/excess surface. | Defect/excess identities and an affine both-sign obstruction; no actual-feature dominance. |
| PascalCenteredXiPrimeSideSignAudit.lean | No. | Eventual nonpositivity is a later ordered-limit hypothesis, not an unconditional provider. |
| PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean | No; fixed-reference GWSS-003E feature. | Polarization and P0-only counterexample; no provider. |
| PascalCenteredXiMellinWitnessProviderDecisionAudit.lean | No independent actual-feature sign/order theorem. | Provider decision remains negative. |
| PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean | Only coefficient transport. | Homogeneity/cancellation; fails independence and sign requirements. |
| PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean | Yes for representation. | Source/feature/approximant identities and scalar transport; no order provider. |

No candidate passes all seven checks: exact actual feature, top-horizontal
inclusion, source derivation, P1/P2/P3 strength, independence from q.im,
avoidance of RH-equivalent assumptions, and finite-level validity. In
particular, the fixed-tau = 0 theorem
pascalCenteredXiPrimeSideQuadraticization_wholeShiftedEnergy_order_iff_scalarSurface_nonneg
is an equivalence for a different feature and does not prove its sign.

## Minimal missing theorem and authorization boundary

The next genuinely new provider must prove, for the exact finite synthesized
nonzero-tau feature and without a limit exchange, at least one of:

~~~text
0 <= (pascalCenteredXiMellinGeneralTauWitnessWholeSource epsilon tau c W X).re
0 <= (pascalCenteredXiMellinGeneralTauWitnessWholeSource epsilon tau c W X).im
~~~

or an exact equality / controlled source-side bound strong enough to imply P1,
P2, or P3. It must be source-derived and independent of invertible q.im
rescaling. It is not assumed or packaged as a provider here.

No RiemannHypothesis, Li criterion, classical Weil positivity assumption,
RH-equivalent raw-ratio bound, zero-moment sign rewrite, conjugation-only
argument, functional-equation-only argument, or limit exchange was used.
GWSS-004 remains unauthorized and is not started.

## Verification and axioms

Focused verification:

~~~text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessShiftedEnergyDominanceAudit.lean
git diff --check
~~~

Both passed locally under Lean 4.32.2. No commit, push, PR update, or CI run
was performed.

The load-bearing new declarations were axiom-audited and reported only:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No sorry, admit, native_decide, or new axiom was added.
