# RH-CFBRC ZDI route closeout report

Date: 2026-08-19

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## 0. Closeout decision

The current ZDI finite-certificate route is closed at **O-INFORMATION**.

This is a successful stop under the completion criterion of
`0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`: the explored finite-certificate route has reached a precise formal obstruction, and no RH-equivalent provider or target-encoding definition has been introduced to bypass it.

Do not continue this branch by adding ZDI-012 Eta schedule, moving-frame, residual-majorant, whole-sum coercivity, or prime-factor post-processing modules.

The branch should be treated as a completed audit checkpoint and merged/archived according to the normal repository workflow before beginning a genuinely new source route from the latest `develop`.

## 1. Original objective

The branch was created to prove Mathlib's exact `RiemannHypothesis` through a finite prime-derived shrinking-interval route.

For every standard nontrivial zeta zero `s`, the desired certificate shape was

```text
|s.re - 1/2| <= q K
q K -> 0
```

or equivalently, before rationalization,

```text
(centeredSigma s.re)^2 <= epsilon K
epsilon K -> 0.
```

The pre-existing DkReal uniqueness layer was intended to convert these nested shrinking bounds into

```text
s.re = 1/2.
```

The branch therefore did not need another proof that the CFBRC zero locus is the critical line.  Its only mathematical burden was the standard-zeta-zero to finite centered-coordinate certificate.

## 2. ZDI-001..005: genuine forward progress

### ZDI-001

Audited the exact Mathlib `RiemannHypothesis` dependency and confirmed that the direct standard-zeta map-zero provider is RH-equivalent, not an independent source.

### ZDI-002

Exposed the reusable DkReal common shrinking-interval uniqueness theorem.  The final interval-completion mechanism is available and is not the current gap.

### ZDI-003

Audited finite prime-side material and separated unconditional finite arithmetic identities from conditional or RH-equivalent providers.

### ZDI-004

Recovered the genuine zero-derived Eta finite-plus-tail identity and rejected the finite Euler-renormalized pseudo-source whose vanishing is carried only by a `riemannZeta s` factor.

### ZDI-005

Established the strongest new source bridge of this branch:

```text
standard nonreal nontrivial zeta zero
  -> finite Eta critical-mirror defect source
  -> exact finite prime-factor coordinate representation
  -> negative Eta tail.
```

In particular,

```lean
etaPrimeFactorMirrorDefectPairedPartial K s
  = -etaCriticalMirrorDefectPairTail K s
```

is a genuine zero-derived finite prime-factor source identity.

The inherited tail bound gives Q2-F smallness and convergence of this finite complex source to zero.

These P2-F / Q2-F facts remain valid reusable Core.

## 3. ZDI-006: the first information boundary

ZDI-006 proved the Q2-F convergence consequences and audited coercivity.

The crucial exact identity is

```text
etaPrimeFactorMirrorDefectPairedPartial K s
  = etaCriticalMirrorDefectPairedPartial K s.
```

Therefore any observable depending only on the resulting whole complex value or its norm is still an observable of the old Eta defect partial.  Prime factorization exposes summand coordinates but does not, by itself, remove cancellation after those coordinates are summed.

No independent fixed-sign functional, positive energy, or centered-coordinate lower bound was found.

## 4. ZDI-007..010: closed side route

ZDI-007 through ZDI-010 audited whether the old Eta moving/block-frame machinery could nevertheless convert the P2-F smallness into a centered-coordinate bound.

The final result is **O-CONSTANT / FACT-FIXED** for the current bounds.

### ZDI-007

Positive-density schedules are incompatible with the old shrinking-relative-length `EtaPairGrowingBlockSchedule` contract.  The positive-density block span has a nonzero limiting span in general.

### ZDI-008

For each fixed nonreal point, sufficiently small positive density can keep the limiting phase span within a prescribed safe angle.  This proves angle feasibility only; it does not produce a common fixed-block coercive projection or residual domination.

### ZDI-009

The normalized current residual-majorant constant is strictly larger than sixteen times the certified margin constant on both off-critical sides.

### ZDI-010

The ZDI-009 scalar obstruction was connected back to the actual existing source objects.  For every realizable positive-density schedule and every audited nonreal off-critical point, the existing normalized residual power majorant is eventually larger than sixteen times the existing normalized block-margin power lower bound.

Thus the route

```text
P2-F whole source
  -> moving/positive-density block frame
  -> current certified margin
  -> current absolute residual majorant
  -> residual domination
```

is closed under the current source bounds.

This does not prove that the exact oscillatory Eta tail is large or that sharper independent estimates are impossible.

## 5. ZDI-011: final finite-certificate information obstruction

ZDI-011 returned to the ZDI-005 prime-factor source and tested whether its internal coordinates could directly support the intended A/B/C scalar certificate.

The finite source was separated exactly into mirror and original endpoint sums:

```text
prime-factor defect partial
  = mirror endpoint partial - original endpoint partial.
```

However, the standard-zero hypothesis supplies only this difference identity.  It does not provide separate zero-derived identities or upper bounds for the two endpoint components.

The whole-sum firewall was formalized for arbitrary post-processing:

```lean
F (etaPrimeFactorMirrorDefectPairedPartial K s)
  = F (etaCriticalMirrorDefectPairedPartial K s).
```

A concrete opposite-unit countermodel records the generic information loss:

```text
||z1 + z2|| = 0
but
0 < ||z1||^2 + ||z2||^2.
```

The historical finite `primeMirrorEnergy` / aggregate mirror Gap remains a strong unconditional candidate for the centered-coordinate lower side:

```text
energy >= 0
energy = 0 iff centeredSigma = 0
```

but there is no source theorem in the audited path giving

```text
standard zeta zero
  -> zero-derived upper control of that positive energy
  -> quantity tending to zero.
```

This is the final classification **O-INFORMATION**.

## 6. Exact reason to stop

The desired DkReal certificate needs one scalar object `E_K(s)` supporting both sides:

```text
A. source provenance:
   E_K is built from finite arithmetic/prime data;

B. zero-derived upper control:
   E_K(s) <= epsilon_K(s), with epsilon_K -> 0;

C. centered-coordinate lower control:
   a_K(s) * (centeredSigma s.re)^2 <= E_K(s),
   with sufficient positive control on a_K.
```

The current branch has separate pieces:

```text
P2-F / Q2-F:
  A + B for a cancellation-prone complex whole sum;

primeMirrorEnergy / mirror Gap:
  A + C for a positive scalar.
```

What is missing is not another estimate of either object.  It is an **independent source identity connecting B and C on the same positive scalar**.

Without that second source identity, repeating whole-sum norm estimates, endpoint rewrites, mode-energy squaring, moving frames, or schedule refinements cannot supply the missing information.

## 7. Reusable trusted Core from this branch

The following conceptual spine should be retained for future routes:

```text
RiemannHypothesis exact dependency audit
DkReal common shrinking-interval uniqueness
standard nontrivial zero open-strip / nonreal facts
zero-derived Eta finite-plus-tail identity
finite natural-mode prime-factor logarithm factorization
P2-F zero-derived finite prime-factor source
Q2-F convergence to zero
positive-density/current-majorant O-CONSTANT obstruction
whole-sum O-INFORMATION firewall
```

All accepted load-bearing ZDI theorems were reported with no `sorryAx` in their axiom audits.

## 8. Next-route selection rule

Do not choose the next research route by asking how to estimate the existing Eta source more sharply.

Choose it by asking:

> Is there a genuinely independent zero-derived **scalar or quadratic identity** whose finite arithmetic side is positive or controls a positive centered-coordinate energy?

A future route is worth starting only if its source can plausibly supply the missing B-to-C bridge.

Potential source families to audit before implementation include:

1. **Fixed Xi / second-moment defect source** — already gives an exact positive horizontal energy and an ordered prime-side arithmetic representation, but global vanishing is RH-equivalent.  A new route would need an independent finite arithmetic sign/upper theorem, not another representation theorem.
2. **Local zero residue / multiplicity identities** — genuinely zero-derived, but they need a new positive centered-coordinate scalar before becoming a DkReal certificate.
3. **A new quadratic explicit-formula observable** — acceptable only if its positivity and zero-derived upper control are both source-derived and not definitions of the desired RH conclusion.

Do not reopen:

```text
positive-density/current residual-majorant domination
whole Eta-sum norm coercivity
prime-factor notation followed only by whole-sum post-processing
RH-equivalent fixed-Xi defect vanishing as a provider.
```

## 9. Formal status

No axiom-audited Lean term of `RiemannHypothesis` has been produced on this branch.

The branch nevertheless meets the roadmap's alternate completion condition: the explored finite-certificate route has reached a precise formal obstruction and the obstruction is recorded without manufacturing an assumption.

Final status:

```text
ZDI finite-certificate route: CLOSED — O-INFORMATION
RH: not proved
DkReal completion layer: ready
missing mathematical ingredient: independent zero-derived positive/quadratic scalar bridge
```
