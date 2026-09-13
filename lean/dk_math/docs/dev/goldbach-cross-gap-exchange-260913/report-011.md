# CGE-011 closeout — Full Alternating Pascal Tail / Parity-Split Signed CRT

## Scope

CGE-011 adds a finite, balanced-window, anchor-local generalization of the
signed CRT accounting layer.  It does not add a universal survivor provider,
Strong Goldbach theorem, density statement, or prime-realization argument.

## Implemented declarations

The implementation is in
`DkMath/NumberTheory/Goldbach/BalancedSignedCRTParityTail.lean` and is exported
by `DkMath.NumberTheory.Goldbach`.

- `signedSubsetResidues`
- `goldbachWindowSubsetSupportSeats`
- `goldbachSignedSubsetCRTCount`
- `goldbachSignedSubsetCRTCount_eq_supportSeats_card`
- `goldbachWindowJOverlapCount`
- `goldbachSignedJCRTSum`
- `goldbachSignedJCRTSum_eq_windowJOverlapCount`
- `goldbachWindowLocalEvenTailMass`
- `goldbachWindowLocalOddTailMass`
- `goldbachWindowEvenTailMass`
- `goldbachWindowOddTailMass`
- `goldbachWindowLocalEvenTailMass_eq_overlapExcess_add_oddTail`
- `goldbachWindowEvenTailMass_eq_overlapExcess_add_oddTail`
- `goldbachSignedEvenTailCRTSum`
- `goldbachSignedOddTailCRTSum`
- `goldbachSignedEvenTailCRTSum_eq_windowEvenTailMass`
- `goldbachSignedOddTailCRTSum_eq_windowOddTailMass`
- `goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget`
- `goldbachPairAt_of_exact_signed_parity_budget`

The generic `j`-layer signed CRT sum was proved equal to the corresponding
Pascal overlap count.  The generic finite subset CRT count was proved exactly
equal to the support-seat count under the explicit finite prime-world anchor.

## Parity and CRT results

The unconditional local parity-tail identity was proved for every finite
support, including empty and singleton supports:

```text
EvenTail = OverlapExcess + OddTail
```

The signed even and odd CRT sums were each identified exactly with their
window parity-tail masses.  Combining these identities with the existing
single-incidence conservation gives the exact finite iff
`goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget`.  The
anchor-local `goldbachPairAt_of_exact_signed_parity_budget` wrapper reuses the
existing survivor-to-`SquareBody` certification bridge.

## Kernel regressions

The audit extends
`DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean`.

- `(n,w,P)=(15,8,5)`: window `9`, incidence `9`, even tail `3`, odd tail `0`.
- `(n,w,P)=(50,10,7)`: window `11`, incidence `19`, even tail `12`, odd tail `2`.
- `(n,w,P)=(22,9,7)`: window `10`, incidence `18`, even tail `14`, odd tail `5`.
  The audit also checks `14 = 9 + 5` and `13 + 1 = 14`.
- Support-size-five arithmetic checks
  `C(5,2)=10`, `C(5,3)=10`, `C(5,4)=5`, `C(5,5)=1`, even tail `15`,
  odd tail `11`, `15 = 4 + 11`, and the CGE-010 truncated overpayment
  `10 - 10 + 5 = 5`.
- `(n,w,P)=(68,15,11)`: support sequence
  `1,1,5,1,2,2,1,2,3,2,2,1,3,3,2,0`, window `16`, incidence `31`,
  covered `15`, overlap `16`, pair `25`, triple `13`, quadruple `5`,
  quintuple `1`, even tail `30`, odd tail `14`.
  The audit kernel-checks `31 + 14 < 16 + 30` and replays `GoldbachPairAt 68`
  through the new parity-budget wrapper.

## Verification

- `lake build DkMath.NumberTheory.Goldbach.BalancedSignedCRTParityTail` — passed.
- `lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit` — passed, `8737` jobs.
- `lake build DkMath` — passed.
- `git diff --check` — passed.
- Fresh full-build warning filter excluding existing `declaration uses \`sorry\`` warnings — no output.
- Forbidden-construct scan for changed source and audit files (`sorry`, `admit`,
  `native_decide`, `unsafe`, new `axiom`) — no matches.
- New public declarations audited with `#print axioms`; only the existing
  logical/classical foundations `propext`, `Classical.choice`, and `Quot.sound`
  occur.  No `sorryAx` or new project axiom occurs.

## Outcome

**A — FULL FINITE PARITY-SPLIT CRT/PASCAL TAIL**

The result is complete at the finite parity-split accounting and conditional
anchor-local endpoint scope specified by CGE-011.  It remains a finite
re-expression: the parity inequality is not proved for arbitrary `n`.
