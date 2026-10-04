# Validation — Gap focusing

Date: 2026-10-04. Working directory: `lean/dk_math`.
Lean / Mathlib: `v4.34.1`. Initial working tree was clean.

The new package has four implementation modules and one public facade.
It exports 50 theorems, including wrappers for existing algebra and two
root-choice independence lemmas promoted from the earlier FLT357 audit.
Four durable test/audit modules cover type boundaries, counterexamples, and
all public theorem dependencies. The main `DkMath` facade imports the package.
One further document-local audit checks the actual current p=7 carrier bridge.

## Commands and results

```sh
lake build DkMath.NumberTheory.GapFocusing \
  DkMathTest.NumberTheory.GapFocusingCalibration \
  DkMathTest.NumberTheory.GapFocusingAxiomAudit \
  DkMathTest.GapFocusingPhase DkMathTest.GapFocusingDegree

lake build DkMath

lake env lean docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/checks/UnitPowerClassAudit.lean

lake env lean docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/SevenCarrierBridge.lean

lake build DkMathTest.GapFocusingPhase
git diff --check
```

| Check | Result | Evidence |
| --- | --- | --- |
| New public facade, four implementations, four test/audit targets | Exit 0; 2820 jobs, no warnings | [focused build](build-focused.txt) |
| Main `DkMath` public facade | Exit 0; 10355 jobs | [root build](build-dkmath.txt) |
| Prior unit-class audit and actual exponent3/5/7 carrier instances | Exit 0 | [prior audit](prior-unit-audit.txt) |
| Actual p=7 focused coordinates, existing extraction, and fixed-ramifier class | Exit 0; three checked theorems, only the allowed axiom set | [carrier bridge](seven-carrier-bridge.txt) |
| Final phase test after adding copyright/file marker | Exit 0 | [phase final build](build-phase-final.txt) |
| All 50 public theorems plus `focusCoordinates` | All dependencies contained in `{propext, Classical.choice, Quot.sound}` | [aggregate audit output](build-focused.txt), [machine-checked summary](audit-summary.txt) |
| `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` scan | No matches in all ten new Lean files, including the document-local audit | [summary](audit-summary.txt) |
| `git diff --check` | Exit 0 | [repository checks](repository-checks.txt) |

The main facade build replayed five existing `sorry` warnings in
`ZsigmondyCyclotomicResearch`, `TriominoCosmicBranchA`, `GcdNextResearch`,
`CyclotomicPrincipalization`, and `TriominoFLT`. Exact locations are retained
in [audit-summary.txt](audit-summary.txt). They are outside the new package;
the 51 audited new declarations have no `sorryAx` dependency.

This validates the stated targets and the main facade, not every module in
the repository or the entire `DkMathTest` library.

## Meaningful calibration boundaries

- Numerical gap divisibility can hold with nonzero focus defect.
- Equal anchor powers do not force equal anchors.
- Simultaneous translation can change the defect.
- Characteristic three adds a formal gap factor at a unit anchor.
- Prime degree11 gives irreducible GN over `ℤ[X]` and `ℚ[X]`, yet its value
  at `(1,1)` is `23*89`.
- Odd-prime doubled degree6 has three residual cyclotomic layers; `p=2`
  collapses the divisor set to two distinct layers.
- Both `2p` composition orders agree at zero gap in `ZMod 4`.
- Ramifier rescaling changes the cube class in `ZMod 7`.

No benchmark or numerical observation is used as proof of a general theorem.
