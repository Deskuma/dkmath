# Review 004 — degree-seven GTail calibration

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Decision: **APPROVED — Outcome B (checked algebraic calibration)**

## Evidence reviewed

- Pushed `DkMath/Lib/Cosmic/GTailSeven.lean` (139 lines).
- Pushed `DkMathTest/CosmicFormula/GTailSeven.lean` (177 lines).
- `report-004.md`, `source-inventory-004.md` and current `ROADMAP.md`.
- Earlier selection, factor, transport and GTail contracts.
- Available `DkMath/FLT/Seven/Basic.lean` entry point for the planned next step.

**Review method:** source/theorem-contract/test review through GitHub. The focused build successes and axiom lists in `report-004.md` were recorded by Codex and **not independently rerun** in this review.

## Findings

1. `GTail_seven_six` and `GTail_seven_five` use canonical `GTail_rec`, preserving the established index convention: k is the exponent of x.
2. Selected high-index Body statements are derived via `selectedBody_Ico` and the evaluated GTail rows.
3. The interior `Finset.Ico 1 7` correctly retains k=1..6 and places only `u^7` and `x^7` in Gap.
4. `selectedBody_seven_interior_eq_mul_residual` uses the **general** active-bound factor theorem (Step 002), and `selectedResidual_seven_interior` explicitly evaluates the finite residual before the final `ring` factorization.
5. The main factor formula follows from the foregoing two endpoints:
   `selectedBody 7 (Ico 1 7) x u = 7*x*u*(x+u)*(x^2+x*u+u^2)^2`.
6. `add_pow_seven_eq_gap_add_interior` reuses `selectedGap_add_selectedBody` rather than replacing the observation with a fresh power expansion. The subtraction statement is correctly isolated under `CommRing`.
7. Endpoint transfer uses Step 003 `selectedBody_insert` and `selectedGap_insert`. Coefficient content changes 7 -> 1, consistently with existing gcd lemmas.
8. General `CommSemiring` regression cases include zero coordinates and arithmetic calibrations at (1,1), (2,3), (3,2). At (2,3), Gap 2315 + Body 75810 = 78125 = 5^7.
9. No number-field norm map or unit-power claim is present. `quadratic_form_four_mul` is correctly labeled as a polynomial identity.

## Codex's recorded checks

The `report-004.md` states successful focused builds for:

```text
lake build DkMath.Lib.Cosmic.GTailSeven
lake build DkMathTest.CosmicFormula.GTailSeven
lake build DkMath.Lib.Cosmic.GTailTransport DkMathTest.CosmicFormula.GTailTransport
```

The test runs `#print axioms` for all fifteen new endpoints, yielding only standard Lean axioms (fourteen lists are `[propext, Classical.choice, Quot.sound]`, the standalone quadratic-polynomial identity lists only `[propext]`). No added `axiom`, `sorry` or FLT owner dependency appears in the submitted source.

## Review decision

**APPROVED / Outcome B.** No blocking repair requested.

## Critical gate for Step 005

A direct theorem with hypothesis `a^7+b^7=c^7` is a logically conditional statement; because FLT7 itself is true, it could conceal a vacuous/circular proof if imported libraries already provide counterexample impossibility. The next step must therefore prove an **independent, satisfiable seven-power bridge** from the natural relation `a+b=c+g`, *without any Fermat equality assumption*.

A suitable target is, in `ℕ` (preferably a `CommSemiring` where appropriate):

```text
g * GTail 7 1 g c + c^7
  = (a^7+b^7) + 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

assuming `a+b=c+g`. The conditional FLT7 corollary must then use this unconditional balance and eliminate `a^7+b^7=c^7` by natural-number cancellation (or ring subtraction), with no imported FLT7 contradiction endpoint or ex falso.

Provide a satisfiable numeric regression of this unconditional bridge. Do not claim any FLT7 closure merely from its existence.
