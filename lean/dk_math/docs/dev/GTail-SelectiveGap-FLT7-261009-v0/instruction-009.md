# Instruction 009 — GTail seven-unit branch

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Scope: Step 009 only; no FLT7 closure.

## Purpose

Use Step 008's exact valuation conservation to inspect the seven-unit branch. Produce checked necessary conditions, a satisfiable arithmetic calibration, and an explicit distinction between exact Fermat equations and compatibility modulo 49.

## 0. Inventory

Read `GTailValuationAudit`, `GTailConstraintAudit`, `GTailSevenValuation`, `PadicValNat`, and the existing FLT7 mod-7/mod-49/mod-343 theorem interfaces. Record signatures, hypotheses, and overlap in `source-inventory-009.md`. Preserve the direct-import dependency direction.

## 1. Unit transfer

Given `hEq : Fermat7Equation a b c`, `hsum : a+b=c+g`, and `¬7∣c`, prove `¬7∣a+b` using the already proved `seven_dvd_focused_gap` and divisibility of sums. Do not assume two seven-units have a unit sum.

## 2. Exact focused branch

Under `0<a`, `0<b`, the above equation/coordinate relation, and `¬7∣a`, `¬7∣b`, `¬7∣c`, derive:
- `padicValNat 7 g = 2 * padicValNat 7 (a^2+a*b+b^2)`;
- `7 ∣ a^2+a*b+b^2`;
- `49 ∣ g`.

Use `padicValNat_focused_gap_balance`. Show valuation zero for a,b,a+b; prove g nonzero from positive focused height. Convert valuation lower bounds to prime-power divisibility with explicit nonzero hypotheses. An adapter from `¬7∣a*b*c` is optional.

## 3. Avoid vacuous tests

Where practical, prove a neutral abstract-product allocation theorem. For nonzero g,T,A,B,C,Q with `g*T=7*A*B*C*Q^2`, `padicValNat 7 T=1`, and A,B,C each prime-to-seven, derive `v7(g)=2*v7(Q)`; with `7∣g` deduce `49∣g`. An abstract satisfiable instance is g=49,T=7,A=B=C=1,Q=7. This is *not* a sample Fermat solution.

Add a checked *mod-49-only* example (a,b,c,g)=(8,9,10,7): a+b=c+g, gcd(a,b)=1, all a,b,c are seven-units, focused height bounds hold, and `(a^7+b^7)%49=c^7%49`, while `49∤g` and the exact Fermat equation is false. This shows why an exact equation cannot be replaced by a residue congruence.

## 4. Audit and delivery

Compare the unit-branch conclusion with existing FLT7 local/mod-343 constraints by source path and theorem name; do not claim novelty without evidence. The separate q-square allocation, order-21, cyclotomic Norm, unit-class and constructive descent problems remain open.

Suggested files: `DkMath/FLT/Seven/GTailSevenUnitAudit.lean` and `DkMathTest/FLT/Seven/GTailSevenUnitAudit.lean`, plus optional small neutral allocation lemma/test. Write `report-009.md` and update the project `ROADMAP.md`.

Build created modules and Step 008 regressions sequentially. Log commands and exit codes; audit all new public axioms and import cycles, and check no proof placeholders or circular FLT7 impossibility use. Do not run the expensive complete test suite or edit LegendreMergedCRT.

Report Outcome B for correct conditional necessary conditions without new obstruction, or Outcome C for a false proposed inference with a concrete counterexample. Stop at Step 009. No PR or merge.
