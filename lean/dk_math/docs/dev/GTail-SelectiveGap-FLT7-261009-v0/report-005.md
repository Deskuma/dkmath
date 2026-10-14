# Report 005 — nonvacuous seven-power shell and conditional FLT7 bridge

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Classification: **Outcome B**. Step 005 complete; Step 006–007 deferred.

## Changed files

- `DkMath/FLT/Seven/GTailBridge.lean`
- `DkMathTest/FLT/Seven/GTailBridge.lean`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-005.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-005.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`

Existing sources, Basic's imports, Lib kernels and façades were not changed.
License headers, import ordering, file-print markers and docstrings follow the established style.

## Exact public contracts

Namespace: `DkMath.FLT.Seven`; `GTail` is `DkMath.CosmicFormula.GTail`.

```lean
theorem gtail_seven_shell {R : Type*} [CommSemiring R] (a b c g : R)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c + c ^ 7 = (a ^ 7 + b ^ 7) +
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2

theorem gtail_seven_defect {R : Type*} [CommRing R] (a b c g : R)
    (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2 +
        (a ^ 7 + b ^ 7 - c ^ 7)

theorem gtail_seven_eq_of_fermat7Equation {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2

theorem gtail_seven_eq_of_counterexamplePack {a b c g : ℕ}
    (h : CounterexamplePack a b c) (hsum : a + b = c + g) :
    g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2
```

## Proof route and nonvacuity

The first theorem assumes only a+b=c+g in an arbitrary CommSemiring. Reverse the existing r=1 tail balance to obtain (g+c)^7, transport the additive relation, then apply the Step 004 selected Gap/Body identity. The latter already uses the general selection and factor kernels; no independent ring expansion replaces that derivation.
The ring defect follows by linear combination of this same shell. Subtraction is confined to CommRing.
The natural conditional bridge obtains the shell, unfolds Fermat7Equation, rewrites a^7+b^7=c^7, commutes the endpoint and applies Nat.add_right_cancel. The packet adapter uses only h.hEq; positivity and coprimality are not consumed.

Direct dependency: Lib.GTailSeven + FLT.Seven.Basic -> FLT.Seven.GTailBridge. The recursive import audit found seven local DkMath modules and 8833 total module names (including public/private imports). Basic's existing Mathlib import reaches exponent-three/four and polynomial FLT APIs; these are not proof dependencies used here. See inventory for exact audit limits. No broad DkMath FLT facade or Three/Five owner import and no contradiction endpoint appear in either new source.

## Regression evidence

- General CommSemiring type check, with the additive relation only.
- Satisfiable a=2,b=3,c=4,g=1: shell proof without Fermat premise. Both sides independently evaluate to 78125; the left uses direct kernel `decide` on the finite GTail definition, the right uses norm_num.
- General a=0 and b=0 shell cases with no positivity.
- Independent reconstruction of the natural conditional proof from shell and cancellation; satisfiable boundary Fermat equation a=0,b=3,c=3,g=0 checks the public adapter.
- Packet-adapter type check and general CommRing defect type check.

## Sequential validation and repairs

All target builds below run from `lean/dk_math`.

1. An initial invocation from the repository root failed (exit 1): no Lake configuration at that root. Corrected working directory; no source change needed.
2. `lake build DkMath.FLT.Seven.GTailBridge`: exit 0, 8931 jobs, owner built in 6.9s.
3. First `lake build DkMathTest.FLT.Seven.GTailBridge`: exit 1. The direct numerical `norm_num [GTail, Finset.sum_range_succ]` reached simp's recursion limit. A local maxRecDepth 2048 retry also failed (exit 1); this temporary option was removed. Replaced that one direct arithmetic check with kernel `decide`. All contracts and production proofs unchanged.
4. Final `lake build DkMathTest.FLT.Seven.GTailBridge`: exit 0, 8932 jobs, test built in 6.2s; no warnings/errors.
5. `lake build DkMath.Lib.Cosmic.GTailSeven DkMathTest.CosmicFormula.GTailSeven`: exit 0, 1069 jobs; replayed all 15 Step 004 axiom checks.
6. `rg -n '\b(sorry|admit|axiom|unsafe)\b|False\.elim|exfalso|no_solution|fermatLastTheorem|^import DkMath\.FLT\.(Three|Five|Seven)$' DkMath/FLT/Seven/GTailBridge.lean DkMathTest/FLT/Seven/GTailBridge.lean`: no matches, exit 1 (expected for an empty search).
7. `git diff --check`: exit 0. Separate whitespace/final-newline check of all four newly created files passed.

## Axiom audit

The final test printed all new public endpoints:

```text
DkMath.FLT.Seven.gtail_seven_shell: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_defect: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_eq_of_fermat7Equation: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.gtail_seven_eq_of_counterexamplePack: [propext, Classical.choice, Quot.sound]
```

Only standard Lean foundations; no added axiom or sorryAx. The axiom list alone does not establish noncircularity: the explicit shell/cancellation source route supplies that evidence.

## Scope and stop

Outcome B: a nonvacuous general shell and exact conditional Fermat7Equation bridge are proved. No independent arithmetic obstruction, primitive gcd/valuation/unit-class restriction, carrier norm conversion or strict descent is asserted. Optional height lemmas remain targets for Step 006: under positive natural Fermat hypotheses establish c<a+b, choose g with a+b=c+g and 0<g, and use c>max(a,b) for g<min(a,b). None is implemented here. Step 006 constraint search and Step 007 façade/full audit are not performed. No FLT7 closure claim.
