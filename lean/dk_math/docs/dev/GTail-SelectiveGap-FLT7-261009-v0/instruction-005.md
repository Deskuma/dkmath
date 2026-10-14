# Instruction 005 — FLT7 GTail bridge with a nonvacuous seven-power shell

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Worktree: `lean/dk_math`  
Prerequisites: `review-001.md` through `review-004.md`  
Scope: **Step 005 only. Do not implement the Step 006 constraint audit.**

## Mission

Connect the completed degree-seven GTail selection/factor/transport calibration to the **existing FLT7 candidate interface**, while proving a **nonvacuous**, reusable shell identity before assuming any Fermat equation.

This is the first consumer under `DkMath.FLT.Seven.*`. The new owner module should be `DkMath/FLT/Seven/GTailBridge.lean`. Crucially, prove the bridge by finite algebra, not by importing a known Fermat impossibility result or using contradiction elimination from an inconsistent hypothetical counterexample packet.

Intended dependency direction:

```text
DkMath.Lib.Cosmic.GTailSeven  -->  DkMath.FLT.Seven.GTailBridge
DkMath.FLT.Seven.Basic       -->  DkMath.FLT.Seven.GTailBridge
```

Do not import broad `DkMath.FLT.Seven` facade (heavy unrelated modules) unless source inspection proves it truly unavoidable; do not import `DkMath.FLT.Three` or `DkMath.FLT.Five`. Keep all neutral math in the existing Lib layer and FLT-specific hypotheses in this owner.

## Phase 0 — inventory and anticycle audit

1. Confirm current branch, clean worktree, Step 004 report/approval.
2. Inspect:
   - `DkMath/Lib/Cosmic/GTailSeven.lean` and its relevant proof dependencies;
   - `DkMath/Lib/Cosmic/GTail.lean`, especially `add_pow_eq_mul_GTail_one_add_gap`;
   - `DkMath/FLT/Seven/Basic.lean`: `Fermat7Equation (x y z : ℕ)` and `CounterexamplePack`;
   - existing FLT7 boundary/gap/coprime lemmas, but avoid importing heavy owners;
   - Mathlib's `Nat.add_cancel`, `pow_pos`, `Nat.pow_lt_pow_iff_left` only as needed.
3. Write `source-inventory-005.md` with exact declaration signatures, intended imports, and an explicit search for potential FLT7 contradiction endpoints reachable via imports.
4. If `GTailBridge.lean` already exists by the time Codex runs, inspect and reconcile rather than overwrite.

## Phase 1 — nonvacuous generic algebraic bridge (mandatory FIRST)

Use any `{R : Type*} [CommSemiring R]`, arbitrary `a b c g : R` and the **only** hypothesis:

```text
hsum : a+b = c+g
```

From existing `add_pow_seven_eq_gap_add_interior` and `add_pow_eq_mul_GTail_one_add_gap` derive an additive shell such as:

```text
g * GTail 7 1 g c + c^7
  = (a^7+b^7) + 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

(The exact associativity/order of addends can be chosen to simplify the proof.) This is true **without** any FLT equation, positivity, coprimality, contradiction, or descent premise. Use the existing degree-seven selected factor theorem, not only `ring` normalization.

This theorem is essential to block vacuous "FLT7 bridge" proofs. Include at least one concrete satisfiable regression; for example, in natural numbers `a=2, b=3, c=4, g=1` has `a+b=c+g`, and the shell equality can be numerically checked. Do NOT impose Fermat equation on that regression.

Optionally provide a `CommRing` *defect identity*, derived from the same shell and typed clearly:

```text
g * GTail 7 1 g c
  = 7*a*b*(a+b)*(a^2+a*b+b^2)^2
    + (a^7+b^7-c^7)
```

The defect measures the deviation from the Fermat equation. A ring-specific statement is expected for this subtraction; never write unguarded natural subtraction in place of a ring identity.

## Phase 2 — conditional FLT7 bridge using only algebraic cancellation

Instantiate the shell at `R=ℕ`. Let:

```text
hEq : Fermat7Equation a b c     -- a^7 + b^7 = c^7
hsum : a + b = c + g
```

Prove the exact conditional theorem:

```text
g * GTail 7 1 g c
  = 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

**Mandatory proof route:**
- obtain the shell theorem using only `hsum`;
- rewrite `a^7+b^7` using `hEq` (unfold `Fermat7Equation` as needed);
- cancel the **same** `c^7` on the two sides via a valid natural addition cancellation lemma;
- finish without `exfalso`, `False.elim`, an imported FLT impossibility theorem, `simp [no_solution]`, or an unproved inequality.

Make an additional adapter from `CounterexamplePack a b c` **only if** it directly reuses the conditional theorem and brings no new circular dependencies. Do not make the counterexample packet the sole theorem interface.

## Phase 3 — focus Gap and possible height bound (strictly optional)

Potentially define `g = a+b-c` over naturals or use the existential form `∃ g, a+b=c+g`. Distinguish:

- The **identity** `a+b=c+g` requires `c ≤ a+b` if derived from Nat subtraction, and does not itself imply `g>0`.
- Under the hypothetical *positive* Fermat equation, one may try to show `c<a+b` by combining strict positivity of the interior factor with the degree-seven balance, hence construct `g>0`.
- `g<min(a,b)` additionally requires `c>max(a,b)`, obtainable algebraically from positive seventh powers under the Fermat equation. These are conditional and do not alone produce a new counterexample or a descending map.

Only implement these height/focus lemmas if the core shell and conditional bridge already have clean focused builds. If too costly, leave them as precisely stated targets for Step 006. **Do not** claim a strict FLT descent from the numerical inequality alone.

## Phase 4 — targeted test and evidence

Create `DkMathTest/FLT/Seven/GTailBridge.lean` (check nearest existing test naming convention first).

Required tests:

1. General-`CommSemiring` type-check for the shell, with no Fermat premise.
2. Satisfiable natural numeric example `a=2,b=3,c=4,g=1` through the shell proof, with independent arithmetic check.
3. Shell boundary cases `a=0` or `b=0` (show that the shell is unconditional; no fabricated positivity).
4. `Fermat7Equation` conditional theorem is an adapter derived **solely from the shell**, not from a closed FLT theorem or a contradiction.
5. Optional ring-defect form and optional Gap positivity/size lemmas, if proved.
6. `#print axioms` for all new public theorem endpoints.
7. Confirm that no previously proved FLT7 contradiction/closure endpoint is mentioned in the proof source, and no broad FLT7 façade import is added.

Build sequentially:

```text
lake build DkMath.FLT.Seven.GTailBridge
lake build DkMathTest.FLT.Seven.GTailBridge
lake build DkMath.Lib.Cosmic.GTailSeven DkMathTest.CosmicFormula.GTailSeven
```

Exact successful runs and failures/repairs, axiom audit, relative file paths, and dependency route must appear in `report-005.md`. Use small focused incremental builds, not a parallel clean workspace build.

## Classification and stop condition

- **Outcome B:** exact, nonvacuous general shell and conditional Fermat7Equation bridge are proved, but no independent FLT7 arithmetic obstruction is discovered. This is a successful Step 005.
- **Outcome A:** a genuinely new, noncircular and useful necessary arithmetic restriction on *hypothetical* positive primitive Fermat7 candidates is proved. The exact new restriction must be stated and separated from algebraic restatement; no surprise unconditional FLT7 claim.
- **Outcome C:** any proposed equation, carrier conversion or preservation condition is false, circular or needs unfulfilled hypotheses; report a counterexample or weakest corrected contract.

Deliver:
- `DkMath/FLT/Seven/GTailBridge.lean`
- `DkMathTest/FLT/Seven/GTailBridge.lean`
- `source-inventory-005.md`
- `report-005.md`
- Updated `ROADMAP.md`, truthful Step 005 state.

**STOP after Step 005.** Do not perform Step 006 (primitive gcd/valuation/unit-class obstruction search), Step 007 (facade export/full audit), merge to `develop`, or claim FLT7 has been proved.
