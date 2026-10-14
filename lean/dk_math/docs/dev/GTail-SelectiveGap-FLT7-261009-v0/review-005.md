# Review 005 — nonvacuous FLT7 GTail bridge

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Outcome B**

## Reviewed sources

- `DkMath/FLT/Seven/GTailBridge.lean` (64 lines)
- `DkMathTest/FLT/Seven/GTailBridge.lean` (75 lines)
- `source-inventory-005.md`, `report-005.md` and `ROADMAP.md`
- Existing `DkMath.FLT.Seven.Basic` and `DkMath.Lib.Cosmic.GTailSeven` interfaces

This is a **static GitHub source and report review**. Focused build and axiom results are supplied by Codex's documented local runs, **not independently reproduced by the reviewer**.

## Main findings

1. `gtail_seven_shell` is an honest `CommSemiring` theorem whose **only** assumption is `a+b=c+g`. Its proof reverses `add_pow_eq_mul_GTail_one_add_gap`, transports the additive relation, and uses the Step 004 semiring identity. It does not assume Fermat's equation.
2. `gtail_seven_defect` is a correct `CommRing` subtraction corollary of the shell. It must not be confused with subtraction over ℕ.
3. `gtail_seven_eq_of_fermat7Equation` explicitly rewrites `a^7+b^7=c^7` in the shell, commutes the same `c^7`, and uses `Nat.add_right_cancel`. There is no `False.elim` / `exfalso` or FLT7 impossibility endpoint in this proof.
4. `gtail_seven_eq_of_counterexamplePack` only extracts the equation field `h.hEq`. It does not silently infer positive gap, coprimality of g and c, descent, or a number-field norm.
5. The general shell has a satisfiable numeric regression at `(a,b,c,g)=(2,3,4,1)`, where both sides are 78125. The natural conditional adapter also has a satisfiable zero-boundary Fermat equation regression; it is not being "validated" by fabricating positive FLT7 solutions.
6. Direct imports are limited to `DkMath.Lib.Cosmic.GTailSeven` and `DkMath.FLT.Seven.Basic`. The latter's `import Mathlib` is existing, not newly introduced. Source proofs contain no known FLT7 closure references.
7. Codex's `report-005.md` records three successful focused builds and four public axiom lists `[propext, Classical.choice, Quot.sound]`. The first attempt on the test module failed due to excessive numerical simplifier recursion; a direct finite `decide` replaced that one check. This does not weaken a theorem statement.

## Approval and Step 006 research gate

**Approved with no blocking repairs.** The algebraic bridge is real, but it imposes no new obstruction by itself.

Step 006 must first distinguish:
- **unconditional/satisfiable arithmetic lemmas** about `a,b,g,c` or `Q=a²+ab+b²`;
- **conditional necessary constraints** obtained from `Fermat7Equation` or `CounterexamplePack`;
- **novel versus previously established** mod-7, gcd, valuation or descent facts.

Important prior interfaces discovered for the audit:

- `DkMath.Lib.Cosmic.GTailCongruence.prime_dvd_GN_iff_dvd_gap`: for prime p, `p ∣ GTail p 1 g u ↔ p ∣ g`, **without** a coprimality hypothesis.
- `DkMath.Lib.Cosmic.GTailBoundary.gcd_GN_eq_gcd_of_one_le` requires `Nat.Coprime g u`; this may **not** be assumed from `Nat.Coprime a b`.
- `DkMath.FLT.Seven.ModSevenSectors.fermat7Equation_modSeven_linear` already establishes the mod-7 linear residue relation and has heavier imports.
- `DkMath.FLT.Seven.DescentClosureAudit.AwayDescentClosureProvider` makes clear that a smaller integer alone is not a new FLT7 counterexample packet.

A proposed first consequence, `7∣g` under `Fermat7Equation` and `a+b=c+g`, is **mathematically correct but already follows from standard mod-7 Fermat congruence**. Do not label it a new obstruction. If proven by the GTail product route, label it an independent route or bridge regression and then seek additional information at mod 49, valuations, or coprime factor allocation.

Do not import heavy FLT7 owner files solely to get these results. Prove neutral lemmas separately if necessary, and document cross-checks by source path/theorem name.

## Status

Outcome B. Authorize Instruction 006, with a strict distinction between an arithmetic constraint and proof of FLT7 closure. No façade promotion or branch merge is authorized by this review.
