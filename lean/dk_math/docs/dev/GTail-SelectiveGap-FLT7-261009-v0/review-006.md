# Review 006 — focused-gap arithmetic constraints and descent frontier

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Outcome B; local C findings documented for weakened proposals**

## Materials reviewed

- `DkMath/FLT/Seven/GTailConstraintAudit.lean` (68 lines)
- `DkMath/Lib/Cosmic/GTailSevenArithmetic.lean` (75 lines)
- `DkMathTest/FLT/Seven/GTailConstraintAudit.lean` (126 lines)
- `source-inventory-006.md`, `constraint-ledger-006.md`, `report-006.md` and `ROADMAP.md`
- Named dependency contracts from ``GTailBridge`, `GTailCongruence` and existing FLT7 modules, including `ModSevenSectors` and `DescentClosureAudit` (for overlap review).

**Review basis:** static inspection of the pushed GitHub Lean sources, theorem dependencies, test examples and Codex validation records; **no independent Lean build was executed in this review**.

## Proof findings

1. `fermat7_focused_bounds` uses the positive endpoints and the exact degree-seven interior term to prove `max a b < c` and `c < a+b`. This is a known power/height necessary condition with a GTail proof route, not a novel FLT7 obstruction.
2. `exists_positive_focused_gap` properly introduces `g=a+b-c` only after proving the necessary inequality, and gives `0<g`, `g<a`, `g<b`, `c+g=a+b`. No descent provider or next Fermat packet is constructed.
3. `seven_dvd_focused_gap` uses `gtail_seven_eq_of_fermat7Equation` and `prime_dvd_GN_iff_dvd_gap`; it does **not** assume `Nat.Coprime g c`. This is the existing mod-seven linear necessary condition via a new path.
4. The four neutral coprimality lemmas prove, from `Nat.Coprime a b`, that `a`, `b`, `a+b` and their product are coprime to `Q=a²+ab+b²`. Their proof uses ordinary, satisfiable natural coprimality arithmetic. They do not assert `Nat.Coprime g c` or `Nat.Coprime g Q`.
5. `gtail_seven_exact_seven_layer` obtains `7∣T` and `49∤T` for `T=GTail 7 1 g c` under `7∣g`, `7∤c` using the known mod-49 boundary congruence. This premise is weaker than full `Nat.Coprime g c`. The example `(g,c)=(14,2)` illustrates the distinction.
6. Neglected-premise examples are appropriately labeled: examples failing `Coprime g c` or `Coprime g Q` do not satisfy the full Fermat equation, so they refute only the weakened, *neutral* implication candidates.
7. The square-allocation examples establish that divisibility of `g*T` by `q²` does not by itself assign a square factor to either multiplicand. No erroneous one-sided allocation, product-to-prime-power inference, or assertion of FLT7 closure appears.
8. The report's proposed `v_7` / `v_q` equalities and `21∣q-1` residue-order target are clearly identified as **not yet Lean-proved**, with needed nonzero/unit/prime assumptions and overlap checks.

## Codex recorded validation (not rerun)

- `lake build DkMath.Lib.Cosmic.GTailSevenArithmetic` — final exit 0, 1060 jobs.
- `lake build DkMath.FLT.Seven.GTailConstraintAudit` — exit 0, 8935 jobs.
- `lake build DkMathTest.FLT.Seven.GTailConstraintAudit` — final exit 0, 8936 jobs.
- `lake build DkMath.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailBridge` — exit 0, 8932 jobs.
- Nine `#print axioms` audits report only standard foundations. The first two quadratic coprimality endpoints use `[propext, Quot.sound]`; the others include `Classical.choice` as reported.
- Final placeholder/unsafe/FLT-closure-pattern scan returned no matches; whitespace validation passed.

The first neutral build failed due to ordinary Lean elaboration issues and was repaired without weakening statements. No full clean/workspace build was performed in Step 006.

## Remaining frontier and Step 007 guidance

- **Not yet proved:** val_7(g) exact allocation, q-adic square allocation, q-order-21 condition, a typed Norm/UnitGauge transport, or a next primitive counterexample packet.
- **Not licensed:** using the smaller g as an infinite descent, imposing `Coprime g c` without a proof, or reading the scalar quadratic factor as a proven cyclotomic unit-power constraint.
- **Step 007:** promote only the reusable neutral `DkMath.Lib.Cosmic` modules to the public `DkMath.Lib` entrance, add the two FLT-specific modules to the FLT7 entrance with correct dependency direction, document clear direct/public imports, and validate regressions and axiom dependencies. Do not promote an FLT7 hypothesis-bearing module into Lib or silently label the proposed stronger local constraints as established.

## Decision

**APPROVED / Outcome B.** Step 006 is ready for integration work, not for an FLT7 closure announcement. Proceed to Instruction 007; no merge to `develop` is authorized by this review.
