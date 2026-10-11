# Report 009 — seven-unit focused branch

Date: 2026-10-09 (JST). Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Step 009 COMPLETE — Outcome B.** Six public endpoints package neutral allocation and conditional necessary unit-branch consequences. No independent obstruction or unconditional FLT7 claim.

## Exact changed files

Relative to `lean/dk_math`:

- `DkMath/Lib/NumberTheory/SevenUnitAllocation.lean`: two neutral endpoints, sole import Lib.NumberTheory.PadicValNat.
- `DkMath/FLT/Seven/GTailSevenUnitAudit.lean`: four conditional endpoints, imports GTailValuationAudit and the new neutral allocation module.
- `DkMathTest/NumberTheory/SevenUnitAllocation.lean`: four arithmetic examples, including theorem-applying satisfiable abstract product and missing-unit sanity check; two axiom prints.
- `DkMathTest/FLT/Seven/GTailSevenUnitAudit.lean`: eight examples, including four conditional interfaces, unit-sum warning, complete mod49-only calibration, Q divisibility and failure of exact valuation balance on that calibration; four axiom prints.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-009.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-009.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`

No prior source, facade, root test driver, constraint ledger, LegendreMergedCRT or Lake configuration change. Existing MIT header/import/file-print/doc/namespace style is maintained. The two direct-import tests are discoverable through the submodule glob; no broad public promotion.

## Exact signatures

Neutral namespace `DkMath.Lib.NumberTheory`:

```lean
theorem padicValNat_seven_unit_product {g T A B C Q : ℕ}
    (hg : g ≠ 0) (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hprod : g * T = 7 * A * B * C * Q ^ 2)
    (hval : padicValNat 7 T = 1)
    (huA : ¬ 7 ∣ A) (huB : ¬ 7 ∣ B) (huC : ¬ 7 ∣ C) :
    padicValNat 7 g = 2 * padicValNat 7 Q

theorem fortyNine_dvd_of_seven_dvd_of_valuation_double {g Q : ℕ}
    (hg : g ≠ 0) (hgap : 7 ∣ g)
    (hval : padicValNat 7 g = 2 * padicValNat 7 Q) :
    49 ∣ g
```

Conditional namespace `DkMath.FLT.Seven`:

```lean
theorem not_seven_dvd_sum_of_focused_equation {a b c g : ℕ}
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g) (hc : ¬ 7 ∣ c) :
    ¬ 7 ∣ a + b

theorem padicValNat_focused_gap_unit_balance {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    padicValNat 7 g = 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2)

theorem seven_dvd_quadratic_of_focused_units {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    7 ∣ a ^ 2 + a * b + b ^ 2

theorem fortyNine_dvd_focused_gap_of_units {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hua : ¬ 7 ∣ a) (hub : ¬ 7 ∣ b) (huc : ¬ 7 ∣ c) :
    49 ∣ g
```

## Proof route

1. Derive 7∣g through `seven_dvd_focused_gap hEq hsum`. If 7∣a+b, rewrite by hsum and use `Nat.dvd_add_left` with 7∣g to get 7∣c, violating the explicit endpoint-unit hypothesis. Thus the sum unit is proved from the exact equation, not assumed from input units.
2. Use Step 008 `padicValNat_focused_gap_balance` and valuation-zero facts for a,b,a+b to obtain v7(g)=2*v7(Q). No primitivity or gcd hypothesis is needed for these exact conditional results.
3. Positive height gives c<a+b, and hsum forces g≠0. Its known seven-divisibility gives 1≤v7(g). The doubled valuation then gives 1≤v7(Q). Positive a,b give Q≠0, so `Vp_ge_one_iff` implies 7∣Q.
4. A positive even v7(g) is at least two. The neutral conversion theorem uses g≠0 and `padicValNat_le_iff_dvd` to conclude 7²∣g, hence 49∣g.

The neutral abstract-product proof separately expands both sides of g*T=7*A*B*C*Q² with all six factors nonzero and the prime Fact instance. Units A,B,C contribute zero, T and the visible coefficient 7 each contribute one; natural arithmetic cancels those common layers. Composing with known 7∣g yields 49∣g. This algebra is satisfiable independently of an FLT equation.

## Checked arithmetic and exact-vs-residue boundary

- **Satisfiable abstract allocation:** g=49,T=7,A=B=C=1,Q=7. Exact product 343=343, residual valuation one, all ordinary factors units. The examples apply the allocation theorem and conversion theorem to prove doubled valuation and 49∣g. T is an abstract residual, not asserted to equal a GTail at Fermat coordinates.
- **Ordinary-unit hypothesis matters:** g=T=7,A=B=1,C=7,Q=1 still satisfies the product but 49∤g. This sanity check omits precisely the C-unit premise; it is not a counterexample to the proved theorem.
- **Unit sum is not automatic:** 1 and 6 are seven-units, but 7∣1+6. The exact-equation sum-unit theorem avoids this unjustified inference.
- **Specified mod49-only example:** a=8,b=9,c=10,g=7. Lean checks a+b=c+g; Coprime a b; all three coordinates are seven-units; max a b<c<a+b; 0<g<a,b; `(a^7+b^7)%49=c^7%49`; 49∤g; and ¬Fermat7Equation a b c. Q=217=7*31 is divisible by seven.
- **Additional checked diagnostic:** at that same residue-only example v7(g)=1 and v7(Q)=1, so v7(g)≠2*v7(Q). Both the exact doubled identity and 49-divisibility fail if the exact equation is replaced by mod49 compatibility, despite the height, coprimality, coordinate units and Q-divisibility checks. This is a counterexample to the weakened residue-only contract, not the conditional exact theorem.

All numeric `decide` checks use ordinary kernel checking. Conditional interfaces are tested with explicit hypotheses and never fabricate a positive exact Fermat solution.

## Sequential focused build record

Cwd `lean/dk_math`; process-local `LEAN_NUM_THREADS=2`; incremental builds, no clean/full suite or heavy facade build. All command exit codes and durations are captured by the local wrapper in `.lake/build/gtail-step009/runs.json` with raw logs.

| Command | Exit | Seconds | Local raw log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.SevenUnitAllocation` | 0 | 3.44 | `01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailSevenUnitAudit` | 0 | 13.99 | `02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.SevenUnitAllocation` | 0 | 3.29 | `03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailSevenUnitAudit` | 1 | 14.14 | `04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailSevenUnitAudit` | 0 | 13.55 | `05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenValuation` | 0 | 1.59 | `06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailValuationAudit` | 0 | 8.05 | `07-build.log` |

The initial owner test failed to synthesize Decidable for a conjunction ending in the named Fermat7Equation. Unfolded that definition before the concrete `decide` check; the corrected module and added valuation diagnostic pass. No theorem statement or premise changed. This was a test elaboration repair, not a false exact-equation inference. Both Step 008 regression modules pass afterward.

## Axioms, dependencies and hygiene

All six new public endpoints were printed in their successful direct tests. Each has exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx/additional axiom. The final new test logs contain no warning/error. A source scan over all four new Lean files for whole-word sorry/admit/axiom/unsafe, False.elim/exfalso and unconditional FLT impossibility patterns has no matches (rg exit 1 for the empty search).

Comment-free import-header closure audit: neutral owner 1074 names (2 local), conditional owner 8797 (17 local), neutral test 1075 (3 local), conditional test 8798 (18 local). DFS passes on the 19 local-module union; neutral has zero FLT modules, and neither owner imports the Seven facade or heavy routing/descent/closure owners. Complete lists are local `imports.json`. Source-name counts include external terminals and omit implicit compiler/native dependencies; they are not job counts or proof-hole guarantees. Existing Basic's Mathlib import remains unchanged.

`git diff --check` and new-file final-newline/trailing-whitespace review pass. Prior valuation sources, facades, ledger, LegendreMergedCRT and Lake settings are byte-identical to HEAD.

## Local constraint overlap and classification

[source-inventory-009.md](source-inventory-009.md) records actual names/hypotheses for existing mod7, mod49 and mod343 interfaces. In particular:

- `ModSevenSectors.fermat7Equation_modSeven_linear` already expresses the linear mod7 necessity. The new sum-unit endpoint uses the small proved gap-divisor route instead of importing that owner.
- `PrimitiveCyclotomicDepth.not_fortyNine_dvd_cyclotomicSeven` excludes a second layer in a difference-gap residual with a unit endpoint. It does not exclude the second layer in this sum-focused carrier; the allocations concern different factors/coordinates.
- `SevenBaseTerminalRamifiedUnitClassAudit.RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff_residue` classifies an explicit packet unit into six residues. A scalar doubled valuation gives no such typed unit receiver.
- `SevenRamifiedFusionAllocationResidueSieve.nested_full_gap_residue_sieve` and `nestedGNResidual_residue_sieve` give mod343 sixth-power necessities from stronger nested allocation congruences/equalities. Their hypotheses are not implied by ordinary mod49 compatibility, and no bridge/equivalence is proved here.

This bounded source comparison supports **Outcome B**: correct exact conditional necessary conditions and neutral calibration, without demonstrated novelty as an independent FLT7 obstruction. No routing or cyclotomic theorem was imported as a contradiction source.

## Lean結果からの気づき・example・実装提案

1. **確認済み:** Step 008保存式を単元分岐へ簡約すると、gの付値が偶数になります。既存7∣gと正性を加えて初めて49∣gが出ます。零でpadicValNatが0になる点を、非零仮定で明示的に除外しています。
2. **確認済み:** 今回の条件付き結論にはNat.Coprime a bが不要です。単元仮定・正性・正確な方程式だけを保持しました。mod49反例は互いに素な座標も満たすため、そこにprimitivityを追加しても合同のみからの推論は救えません。
3. **確認済み:** Qの7整除性は指定mod49例にも成立します。しかしv7(g)=2*v7(Q)は不成立です。因子の合同・整除だけと、正確な積等式に基づく付値配分は異なる情報です。
4. **実装提案（未実施）:** 将来のAPI整理では¬7∣a*b*cを三つの単元仮定へ分解する薄いadapterを検討できます。今回の主要命題は明示的な三仮定のままにして、仮定の消費箇所を追える形にしました。
5. **比較提案（未実施）:** 単元分岐と既存のmod49/mod343必要条件との含意を調べるなら、各packet・座標・端点単元を指定した小さいtyped bridgeが必要です。今回の付値恒等式から、そのbridgeや次の候補を作れるとは主張しません。

## Frontier and stop

The historically deferred seven-unit consequence is now checked under the exact positive equation and explicit unit hypotheses. The original [constraint-ledger-006.md](constraint-ledger-006.md) stays intact; this report/ROADMAP records the new status. Separate q-square distribution, order-21, cyclotomic Norm, residual unit class and constructive descent remain open. A smaller/divisible focused gap does not supply a new primitive Fermat packet. Stop at Step 009; no full test suite, unrelated Legendre edits, PR or merge.
