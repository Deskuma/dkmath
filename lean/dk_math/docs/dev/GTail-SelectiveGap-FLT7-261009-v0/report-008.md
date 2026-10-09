# Report 008 — focused seven-adic conservation calibration

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Step 008 COMPLETE — Outcome B.** Two neutral valuation endpoints and one conditional focused-gap balance are kernel checked. This is algebraic conservation, not a new contradiction or descent restriction. Optional unit-branch work is deferred.

## Exact changes

Paths relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailSevenValuation.lean`: two reusable natural-number valuation theorems.
- `DkMath/FLT/Seven/GTailValuationAudit.lean`: conditional balance using only the small constraint owner and neutral valuation module.
- `DkMathTest/CosmicFormula/GTailSevenValuation.lean`: seven nonvacuous/boundary/missing-premise examples and both neutral axiom prints.
- `DkMathTest/FLT/Seven/GTailValuationAudit.lean`: one conditional interface example and its axiom print.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-008.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-008.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/validation-addendum-007.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`: post-integration experiment status and subsequent owner evidence link.

Existing mathematics, Lib/Seven facades, root driver, report-007, constraint-ledger-006, Lake settings and LegendreMergedCRT remain unchanged. New direct modules/tests follow the MIT header, import, file-print and namespace style. Tests are discoverable through the configured submodule glob; no broad facade promotion was added.

## Exact public signatures

In `DkMath.CosmicFormula`:

```lean
theorem padicValNat_gtail_seven_eq_one {g c : ℕ}
    (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 (GTail 7 1 g c) = 1

theorem padicValNat_gap_mul_gtail_seven {g c : ℕ}
    (hg : g ≠ 0) (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 (g * GTail 7 1 g c) = padicValNat 7 g + 1
```

In `DkMath.FLT.Seven`:

```lean
theorem padicValNat_focused_gap_balance {a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) (hend : ¬ 7 ∣ c) :
    padicValNat 7 g = padicValNat 7 a + padicValNat 7 b +
      padicValNat 7 (a + b) + 2 * padicValNat 7 (a ^ 2 + a * b + b ^ 2)
```

## Proof route and nonzero discipline

The Step 006 exact layer gives 7∣T and ¬7²∣T. Since 7² divides zero, its nondivisibility forces T≠0. Existing `Vp_ge_one_iff` gives valuation at least one; existing power-divisibility equivalence excludes valuation at least two. Natural arithmetic yields exactly one. This residual theorem is stronger in its boundary coverage than the requested nonzero-gap version: g≠0 is unnecessary for T itself.

For g*T, both g and T are nonzero and `[Fact (Nat.Prime 7)]` is explicitly supplied to `padicValNat.mul`. The conditional theorem derives c<a+b from the proved height bound and then g≠0 from hsum; `seven_dvd_focused_gap` provides 7∣g. Positive a,b imply nonzero a,b,a+b,Q and Q² and all intermediate product factors. Apply `congrArg (padicValNat 7)` to the exact GTail/Fermat product and expand its products and Q². The two sides become `v7(g)+1` and `1+v7(a)+v7(b)+v7(a+b)+2*v7(Q)`. `omega` cancels the common one with no truncated subtraction. No full gap-endpoint coprimality is assumed.

Mathlib's `padicValNat.pow` has only the prime Fact instance and no base-nonzero premise; the base is positive here anyway. The multiplicativity premises cannot be omitted. No new general valuation definition is introduced.

## Focused compilation evidence

Cwd `lean/dk_math`; process-local `LEAN_NUM_THREADS=2`. Commands were sequential incremental builds. No clean, root/facade build, full DkMathTest run, memory/configuration change or profiling in Step 008. Raw local logs: `.lake/build/gtail-step008/`. For the first four invocations no wrapper elapsed duration was recorded (Lean's individual module timing is not substituted for total duration).

| Command | Exit | Seconds | Local raw log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailSevenValuation` | 0 | not recorded | `01-neutral.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailValuationAudit` | 0 | not recorded | `02-owner.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenValuation` (initial) | 1 | not recorded | `03-neutral-test.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenValuation` (repaired) | 0 | not recorded | `04-neutral-test-repair.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailValuationAudit` | 0 | 19.76 | `05-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailPadic` | 0 | 1.55 | `06-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSeven` | 0 | 1.45 | `07-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailBridge` | 0 | 8.24 | `08-focused.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailConstraintAudit` | 0 | 8.24 | `09-focused.log` |

The initial neutral test failed only in the finite `(7,7)` divisor computation: `norm_num [GTail, Finset.sum_range_succ]` reached the simplifier recursion limit. Replaced the concrete nonzero/divisibility checks with ordinary kernel-checked `decide`, without increasing limits or changing any theorem/hypothesis. The repaired module passes. No false valuation inference was found, so this local tactic repair is not Outcome C.

Relevant earlier degree-seven, bridge and constraint regressions pass; the existing generic GTailPadic module also passes. All three new endpoint `#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`. No sorryAx or additional axiom. The successful new test logs contain no warnings/errors.

## Dependency and source audit

Comment-stripped import-header closure audit: neutral production module 1082 source names / 6 local DkMath modules; conditional owner 8795 / 15; neutral test 1083 / 7; conditional test 8796 / 16. External terminal module names are counted, implicit compiler/native dependencies are not. These counts are source reachability, not build jobs or declaration-hole guarantees. DFS passes for the union's 17 local modules, with zero FLT modules in the neutral closure. No descent/closure owner or Seven facade is reachable through these local imports. Existing Basic's broad Mathlib import accounts for the large external owner closure. Complete names are stored locally in `imports.json`.

Whole-word sorry/admit/axiom/unsafe, False.elim/exfalso and unconditional FLT impossibility patterns: no matches in the four new Lean sources (rg exit 1 for the empty scan). All three axiom checks use standard foundations. `git diff --check` and a separate new-file trailing-whitespace/final-newline check pass. Ledger and LegendreMergedCRT byte comparison against HEAD passes.

## Overlap and classification

The generic `GTailPadic.padicValNat_GN_prime_eq_one_of_dvd_gap` already supplies residual valuation one with full Coprime g c for odd primes. This new seven-specific endpoint packages the weaker endpoint-unit condition already proved in Step 006. `(14,2)` with gcd 2 distinguishes the contracts; this is useful API coverage, not claimed new p-adic mathematics.

Existing FLT7 `CounterexampleRouting.padicValNat_GN_seven_eq_one_of_counterexample` and `padicValNat_gap_shape_of_counterexample` concern z-y with a primitive packet and a seventh-power factor equation. `PrimitiveCyclotomicDepth.padicValNat_GN_seven_sub_eq_one_iff` concerns a-b with primitive coordinates. They were inspected only, not imported or used to assume a+b-c is primitive. The new conditional sum-focus identity closes the particular deferred valuation-calculation item in report-006; it supplies no separate arithmetic obstruction. **Outcome B**, not A or unconditional FLT7.

## Lean結果からの気づき・試したexample・提案

1. **確認済み:** `(g,c)=(7,2)` と `(14,2)` では尾の付値が1、積の付値が2。後者では全体のgcdが2であり、7の端点単元だけで十分なことを確認しました。
2. **確認済みの欠落仮定反例:** `(7,7)` では7∣gを満たしても49∣T、v7(T)≠1。端点単元仮定を外した正確な一段の主張は成立しません。これはFermat候補の反例ではなく、中立条件の反例です。
3. **確認済みの零境界:** `(0,2)` でもv7(T)=1ですが、v7(0*T)=v7(0)=0。padicValNatは零で0なので、積の式をg≠0なしに延長できません。両APIで非零仮定を区別する理由です。
4. **条件付き型検査:** 正のa,bとFermat方程式を仮定した保存式をexampleで適用しました。正のFermat解を具体例として捏造していません。等式の成立だけで解の存在や非存在は推論できません。
5. **今後の候補（今回未実装）:** 単元分岐では、まず既存mod-7線形合同と¬7∣cから¬7∣a+bを明示的に導く必要があります。a,bが単元でも和が単元とは限りません。その証明後に付値式の簡約と49∣gを試し、既存mod-49必要条件との同値性・重複を確認できます。今回その分岐を独立障害と分類する証拠はなく、定理追加もしていません。
6. **実装提案:** 実験時はこの直接importを使用し、公開facadeへの追加は別の統合判断に分けると、局所算術の仮定と依存を追いやすくなります。一般素数への端点単元版拡張も考えられますが、本指示の範囲では実装していません。

## Step 007 evidence and frontier

[validation-addendum-007.md](validation-addendum-007.md) records the owner's subsequent `./lb -T` success, the actual lake-test route, log digest, coverage and runtime-commit evidence limitation. It does not overwrite the historical interrupted run or pretend a new Codex all-suite execution occurred. The old 683-submodule run does not cover the new Step 008 modules; those are validated by the focused commands above.

[constraint-ledger-006.md](constraint-ledger-006.md) stays byte-identical as a historical ledger. Its deferred exact v7(g) equality is now proved under precisely ha,hb,hEq,hsum,hend by the new endpoint. The optional unit restriction, q² allocation, order-21, typed cyclotomic Norm/unit-power-class transfer and constructive next packet remain unproved in this checkpoint. No new descent provider, large search, Legendre optimization, PR or merge. Stop after this calibration.
