# Report 006 — GTail FLT7 constraints and descent frontier

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Outcome B. Step 006 complete; stop before Step 007.**

The mandatory positive focused-gap certificate and prime-seven divisibility checkpoint are proved. Four neutral quadratic coprimality endpoints and an explicit endpoint-unit residual layer are checked on satisfiable inputs. The focus is arithmetic information with honest premises; none is promoted to an independent FLT7 obstruction or closure.

## Changed paths

Paths relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailSevenArithmetic.lean`
- `DkMath/FLT/Seven/GTailConstraintAudit.lean`
- `DkMathTest/FLT/Seven/GTailConstraintAudit.lean`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-006.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/constraint-ledger-006.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-006.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`

Existing FLT7 owners and neutral kernels are unchanged. New Lean files use the established MIT header, imports, file-print marker and documentation style. No facade exports are added.

## Exact public theorem signatures

Neutral namespace: `DkMath.CosmicFormula`. Owner namespace: `DkMath.FLT.Seven`.

### DkMath/Lib/Cosmic/GTailSevenArithmetic.lean

```lean
theorem coprime_left_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime a (a ^ 2 + a * b + b ^ 2)

theorem coprime_right_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime b (a ^ 2 + a * b + b ^ 2)

theorem coprime_sum_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (a + b) (a ^ 2 + a * b + b ^ 2)

theorem coprime_product_seven_quadratic {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2)

theorem gtail_seven_exact_seven_layer {g c : ℕ} (hgap : 7 ∣ g) (hend : ¬ 7 ∣ c) :
    7 ∣ GTail 7 1 g c ∧ ¬ 7 ^ 2 ∣ GTail 7 1 g c
```

### DkMath/FLT/Seven/GTailConstraintAudit.lean

```lean
theorem fermat7_focused_bounds {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) : max a b < c ∧ c < a + b

theorem focused_gap_lt_coordinates {a b c g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) (hsum : c + g = a + b) : g < a ∧ g < b

theorem exists_positive_focused_gap {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hEq : Fermat7Equation a b c) :
    ∃ g : ℕ, 0 < g ∧ g < a ∧ g < b ∧ c + g = a + b

theorem seven_dvd_focused_gap {a b c g : ℕ} (hEq : Fermat7Equation a b c)
    (hsum : a + b = c + g) : 7 ∣ g
```

## Proof dependencies and interpretation

The max bound reuses Basic.right_lt_of_fermat7Equation twice, with a symmetric equation for the other coordinate. The upper bound explicitly proves positivity of Q and the interior factor, rewrites the selected degree-seven balance, then uses Nat.pow_lt_pow_iff_left. This uses the selected-factor API as a route to a known strict power inequality; it does not add a new arithmetic obstruction.
The focused certificate uses g=a+b-c only after c<a+b, and Nat.add_sub_of_le at that bound. Any gap satisfying c+g=a+b has g<a and g<b. A separate hz premise is unnecessary because ha,hb and the equation already give c>max(a,b).

Seven divisibility uses exactly the Step 005 bridge: 7 divides its RHS, primality splits the product, and either g is divisible or prime_dvd_GN_iff_dvd_gap converts tail divisibility to gap divisibility. No Coprime g c is assumed. Existing ModSevenSectors.fermat7Equation_modSeven_linear already proves the corresponding residue relation. This endpoint is a **known necessary condition with a new GTail proof route**.

The first Q coprimality rewrites Q=b²+a*(a+b) and cancels the multiple of a; the second uses symmetry. For the sum, Q+ab=(a+b)² forces a common divisor to divide ab, against Coprime (a+b) (ab). Combining the three endpoints localizes primes dividing Q away from a*b*(a+b). These are neutral natural arithmetic lemmas, not claims about coprimality of g with c or Q.

The residual endpoint gives 7∣T and ¬49∣T from 7∣g and ¬7∣c alone. The mod-49 head is 7*c^6; a supposed second layer would divide that head, cancellation would force 7∣c. This weakens the full gap/endpoint coprimality premise of GTailPadic.not_prime_sq_dvd_GN_of_dvd_gap for this degree-seven receiver. It does not claim a new p-adic theorem; padicValNat=1 is not an added endpoint.

Direct neutral imports: GTailCongruence, Nat.GCD.Basic, NormNum, Ring. Direct owner imports: GTailBridge and GTailSevenArithmetic. Recursively verified closures: neutral 1518 module names with four local DkMath modules; owner 8838 names with twelve local DkMath modules. The exact lists are in source-inventory-006. Basic's existing broad Mathlib import remains; no CounterexampleRouting, ModSevenSectors, DescentClosureAudit, GTailPadic, norm carrier or other heavy FLT7 owner is imported. Source proof routes contain no FLT7 impossibility invocation or contradiction elimination on the arithmetic goals.

## Checked examples and missing-premise findings

- All four conditional owner theorem interfaces are type-checked without fabricated positive Fermat candidates; the prime-divisor proof is independently reconstructed in the test.
- The zero-boundary Fermat equation (0,3,3) exercises the seven-divisibility endpoint with g=0. It is not a positive height example.
- The neutral prime address holds for arbitrary g,c. At (g,c)=(7,2), 7 divides the row; at (1,4), neither g nor the row is divisible by seven, checked independently by kernel arithmetic.
- Q coprimality holds on (2,3) and the boundary (0,1). The claimed conclusion fails after dropping primitive-pair coprimality, at (2,2). A general prime-exclusion example schema checks the consequence q∣Q -> q∤a*b*(a+b).
- (g,c)=(14,2) has gcd=2, but 7∣T and ¬49∣T. Thus the explicit endpoint-unit premise is strictly weaker than Coprime g c. Dropping it fails at (7,7), where 49∣T.
- (a,b,c,g)=(11,17,21,7) satisfies primitive-pair coprimality, c+g=a+b, max(a,b)<c, 0<g<min(a,b), and 7∣g; nevertheless gcd(g,c)=7.
- (8,11,12,7) additionally has Coprime g c but Q=273 and gcd(g,Q)=7. Both examples are explicitly checked **not** to satisfy Fermat7Equation. They refute weakened neutral inference rules, not conclusions under the full positive Fermat premise.
- 9∣3*3 does not imply 9∣3. Also 9∣3*GTail 7 1 3 3 with ¬9∣3. These are neutral allocation sanity checks and omit the FLT/coordinate premises; they must not be presented as counterexamples to a full FLT-conditioned allocation theorem.
- (1,2,3) satisfies the seventh-power equation modulo 49 and 7∣Q, but not the exact Fermat equation. This is a checked warning against treating finite residue compatibility as a solution or an obstruction.

## Sequential focused validation

All commands run from `lean/dk_math`.

| Command / attempt | Result |
| --- | --- |
| First `lake build DkMath.Lib.Cosmic.GTailSevenArithmetic` | exit 1: symmetry simplification changed the coprime expression; dvd_add orientation mismatch; narrow norm_num did not prove Prime 7 |
| Corrected `lake build DkMath.Lib.Cosmic.GTailSevenArithmetic` | exit 0; 1060 jobs; built in 1.8s |
| `lake build DkMath.FLT.Seven.GTailConstraintAudit` | exit 0; 8935 jobs; built in 5.5s |
| Initial `lake build DkMathTest.FLT.Seven.GTailConstraintAudit` | exit 0; 8936 jobs; built in 5.6s |
| Final test build after adding prime-exclusion and mod-49 compatibility regressions | exit 0; 8936 jobs; built in 6.1s |
| `lake build DkMath.FLT.Seven.GTailBridge DkMathTest.FLT.Seven.GTailBridge` | exit 0; 8932 jobs; replayed all four bridge axiom checks |

The initial neutral errors were repaired locally: explicit polynomial equality for symmetry instead of broad simp; correct Nat.dvd_add_right orientation; kernel decide for Prime 7. No hypothesis or theorem contract was weakened. Successful final builds have no warnings/errors. These are incremental focused checks, not a whole-workspace or clean build.

## Source and whitespace audit

```text
rg -n '\b(sorry|admit|axiom|unsafe)\b|False\.elim|exfalso|no_solution|fermatLastTheorem|^import DkMath\.FLT\.(Three|Five|Seven)$' DkMath/Lib/Cosmic/GTailSevenArithmetic.lean DkMath/FLT/Seven/GTailConstraintAudit.lean DkMathTest/FLT/Seven/GTailConstraintAudit.lean
```

No matches, exit 1 (expected for an empty search). `git diff --check` exits 0. A separate trailing-whitespace/final-newline audit includes all six new files and ROADMAP because git diff alone does not cover untracked contents: PASS (7 files, preserving intentional Markdown hard breaks in ROADMAP). The initial strict whitespace script flagged the inherited two-space Markdown line endings in ROADMAP; the corrected check permits those existing hard breaks. Import closures and source-only inspections are recorded in the inventory; no cycle to an existing heavy FLT7 owner was added.

## Public axiom audit

All nine endpoints are printed by the final test:

```text
DkMath.FLT.Seven.fermat7_focused_bounds: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.focused_gap_lt_coordinates: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.exists_positive_focused_gap: [propext, Classical.choice, Quot.sound]
DkMath.FLT.Seven.seven_dvd_focused_gap: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coprime_left_seven_quadratic: [propext, Quot.sound]
DkMath.CosmicFormula.coprime_right_seven_quadratic: [propext, Quot.sound]
DkMath.CosmicFormula.coprime_sum_seven_quadratic: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.coprime_product_seven_quadratic: [propext, Classical.choice, Quot.sound]
DkMath.CosmicFormula.gtail_seven_exact_seven_layer: [propext, Classical.choice, Quot.sound]
```

Only standard foundations. The axiom list alone does not establish noncircularity; the source derivations and nonvacuous neutral examples establish the stated proof routes.

## Lean結果からの気づき・推論と追加実装候補

以下は、証明済みAPI、今回試したexample、未形式化の推論を区別した研究メモです。未証明の証人・公理は追加していません。

### 確認できたこと

1. 二次因子Qは、原始的な入力ならa、b、a+bのすべてと互いに素です。したがってQの素因子は右辺の平方部分に局在します。ただし左辺g*Tのどちらへ配分されるかは、この結果だけでは決まりません。
2. 7の層の制御に必要なのは、ここでは端点cが7の単元であることです。gとcが完全に互いに素である必要はありません。(14,2)のexampleがこの差を実証しています。境界gcd APIと残余のmod-49 APIは、要求する仮定を区別して使うべきです。
3. 新しいfocus g=a+b-c と、既存FLT7で使うc-bは別の座標です。既存の coprime_gap_y_of_counterexamplePack の仮定・結論を、そのまま移すことはできません。小さいgを得ても次のFermat候補は構成されていません。

### 試した有限計算（Python探索とLean検査の区別）

ローカルPythonで `pow(n,7,49)` をn=1..48の7の単元について計算すると、像は `{1,18,19,30,31,48}` でした。これは既存SevenBaseTerminalRamifiedUnitClassAuditの六元分類と一致し、新定理ではありません。
さらにa,b,c=1..6で `(a^7+b^7-c^7)%49==0` を列挙すると12組ありました。全12組でQ%7=0でした。これは有限プログラムの探索結果であって、一般的なmod-49必要条件をLeanで証明した結果ではありません。Leanで今回確認したのは、その一例(1,2,3)の合同、Qの7整除性、正確なFermat方程式の不成立です。

再現用の探索式:

```python
triples = [(a,b,c) for a in range(1,7) for b in range(1,7) for c in range(1,7)
           if (pow(a,7,49)+pow(b,7,49)-pow(c,7,49)) % 49 == 0]
# 12 triples; all (a*a+a*b+b*b) % 7 == 0
```

### 未形式化の推論・小さい次の命題候補

記号v_qはpadicValNat qを表します。以下の型を満たす定理は今回追加していません。

- **7進付値の保存式:** `ha : 0<a`, `hb : 0<b`, `hEq : Fermat7Equation a b c`, `hsum : a+b=c+g`, `hend : ¬7∣c` の下で、
  `v_7(g)=v_7(a)+v_7(b)+v_7(a+b)+2*v_7(Q)`。
  今回の正確な一段整除結果からv_7(T)=1を導き、橋の両辺の乗法付値を比較して共通の1を消す方針です。各因子の非零性を明示する必要があります。一般のpadicValNat乗法APIを使う小さい校正ファイルが次の実装候補です。
- **7の単元入力の分岐:** 上の仮定に `¬7∣a*b*c` を加えると、a,b,a+bの付値が0になり、`v_7(g)=2*v_7(Q)` が予想されます。既に7∣gなので、ここから7∣Q、49∣gが期待されます。これは付値式からの推論で、今回の公開定理ではありません。標準的な局所必要条件との重複を監査してから実装・分類すべきです。
- **q平方の配分保存式:** `ha,hb,hEq,hsum`, `hcop : Nat.Coprime a b`, `hq : Nat.Prime q`, `hq7 : q≠7`, `hQ : q∣Q` の下で、
  `v_q(g)+v_q(T)=2*v_q(Q)`。
  中立coprimalityで右辺の他の因子がqの単元になることを利用できます。この保存式から直ちに「q²∣g」や「q²∣T」の一方を指定することはできません。追加の境界gcd・端点単元、または実際の付値配分証明が必要です。
- **位数による分岐候補:** 直前の条件に `q≠3` と `¬q∣g` を加えたとき、`21∣q-1` を候補とします。Qの零合同からa/bの位数3、尾の零合同から(c+g)/cの位数7を狙う推論です。有限体内の分母の非零性と各位数の非自明性を証明しなければ使えません。既存prime/cyclotomic位数結果との重複も未監査なので、新規障害とは呼びません。

これらは既存の合同・因数分解より強い局所情報を整理する候補ですが、次候補の座標や単元類の消去を与えるものではありません。

## Reconstruction and normalization frontier

The ledger records exact rejected/weakened contracts and deferred targets. AwayDescentClosureProvider requires a new primitive positive equation packet and a matching new carrier; smaller g supplies neither. A route would still need consistent prime-power allocation, fixed-carrier root/unit extraction, signed-to-natural reconstruction, equation conservation, positivity/primitivity and the actual strict measure comparison.

TraceOne norm signs were inspected: Q over integers is the norm of ⟨a,b⟩ in TraceOneInt(-1); standard Eisenstein coordinates (m,n) have norm m²-mn+n². No typed map to an FLT7 cyclotomic carrier or new norm theorem is asserted here. UnitGauge fixed-ramifier root-choice independence and weighted-unit rescaling criterion show why changing normalization is material. A scalar Q² identity cannot settle the residual seventh-power unit class.

Overall Outcome B, with local C counterexamples to weakened premises. No genuinely independent FLT7 arithmetic obstruction is claimed. Step 007 façade promotion, whole build and merge are outside this checkpoint.
