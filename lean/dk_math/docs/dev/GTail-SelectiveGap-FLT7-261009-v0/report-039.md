# Step039 report — signed defect square stability and non-Fermat controls

2026-10-11。Outcome B。
Base HEAD: `3644e9a7b272b587d90035f2fc585d5ab4202fe9`。
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`。
[source inventory](source-inventory-039.md) / [frontier](frontier-039.md)。

## 検証した成果

新 production/test owner を作成し、公開7宣言（definition1 / theorems6）を検証した。
核心の endpoint と square route に hEq を使わない。明示 hc fallback は不要だった。

| Gate | Checked endpoint | Precise scope |
|---|---|---|
| 1 | focusedFermatDefect:ℤ、focused identity、Int/Nat square-product iff | focus と q∣Q のみ。primality / positivity / primitive / hEq 不要 |
| 2 | endpoint_unit_of_defect | q prime,hcop,hQ,q∣Δ → q∤c。focus / hEq 不要 |
| 3 | defect_square_prime_route | q prime≠7,hcop,hQ,focus,q²∣Δ → square Gap/Tail split。hEq / positivity / entry hT なし |
| 4 | two proposed countermodels + budget-separation control | positive primitive strict focused geometry、signed integer support、¬hEq / ¬global balance |
| 5 | focusedFermatDefect_zero_iff | Δ=0 iff original Fermat7Equation。focus すら不要な cast corollary |

Gate1 は existing gtail_seven_defect を使用し、degree-seven shell を再証明していない。
Int 側の quadratic term は q² の倍数なので dvd_sub / dvd_add で両向きを得る。
Gate2 は neutral quadratic coprimality と existing seventh-power sum shell を使う。
q∣c と q∣Δ を仮定すると q∣a⁷+b⁷、従って q∣(a+b)⁷ となり primitive quadratic unit に矛盾する。
Gate3 は q∣g で split し、neutral head exclusion と verified Coprime.pow_left 2 /
dvd_of_dvd_mul_left により q² を一方に割り当てる。新 p-adic equality は主張しない。

## 正負を保った Lean numeric certificates

候補の Q/T/positive Tail defect values はすべて Lean の decide で一致した。訂正する候補値はなかった。
Gap defect は今回 exact signed integer 値まで検証した。

| Quantity | Tail q43: (1166,1857,1858,1165) | Gap q13: (196,211,238,169) |
|---|---|---|
| a+b=c+g | 3023 | 407 |
| gcd(a,b) | 1 | 1 |
| geometry | 0<g<a,b<c<a+b | 0<g<a,b<c<a+b |
| Q | 6,973,267 | 124,293 |
| T | 1,914,732,507,483,487,090,603 | 10,690,523,583,988,879 |
| Δ:ℤ | +2,642,627,963,860,178,152,897 | −13,523,337,259,569,605 |
| vq(Q) | 1 | 1 |
| vq(g) | 0 | 2 |
| vq(T) | 2 | 0 |
| vq(∣Δ∣) | 2 | 2 |
| Δ support | q²∣Δ、q³∤Δ、Δ≠0 | q²∣Δ、q³∤Δ、Δ≠0 |
| route | q²∣T、q∤g | q²∣g、q∤T、canonical ratio1 |
| selected-prime budget | vq(g)+vq(T)=2vq(Q) | vq(g)+vq(T)=2vq(Q) |
| exact equation / global balance | both false | both false |

Int divisibility を直接 decide した。negative Δ の valuation は `padicValNat q Δ.natAbs` として
実際の absolute integer value で検証した。Δ を ℕ subtraction に変換していない。
二つの valuation は prime powers の下界/上界と既存 padicValNat_le_iff_dvd で確認した。
Fermat equation / scalar balance の否定は zero-defect iff と旧 Step032 iff を使った。

Optional Tail control は Step037 の actual nativeKernel の maximality と実際の J²/J³/J⁴ memberships を
hEq なしで再検証した。Gap model は canonical ratio1 / nonidentity guard failure のみで、Tail receiver に接続しない。

旧 q13 small (14,29,30,13) と q43 small (5,8,9,4) はともに new q²-defect premise が false。
q43 small の additive focus / first Tail support と historical Step032 correction を保持した。

追加の budget-separation control: q13、(2198,2213,2214,2197)。
positive primitive strict focused geometry、q∣Q、q²∣Δ、Δ≠0 を kernel checked。
v13(Q)=1 だが v13(g)≥3 なので v13(g)+v13(T)≠2v13(Q) を証明した。
これは q²-defect support から valuation equality を一般化できないことの具体的な反例。
新 q³/q⁴ defect hierarchy / general valuation API は追加していない。

新 test は example46件。symbolic tests は identity / both square iff / no-focus endpoint /
hEq-free route / zero-defect iff / Step032 balance composition の exact signatures を確認する。

## Noncircularity / proof-owner audit

核心5 theorem の source/proof-body audit は Fermat7Equation / CounterexamplePack consumer0、
旧 hEq endpoint / prime_square_focused_allocation / focused_prime_route consumer0。
Step031 hEq guards/readouts、Step037 focused_receiver、Step038 tail_receiver も核心で使用0。
separate zero-defect iff の signature/proof だけが actual Fermat7Equation を参照する。

読み合わせた equation-free external owner routes:
GTailBridge.gtail_seven_defect → gtail_seven_shell → neutral add_pow_seven_eq_gap_add_interior、
neutral coprime_product_seven_quadratic、neutral not_prime_dvd_gtail_seven_of_gap、
Step038 gap_ratio_eq_one。これらの選択した実際の lemma bodies に equation / packet premise はない。
証拠は proof-dependency-audit.json。unconditional FLT7 result を呼んで branch を閉じていない。

## 公開宣言の実際の elaborated signatures

最終 test07 の #check 出力から取得した。

### focusedFermatDefect

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect (a b c : ℕ) : ℤ
```

### focusedFermatDefect_eq

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_eq {a b c g : ℕ} (hfocus : a + b = c + g) :
  focusedFermatDefect a b c = ↑g * ↑(GTail 7 1 g c) - 7 * ↑a * ↑b * ↑(a + b) * ↑(a ^ 2 + a * b + b ^ 2) ^ 2
```

### defect_square_iff_product_int

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_int {q a b c g : ℕ} (hfocus : a + b = c + g)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) : ↑q ^ 2 ∣ focusedFermatDefect a b c ↔ ↑q ^ 2 ∣ ↑g * ↑(GTail 7 1 g c)
```

### defect_square_iff_product_nat

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_iff_product_nat {q a b c g : ℕ} (hfocus : a + b = c + g)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) : ↑q ^ 2 ∣ focusedFermatDefect a b c ↔ q ^ 2 ∣ g * GTail 7 1 g c
```

### endpoint_unit_of_defect

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.endpoint_unit_of_defect {q a b c : ℕ} (hq : Nat.Prime q)
  (hcop : a.Coprime b) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hD : ↑q ∣ focusedFermatDefect a b c) : ¬q ∣ c
```

### defect_square_prime_route

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.defect_square_prime_route {q a b c g : ℕ} [Fact (Nat.Prime q)]
  (hq7 : q ≠ 7) (hcop : a.Coprime b) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hfocus : a + b = c + g)
  (hD2 : ↑q ^ 2 ∣ focusedFermatDefect a b c) :
  q ^ 2 ∣ g ∧ ¬q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1 ∨ q ^ 2 ∣ GTail 7 1 g c ∧ ¬q ∣ g
```

### focusedFermatDefect_zero_iff

```lean
DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall.focusedFermatDefect_zero_iff {a b c : ℕ} :
  focusedFermatDefect a b c = 0 ↔ Fermat7Equation a b c
```

## 実際の公理監査

| Public declaration | #print axioms |
|---|---|
| focusedFermatDefect | propext |
| focusedFermatDefect_eq | propext, Classical.choice, Quot.sound |
| defect_square_iff_product_int | propext, Classical.choice, Quot.sound |
| defect_square_iff_product_nat | propext, Classical.choice, Quot.sound |
| endpoint_unit_of_defect | propext, Classical.choice, Quot.sound |
| defect_square_prime_route | propext, Classical.choice, Quot.sound |
| focusedFermatDefect_zero_iff | propext |

全7宣言は standard-only。非標準公理0。definition と zero-iff は propext のみ、残る5 theorem は propext / Classical.choice / Quot.sound。

## 実行した compiler commands / failures / repairs

cwd: `lean/dk_math`。Lake builds は sequential、process-local `LEAN_NUM_THREADS=2`。
各 NN log は `.lake/build/gtail-step039/NN-build.log`。

| Log | Actual command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall` | 1 | 0 | 16.3 |
| 02 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall` | 1 | 0 | 15.54 |
| 03 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 16.15 |
| 04 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 15.85 |
| 05 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 15.93 |
| 06 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall` | 1 | 0 | 17.59 |
| 07 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 21.21 |
| 08 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 8.57 |
| 09 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 8.51 |

- 01: Gate1 の focused signed identity で ring normalization mismatch。
  unrestricted push_cast が simp-tagged GTail を finite sum に展開し、既存 hs の opaque GTail と揃わなかった。
  加えて linear_combination の係数を −hs とする必要があった。
- 02: targeted cast simp / −hs に変更後も dsimp が goal の GTail を展開し mismatch が残った。
  defect definition のみを unfold する局所 repair に変更。
- 03: literal signed defect identity と Int/Nat square transport を単独で成功。
- 04: no-focus / no-hEq endpoint gate を追加し成功。
- 05: hEq-free square route / zero-defect iff を含む最終 production が実際に Built、exit0 / warning0。
- 06: 数値 test の a,b が結論から復元されず decide の expected type に metavariables が残った。
  numeric endpoint/route calls に explicit a,b を指定。
  local notation Δ.natAbs は qualified identifier と解釈されたため (Δ).natAbs に変更。
  sections 内の同名 private vQ/vD は namespace を分けて修正した。
  いずれも numeric premise / theorem semantics は変更していない。
- 07: 修正後の最終 test が実際に Built。追加 budget-separation control を含む46 examples と
  全7 #check / #print axioms が成功、warning0。
- 08/09: Step038/037 の指定 direct regression targets が成功、warning0。
  既存 target の cached replay を含む。新 source05/test07 の Built と区別する。

別途 `LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step039/api-probe.lean > .lake/build/gtail-step039/api-probe.log 2>&1`
は exit0 / warning0。Int.natCast_dvd_natCast、Coprime APIs、dvd_add/dvd_sub、selected shell/defect signatures を確認した。
候補 API 名の失敗はなかった。全 clean all-suite build の結果としては扱わない。

## Lean 結果からの気づき・試した命題・実装提案

1. 試した square iff は prime q や primitive input を必要としなかった。
   q∣Q と focus だけで quadratic contribution が q² の倍数となり、Δ と g*T の支持が両向きに移る。
   divisibility を保つ整数差を使うことが重要で、Δ を natural subtraction にすると Gap の負の defect が失われる。
2. endpoint guard は focus なし、さらに q² ではなく q∣Δ だけで証明できた。
   Step010 の hEq endpoint を呼び出さず、neutral primitive coprimality と existing shell の合成で済んだ。
   これは実際の仮定の弱化であり、global contradiction ではない。
3. main route に positivity / zero handling の追加仮定は不要だった。
   square-product cancellation に existing Coprime.pow_left 2 を使い、q²-only proof を構成できた。
   Gap/Tail head exclusion の q≠7 は残る。q≠3 を total route に加えていない。
4. 正の Tail Δ と負の Gap Δ のどちらも selected prime depth2、しかも strict positive primitive focus を満たした。
   したがって Step038 square routing の conclusion だけでは Δ=0 と finite congruence を区別できない。
5. 指定された二例では selected-prime budget equality まで成立する一方で global scalar equality が false。
   この一素数の equality を持つこと自体が exact Fermat equation を復元しない。
6. さらに試した q13 (2198,2213,2214,2197) は q²∣Δ だが budget equality が false。
   下界から equality を導けないことも kernel-checked control として保存した。
   q³ を一般化する production API は追加していない。
7. literal zero-defect iff は focus を要しない stronger signature で通った。
   focus は Δ と global product balance の比較にだけ必要で、元の equation と Δ=0 の比較には不要。
8. 今後の実装候補は、original primitive data に対し finite congruence と zero defect を区別する
   explicit global invariant、または旧 signed/provider field ごとの actual reconstruction theorem。
   追加仮定が Δ=0/hEq を言い換えただけでないか、既存 unconditional closure を隠していないかを
   証明署名と owner dependencies で先に確認する必要がある。
   今回その invariant / reconstruction theorem は実装していない。

## Reconstruction contract / stop

Gap ratio1 は q13²∣g の実際の non-Fermat data と両立する。
Tail source-linked kernel と混合 J³/J⁴ は q43²∣T の実際の non-Fermat data と両立する。
共通 residue0 は二つの source images の equality を与えない。
exact global balance は Step032 により under focus hEq と同値であり、q² defect / local power support から得ていない。

read-only actual AwayDescentClosureProvider は nextX/Y/Z、new CounterexamplePack、
new AwayValuationTransferPacket と
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd` を要求する。
signed packet は balanced axis、signed root identities / coprimality、gap/quotient roots、
7-unit guards、normalizedEquation を要求する。新 Ideal C や signed defect divisibility はこれらの値を構成しない。
旧 packet/provider の非存在を証明したという意味でもない。

Outcome B として Step039 を停止する。新しい q³/q⁴ defect hierarchy、Gap receiver、spectrum、
exact common ideal valuation、signed packet、primitive counterexample、unconditional FLT7 descent は構成していない。

## 最終依存・書式・履歴監査

- 公開7宣言 / example46件、standard-only axioms、最終 source05 / test07 / regression08 / 09 exit0 / warning0。
- 新 source/test の comments / strings を除く scan は
  `sorry / admit / axiom / unsafe / native_decide / set_option / False.elim` 全件0。
  MIT2026 D. and Wise Wolf header、import 後の file print と書式を検査した。
- production closure8954 modules（local174）、test closure8955（local175）、
  local union175 vertices の DAG cycle0。
  neutral GTailSevenRealTraceResidue closure1907（local20）の FLT reachability0、
  到達する27 neutral Lib owners の各独立 closure でも FLT reachability0。
- Seven facade、SevenRamifiedFusionGlobalOrientedPrimeFactorization、Kummer.CyclotomicPrincipalization、
  CyclotomicQRTraceOneBridge、SevenRamifiedFusionCyclotomicDegreeSixDomain、
  SevenRamifiedFusionOrientedCarrierValuationOwnership は今回の closure に含まれない。
  signed modules は既存の推移的 imports として残る。新 direct import は Step038 一つのみ。
- 保存済み Step038 module set と live Step039 closure の差分は新 owner 一つ、削除0。
  これは historical module set comparison であり、旧 build を今回実行したと扱わない。
- 核心 proof-owner scan で equation/packet と旧 hEq-dependent endpoints の参照0を確認。
  separate zero-iff が original equation を参照する boundary と区別した。
- 既存 tracked sources / historical reports/reviews は byte-stable。
  ROADMAP は HEAD の既存 bytes を保持した追記のみ。
  新5ファイルと追記範囲の newline / tab / trailing whitespace、git diff --check が成功。

証拠: `.lake/build/gtail-step039/` の runs.json、build/probe logs、signatures.json、
proof-dependency-audit.json、imports.json、audit.json、import-impact.json、workspace-audit.json。
