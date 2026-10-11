# Step038 report — total focused prime route / Tail-only native receiver

2026-10-11。Outcome B: formal interface completeness。
Base HEAD: `9422f149699ea15fb603551e900f62c6cef140a3`。
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`。
[source inventory](source-inventory-038.md) / [frontier](frontier-038.md)。

## 実装結果と仮定の境界

公開 theorem7件、新 production owner と test owner を作成した。
新 direct import は Step037 owner 一つで、Step010/031/032/037 と E/R/C を変更しない。

| Gate | Performed proof | Exact limit |
|---|---|---|
| 1 | gap_ratio_eq_one / gap_nonidentity_guard_unavailable | q prime、q∤c、q∣g のみ。canonical ratio=1 が非自明 guard を破る |
| 2 | focused_coordinate_units / focused_prime_route | hEq と positive primitive focus、q≠7、q∣Q の下で全二分岐。entry hT なし |
| 3 | tail_receiver | Tail branch q²∣T から hT を導き、実際の nativeKernel / typed contractions / joint sum / all Step037 bounded readouts を返す |
| 4 | norm_image_ne_cyclotomic / tail_source_images_ne | supplied R evaluation と q∤b による coordinate separation。hEq の矛盾ではない |

Gap case は q²∣g、q∤T、canonical ratio=1 の live alternative。
Tail case は q²∣T、q∤g、q∣T。coordinate units は分岐前に Step010 から導く。
Tail adapter は q-unit assumptions を追加せず Step031 guards を再利用する。
q3 は total route の例外として勝手に除かず、Tail 側の guards が q≠3 を供給する。
q7 は total square route の明示例外だが raw Gap ratio lemma は q7 にも適用できる。

Tail output の J は存在だけを隠した Nonempty ではなく、元の nativeKernel の let 値。
P は Ideal E、K は Ideal R、その map の sup と J が Ideal C で等しい。
α/F0 の first memberships、α²/F0 の J²、混合積 J³/J⁴、
vq(T)=2vq(Q)、Even、q²∣T、q⁴∣T↔q²∣Q、q³∣T↔q⁴∣T を保持する。
source square transport は Step037 をそのまま呼び、新しい all-k / exact-depth proof はない。

Optional combined sum/packet や inductive route は追加しなかった。
公開 disjunction と Tail adapter が分岐証拠を明示的に受け渡す。
Optional generic image inequality は実装した。R の domain / cast injectivity は仮定せず、
actual R evaluation で imaginary coefficient b の非零を検出した。

## Numeric / symbolic regressions

新 test の example60件が成功した。

| Control | Checked | Interpretation |
|---|---|---|
| symbolic prime / hEq | raw Gap ratio、guard failure、coordinate units、entry hT なし total route、全 Tail adapter signature、image inequality、Step032 balance iff | 仮想 hEq を保ち、正の Fermat tuple を作らない |
| q43 large (1166,1857,1858,1165) | actual nativeKernel=M43、α/F0 membership、bounded J²/J³/J⁴、focus/coprime、¬hEq、¬exact balance、image inequality | new hEq-conditioned route の数値インスタンスではない |
| q43 small (5,8,9,4) | additive focus、same M43、first Tail support、¬q²∣T、¬doubled budget、source K² nonmembership、¬hEq、¬exact balance | corrected Step032 history を保持。C の J² nonmembership への逆移送はしない |
| q13 (14,29,30,13) | focus / Q support / Gap support / Tail absence、q∤c、canonical ratio=1、guard failure、¬hEq、¬q²∣g | raw control のみ。full hypothetical route の square conclusion を数値例に適用しない |
| q127 t20/r2 | polynomial / seventh-root guards、actual supplied evPair maximal/prime kernel、typed contractions / generator images | natural Q/T input や hEq を供給しない |
| artificial q43 c1/g43 | canonical ratio=1 だが supplied r11 はそれと異なる、pairedKernel37/11 は maximal | Gap prime で他の supplied root が存在することと native Tail ratio を区別 |
| q7 / q3 / q13 | nonidentity seventh root absence、q7/q3 raw Gap ratio=1、q3 repeated quadratic root | exception/guard の区別を維持 |
| old boundaries | Step035 strict source extensions、Step036 joint sum、Step033 no direct E↔R RingHom | common membership は source equality ではない |

## 公開 theorem の実際の elaborated signatures

以下は最終 test06 の実際の #check 出力。暗黙引数と let 証拠も記録する。

### gap_ratio_eq_one

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_ratio_eq_one {q c g : ℕ} [Fact (Nat.Prime q)] (hc : ¬q ∣ c) (hg : q ∣ g) :
  gtailSevenTailRatio q c g = 1
```

### gap_nonidentity_guard_unavailable

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.gap_nonidentity_guard_unavailable {q c g : ℕ} [Fact (Nat.Prime q)] (hc : ¬q ∣ c)
  (hg : q ∣ g) : ¬gtailSevenTailRatio q c g ≠ 1
```

### focused_coordinate_units

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_coordinate_units {q a b c : ℕ} [Fact (Nat.Prime q)] (hcop : a.Coprime b)
  (hEq : Fermat7Equation a b c) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) : ¬q ∣ a ∧ ¬q ∣ b ∧ ¬q ∣ a + b ∧ ¬q ∣ c
```

### focused_prime_route

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.focused_prime_route {q a b c g : ℕ} [Fact (Nat.Prime q)] (ha : 0 < a)
  (hb : 0 < b) (hcop : a.Coprime b) (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g) (hq7 : q ≠ 7)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
  q ^ 2 ∣ g ∧ ¬q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1 ∨ q ^ 2 ∣ GTail 7 1 g c ∧ ¬q ∣ g ∧ q ∣ GTail 7 1 g c
```

### tail_receiver

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_receiver {q a b c g : ℕ} [Fact (Nat.Prime q)] (ha : 0 < a) (hbpos : 0 < b)
  (hcop : a.Coprime b) (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g) (hq7 : q ≠ 7)
  (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
  have hT := ⋯;
  have hu := ⋯;
  have J := nativeKernel a b c g hQ ⋯ ⋯ ⋯ hT;
  J =
      Ideal.map fromEisenstein (eisensteinResidueIdeal (gtailSevenResidueRoot q a b) ⋯) ⊔
        Ideal.map fromCyclotomic (seventhRootKernel (gtailSevenTailRatio q c g) ⋯ ⋯ ⋯) ∧
    J.IsMaximal ∧
      Ideal.comap fromEisenstein J = eisensteinResidueIdeal (gtailSevenResidueRoot q a b) ⋯ ∧
        Ideal.comap fromCyclotomic J = seventhRootKernel (gtailSevenTailRatio q c g) ⋯ ⋯ ⋯ ∧
          fromEisenstein (gtailSevenNormCoord a b) ∈ J ∧
            fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ∧
              padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
                Even (padicValNat q (GTail 7 1 g c)) ∧
                  q ^ 2 ∣ GTail 7 1 g c ∧
                    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
                      (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) ∧
                        fromEisenstein (gtailSevenNormCoord a b ^ 2) ∈ J ^ 2 ∧
                          fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
                            fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈
                                J ^ 3 ∧
                              fromEisenstein (gtailSevenNormCoord a b ^ 2) *
                                  fromCyclotomic (gtailCyclotomicFactor c g 0) ∈
                                J ^ 4
```

### norm_image_ne_cyclotomic

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.norm_image_ne_cyclotomic {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q) (hr0 : r ≠ 0)
  (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (a b : ℕ) (hb : ¬q ∣ b) (u : SevenCyclotomicDegreeSixInt.Ring) :
  fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic u
```

### tail_source_images_ne

```lean
DkMath.FLT.Seven.GTailFocusedPrimeRoute.tail_source_images_ne {q a b c g : ℕ} [Fact (Nat.Prime q)] (hcop : a.Coprime b)
  (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
  (hT : q ∣ GTail 7 1 g c) : fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic (gtailCyclotomicFactor c g 0)
```

## 公理監査

最終 test06 の全7公開 theorem の #print axioms は、各々
`[propext, Classical.choice, Quot.sound]` のみ。非標準公理0。

| Theorem | Actual axioms |
|---|---|
| gap_ratio_eq_one | propext, Classical.choice, Quot.sound |
| gap_nonidentity_guard_unavailable | propext, Classical.choice, Quot.sound |
| focused_coordinate_units | propext, Classical.choice, Quot.sound |
| focused_prime_route | propext, Classical.choice, Quot.sound |
| tail_receiver | propext, Classical.choice, Quot.sound |
| norm_image_ne_cyclotomic | propext, Classical.choice, Quot.sound |
| tail_source_images_ne | propext, Classical.choice, Quot.sound |

## 実行した Lean 検証と修正

cwd は `lean/dk_math`。すべて process-local `LEAN_NUM_THREADS=2`、Lake build は順次実行。
各行のログは `.lake/build/gtail-step038/NN-build.log`。

| Log | Actual command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 14.25 |
| 02 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 14.23 |
| 03 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 14.82 |
| 04 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedPrimeRoute` | 1 | 0 | 15.16 |
| 05 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 15.78 |
| 06 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 23.93 |
| 07 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedGenericPrimeReceiver` | 0 | 0 | 8.44 |
| 08 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin` | 0 | 0 | 8.56 |

- 01: Gate1 の source-actual Gap ratio と guard failure を単独でコンパイル。
- 02: Gate2 の coordinate units と hT を仮定しない total square route が成功。
- 03: Gate3 の Tail-only adapter と joint sum / 全 Step037 readouts が成功。
- 04: optional image inequality の `simpa only` で cast normalization が途中で止まり、
  `evalCyclotomicFromSeventhRoot ... ↑b=0` と `↑b=0` の mismatch が発生した。
  integer cast が natural cast に正規化されるため `map_natCast` を追加して修正。
- 05: 修正後の最終 production source を実際に Built、exit0 / warning0。
- 06: 最終新 test を実際に Built、example60件と公開7件の #check / #print axioms が成功。
- 07/08: Step037/036 の選択した direct regression targets が成功。既存 target の cached replay を含む。
  全 clean build / all-suite の結果として扱わない。

別途 `LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step038/api-probe.lean` は exit1。
`ZMod.isUnit_iff` が存在しないことを確認した。
修正後の `LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step038/api-probe.lean > .lake/build/gtail-step038/api-probe-fixed.log 2>&1` は exit0 / warning0、
実在する三つの unit API と cast / div / divisibility APIs を確認した。
初回 probe の shell redirect は repo root で実行し、相対ログ directory 不在で shell exit1。
その invocation は Lean を起動していない。Lake cwd に直して上記 probe を実行した。

## Lean 結果からの気づき・試した命題・実装提案

1. 試した basic Gap ratio identity は Fermat 情報を全く必要としなかった。
   q∤c は実際の cancellation の必須仮定であり、q∣g は分子の g residue を0にする。
   q7 / q3 の controls も通り、ratio lemma の scope と total route の例外を分離できた。
2. hT を入口から除いても、既存 Step010 の square split で total route が通った。
   今回の進展は新 valuation proof ではなく、Gap を明示した interface completeness。
   Gap の live alternative を消していない。
3. abstract supplied-root receiver と canonical root は別の情報である。
   q43,c1,g43 の ratio は1だが supplied r11 を使う evPair は実在する。
   これは「Gap prime に seventh root が一切ない」という誤った一般化を防ぐ。
4. norm-image inequality を任意の u:R に拡張できた。
   imaginary coefficient を取り、R evaluation で非零を検出するだけで足りた。
   domain / cast injectivity を新たに仮定せず、hEq / Q / Tail support にも依存しない。
   Fermat 方程式は C 内で α=F0 を要求しないので、これを obstruction と数えない。
5. q13 raw Gap sample は q∣g だが q²∤g、しかも ¬hEq。
   この例に hypothetical hEq の square-route conclusion を適用できないことも数値検証した。
   q43 small sample の additive focus と failed doubled budget も保持した。
6. 今後、consumer が複数現れた場合には公開 disjunction と Tail readout を
   source-indexed route record にまとめる実装は考えられる。
   今回はその record を追加せず、型付き let J を返す二つの theorem で契約を公開した。
   record 化は証拠の梱包であり新しい数学的制約ではない。
7. 次の研究候補には、両 live branches のいずれかを制約する global relation、または
   original primitive data から nextPack/nextRoute/carrier_match を実際に構成する theorem が必要。
   結論が Step010/031 の直接帰結でも assumed hEq と同値の balance でもないかを先に点検する。
   今回そのような新命題や provider は構成していない。

## Reconstruction contract / stop

| Stage | Proven | Still missing |
|---|---|---|
| q∣Q under positive primitive hEq | q² Gap OR q² Tail、units、exact guard | contradiction / independent restriction |
| Gap | q²∣g、q∤T、canonical ratio=1 | appropriate source-linked Gap recipient / descent |
| Tail | native C maximal kernel、typed E/R contractions、joint sum、memberships、even vq(T)、bounded mixed support | new global arithmetic、exact M valuation、signed carrier transfer |
| global balance | focus の下で hEq と同値（旧 Step032） | weaker-data derivation without hEq |
| signed packet | newly constructed fields0 | balanced axis、signed identities、7-units、normalizedEquation |
| away provider | newly constructed fields0 | nextX/Y/Z、CounterexamplePack、AwayValuationTransferPacket、carrier_match |

read-only source で確認した AwayDescentClosureProvider の exact field は
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd`。
Ideal C の join / mixed-power membership はこの natural carrier equality を供給しない。
RamifiedSignedRootDepthPacket は balanced、signed roots と normPacket roots の一致、
IsCoprime、gapRoot/quotientRoot、signedGap=7⁴*gapRoot、signedQuotient=7*quotientRoot、
両 root の7-unit と normalizedEquation を要求する。今回どれも新構成していない。
新 source で旧 packet/provider を direct import / proof-body reference していない。
既存 transitive closure から消えたという主張でも、その非存在証明でもない。

Step038 を Outcome B として停止する。独立 FLT7 obstruction や primitive descent は得ていない。

## 最終依存・書式・履歴監査

- 公開 theorem7件、example60件、全公理 standard-only を実際の最終 test06 で確認。
- 新 source/test のコメント・文字列を除く scan は
  `sorry / admit / axiom / unsafe / native_decide / set_option / False.elim` 全件0。
  MIT2026 D. and Wise Wolf header と import 後の file print を検査した。
- production closure8953 modules（local173）、test closure8954（local174）。
  local union174 vertices の DAG は cycle0。
  neutral GTailSevenRealTraceResidue closure1907（local20）の FLT reachability0。
  到達する27 neutral Lib owners の各独立 closure でも FLT reachability0。
- Seven facade / SevenRamifiedFusionGlobalOrientedPrimeFactorization /
  Kummer.CyclotomicPrincipalization / CyclotomicQRTraceOneBridge /
  SevenRamifiedFusionCyclotomicDegreeSixDomain /
  SevenRamifiedFusionOrientedCarrierValuationOwnership は今回の closure に含まれない。
  旧 signed modules は従来の推移的依存として残る。新 direct import は Step037 一つのみ。
- 保存済み Step037 module set と今回の live closure を比較し、追加は新 owner 一つ、削除0。
  これは module set の比較であり、過去の build を今回の fresh build として扱わない。
- 全最終 selected build / regression は exit0 / warning0。新 source05 / test06 は Built、
  既存 regression07 / 08 は cached replay を含む。
- 既存 tracked source / historical docs の差分0。ROADMAP は HEAD の既存 bytes を保持した追記のみ。
  新5ファイルと追記範囲の newline / tab / trailing whitespace 検査および git diff --check が成功。

証拠: `.lake/build/gtail-step038/` の runs.json、個別 build logs、api-probe logs、
signatures.json、imports.json、audit.json、import-impact.json、workspace-audit.json。
