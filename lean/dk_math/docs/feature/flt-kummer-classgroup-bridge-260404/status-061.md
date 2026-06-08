# status 061: `d = 3` 整理の完了と honest migration の本線化

## 1. まず検証結果

賢狼の側で、新しい snapshot `__snapshot-dk_math-lean-code-260415-0100.tar.gz` を展開して見た。
SHA-256 は、お主が示した

$$
\texttt{a610b5f89c6b49c13c1521e27039f12fca85b81975936d1cc054c33f9a03f4a6}
$$

と一致しておる。
つまり、見ておる中身は確かに最新更新済みのものじゃ。

ただし、ここで一点だけ正直に言うと、この環境には `lake` が入っておらず、わっち自身は `./lean-build.sh` の再実行まではできなかった。よって今回は、

* hash 一致
* snapshot 展開
* 対象 Lean ファイルの静的確認
* `sorry` の現況確認
* diff で触れた theorem / alias / deprecation / target の実在確認

で検証しておる。
build 成功そのものについては、snapshot 内の更新内容とお主の差分レポートを整合確認した、という形じゃ。

賢狼が展開後に数えた現状は、

* Lean ファイル数: 253
* `theorem|lemma|def` 行数ベースの宣言数: 4492
* `sorry` トークン総数: 20

じゃ。
この 20 個のうち、今回の FLT / Kummer / valuation 再編に直接効く本丸は、実質かなり絞れておる。

## 2. いまの本当の戦況

結論から言えば、 **`d = 3` の valuation 再編は、ほぼ整理完了** じゃ。
そして **主戦場は `ZsigmondyCyclotomicResearch` の honest migration に戻った** 。

この認識でよい。

### 2.1. `GcdNextResearch` 側

ここは、かなり綺麗になっておる。

`d = 3` の話はもう、

* primitive 枝
* boundary (q \neq 3) 枝
* boundary (q = 3) 枝

へ canonical に分岐する設計に移り、`padicValNat_d3_canonical_case_split` と `padicValNat_d3_layer_b_case_split` が正規入口として立っておる。さらに primitive 枝用に `padicValNat_d3_primitive_upper_bound` も前に出た。旧 `padicValNat_d3_upper_bound` は deprecated になり、境界注入つき helper も `..._research` 名へ落とされた。これは設計としてたいへん良い。もう「偽な一様上界が mainline に居座る」状態ではない。

そして今の `GcdNextResearch` の **実 `sorry` は 1 個だけ** で、それは `padicValNat_upper_bound_layer_b_stub` の **`d > 3` 用研究スタブ** じゃ。
つまりこのファイルに関しては、`d = 3` の泥沼は抜けた。残務は

$$
d > 3
$$

へ押し出せた、ということじゃ。

### 2.2. `ZsigmondyCyclotomicResearch` 側

ここも整理は進んでおる。
`..._honest` と `..._research` の二系統が明示され、旧 public 名は deprecated alias に落ちた。つまり theorem 名だけで、

* honest route
* 研究 placeholder 依存 route

が区別できるようになった。これは大きい。

ただし、 **根の `sorry` はまだここに 1 個残っておる** 。
それが `squarefree_implies_padic_val_le_one_research` じゃ。
いまの research debt の中心は、まさにここじゃな。
この状況は、差分レポートともぴたり一致しておる。

### 2.3. `PrimitiveBeam` と `CosmicPetalBridgeGNNoWieferichResearch`

ここが、次の実務戦線じゃ。

snapshot を見ると、`PrimitiveBeam` の中には **すでに honest theorem を使っている箇所** と **まだ `_research` を踏んでいる箇所** が両方ある。
これは重要な手がかりじゃ。つまり、ここは理論が未確定というより、

$$
\text{同じファイル内で migration が途中}
$$

という段じゃ。

また `CosmicPetalBridgeGNNoWieferichResearch` も、`TriominoPrimitivePrimeFactorPadicValNatLeOneTarget` までは clean target 化されておるが、primitive-core 自体はまだ `_research` を踏んでおる。つまりここも、 **theorem 境界の切り出しは済み、本体 caller migration がまだ残っている** 段階じゃ。

### 2.4. Kummer / CyclotomicPrincipalization 側

ここは first-case の clean wiring 修正がきちんと入っており、その点は良い。実際、snapshot 中の `RegularPrimeRouteNoSorry.lean` でも、first-case / caseSplit 周辺は `#print axioms` の no-sorry 監視対象として並んでおる。
ただし non-first-case 側には、依然として

$$
\exists z',; z'^p = (x/q)^p + y^p
$$

を返す一点に局所化された直接 `sorry` が 1 個残っておる。
つまり Kummer 戦線は、

* first-case 周辺はかなり整理済み
* non-first-case peel existence core に 1 個の核が残る

という状態じゃ。
ここは `ZsigmondyCyclotomicResearch` とは別系統の open kernel と見てよい。

## 3. いま残っている「本当に重要な」 open kernel

今回の系統に限って言えば、重要度順はこうじゃ。

### 3.1. 最重要

`ZsigmondyCyclotomicResearch.lean` の

$$
\texttt{squarefree\_implies\_padic\_val\_le\_one\_research}
$$

の `sorry`。
これは名前の上でも research root として隔離済みじゃが、実際に downstream の `_research` caller がまだ踏んでおる。
よって、 **いまの本丸はここ** じゃ。

### 3.2. 次点

`GcdNextResearch.lean` の

$$
d > 3
$$

用 layer-B stub。
これは `d = 3` の誤配線ではもうない。
ちゃんと `d ≠ 3` 前提つき研究 stub に隔離されておる。
つまり「存在は気になる」が、優先順位は research root より一段下じゃ。

### 3.3. 別戦線の核

`CyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree` の直接 `sorry`。
これは valuation migration と並行しうるが、性質が違う。
primitive valuation の honest 化と、Kummer non-first-case existence kernel の補強は、別タスクとして見るべきじゃ。

## 4. 周囲の状況

お主のプロジェクト全体として見ると、FLT 幹線が本丸であり、`ZsigmondyCyclotomic` 系の完成度が FLT を決める、という地図は変わっておらぬ。

一方で、周辺の設計文書では、LPS / PowerSwap / GapContours / CosmicFormula 周りは、今すぐ完全証明へ突っ込むより、 **定義と局所核を整理して別柱に独立させる** 方針がかなり明確に出ておる。つまり、そちらは中長期の構造整備としては筋がよいが、 **現在の FLT/Kummer ボトルネックそのものではない** 。

ゆえに、いまの snapshot で優先順位を付けるなら、

$$
\text{FLT valuation / Kummer repair}
\quad\gg\quad
\text{LPS 系の再配置}
$$

じゃな。

## 5. 次の戦略

わっちの提案は、三段構えじゃ。

### 5.1. 第一段. `_research` caller を残敵一覧として固定する

まずは、実コード上で `_research` を踏んでいる箇所を、作業単位として固定するのがよい。
わっちが snapshot で見た限り、diff 関連の本筋では主に次じゃ。

* `PrimitiveBeam.lean` の 2 箇所
* `GcdNextResearch.lean` 冒頭の private primitive valuation 補題
* `GcdNextResearch.lean` の private boundary receiver 注入
* `CosmicPetalBridgeGNNoWieferichResearch.lean` の primitive-core theorem

この一覧を今後の **migration queue** にする。
ここが “見えている敵” じゃ。

### 5.2. 第二段. `PrimitiveBeam` を最初の honest migration 対象にする

これはかなり有望じゃ。
同じファイルの中に honest 呼び出しと research 呼び出しが共存しておるので、局所的な書き換えパターンが見えやすい。
つまり、

* `Squarefree (GN ...)` を caller に追加した strengthen 版を前に出す
* 旧 theorem は compatibility / research 名へ落とす

という移行が、一番やりやすい。

ここで 1 本でも `_research` 呼び出しを `..._honest` に置き換えられれば、今後の移行テンプレが固まる。
まずはここを叩くのが良い。

### 5.3. 第三段. `GcdNextResearch` の private primitive bound を分離する

`GcdNextResearch` 冒頭の `primitive_prime_padic_bound_diff` は、いま still `_research` を踏んでおるが、これは boundary ではなく **一般 d の primitive valuation 補題** じゃ。
ただしここは `d = 3` の新 API をそのまま使うには、追加仮定 `h_Ag`, `h_phi`, `hq_not_sq` が足りぬ。
ゆえにここは、無理に差し替えるより先に

* 何が不足しているかを theorem 名で切る
* `d = 3` specialized honest 版
* `d > 3` research 版

へ分解する方が筋じゃろう。

つまりこの箇所は、 **差し替え先がまだ足りぬので target 分離を先にやるべき** じゃ。

## 6. ロードマップ

いまからの短中期ロードマップを、賢狼ならこう切る。

### 6.1. 直近

* `PrimitiveBeam` の research caller を 1 本でも honest へ移す
* `CosmicPetalBridgeGNNoWieferichResearch` について、target-based clean route と primitive-core research route の境界をさらに明示する
* `GcdNextResearch` 冒頭の primitive bound を、`d = 3` / `d > 3` の責務で分ける

### 6.2. 次段

* `ZsigmondyCyclotomicResearch` の root `squarefree_implies_padic_val_le_one_research` を、caller migration を通じて包囲する
* `_research` 名しか必要としない caller を、明示的な research target へまとめ直す
* 逆に `Squarefree (GN ...)` を供給できる caller は順次 `..._honest` に寄せる

### 6.3. その後

* `CyclotomicPrincipalization` non-first-case existence core の単独攻略
* `d > 3` layer-B stub の本格化
* それとは別柱として、LPS / PowerSwap / CosmicFormula / PowerSums の再配置を進める

## 7. 最終判断

いまの snapshot は、かなり良い。
少なくとも、

* `d = 3` valuation story の再配線
* legacy と honest / research の名札分け
* Kummer first-case clean wiring
* FLT/Kummer valuation 周辺の debt の局所化

は、うまく進んでおる。

よって、次の主戦場はもうはっきりしておる。

$$
\boxed{
\text{`ZsigmondyCyclotomicResearch` の `\_research` caller を、
1 本ずつ honest / research に仕分けて剥がす}
}
$$

これじゃ。

ひとことで言えば、
**いまは新しい理論を増やす段ではなく、見える debt を順に剥がして mainline を澄ませる段** じゃよ。

必要なら次に、わっちがそのまま使える形で

* `_research` caller 一覧
* それぞれの migration 可否
* 優先順位つき TODO

を Markdown で起こすぞい。

---

## 1. 現在の戦況

今回の snapshot 更新で、これまでの diff 群による再編はかなり実を結んでおる。

まず大きいのは、`d = 3` の valuation story が、もはや **偽な一様上界 API** を中心に回っておらぬことじゃ。
いまの正規入口は次の三本立てに整理されたと見てよい。

* primitive 枝
  `padicValNat_d3_primitive_upper_bound`
* canonical 分岐入口
  `padicValNat_d3_canonical_case_split`
* layer-B 文脈での分岐入口
  `padicValNat_d3_layer_b_case_split`

そして旧 `padicValNat_d3_upper_bound` は deprecated、boundary receiver つき helper も `..._research` 名へ落ちた。
ゆえに `d = 3` 戦線そのものは、ほぼ **整理完了** と見てよい。

他方で、主戦場は `ZsigmondyCyclotomicResearch` 側へ戻った。
ここでは

* `..._honest` 系
* `..._research` 系
* 旧 public 名の deprecated alias

が分離され、まだ未修復の caller だけが明示的に `_research` を踏む構造になっておる。
これは非常に大きい。いまや debt は「どこかに潜んでいる」ものではなく、「名前で見える」ものになったからじゃ。

---

## 2. 何が片付き、何が残っているか

### 2.1. 片付いた部分

#### A. `d = 3` の false route の主経路追放

boundary-divisor family については、
「`padicValNat q (a^3-b^3) ≤ 1` を全域で返す」方針が誤りと分かり、

* `q \ne 3` 枝では exact equality
* `q = 3` 枝では `+1` 公式

という **exact valuation classification** へ移った。

これにより、`d = 3` を general upper bound の主経路から切り離せた。

#### B. `GcdNextResearch` 側の debt の局所化

`padicValNat_d3_upper_bound_of_boundaryReceiver` は research 専用へ改名され、
旧名は compatibility alias に落ちた。さらに legacy な boundary receiver 注入も private lemma に隔離された。

この結果、`GcdNextResearch` に残る direct `sorry` は、実質

\[
d > 3
\]

の layer-B stub だけじゃ。

#### C. `ZsigmondyCyclotomicResearch` 側の命名整理

`squarefree_implies_padic_val_le_one_research` と
`padicValNat_primitive_prime_factor_le_one_research` が導入され、
旧 public 名は deprecated alias へ落ちた。

これで downstream caller は、

* honest 依存
* 研究 placeholder 依存

を theorem 名だけで見分けられるようになった。

---

### 2.2. まだ残っている部分

#### A. 研究 root そのもの

`ZsigmondyCyclotomicResearch` 側には、なお research root が残っておる。
つまり問題はもう「命名混乱」ではなく、**一部 caller がまだ honest route に移れていない** ことじゃ。

#### B. `d > 3` の layer-B stub

`GcdNextResearch` 側の direct `sorry` は、いまやこの戦線だけじゃ。
したがって、`d = 3` の整理が終わった現在、ここは純粋に

\[
d > 3
\]

の研究スタブとして読むべきじゃ。

#### C. Kummer non-first-case 側の別 open kernel

FLT/Kummer 文脈では、non-first-case existence core に依然として別系統の open kernel が残っておる。
これは valuation migration と直交する、別戦線じゃ。

---

## 3. 現在の構造的な見取り図

いまの戦況は、次のように整理すると分かりやすい。

### 3.1. valuation / Zsigmondy 系

* `d = 3` special story
  ほぼ整理完了
* primitive-prime family
  honest migration 進行中
* boundary-divisor family
  exact valuation API へ移行済み
* remaining research root
  `ZsigmondyCyclotomicResearch` に集約

### 3.2. Kummer / principalization 系

* first-case wiring
  clean 化がかなり進んだ
* non-first-case
  existence core に open kernel が残る

### 3.3. 周辺構造

LPS / PowerSwap / GapContours / CosmicFormula / PowerSums の整理方針はかなり明瞭で、
それぞれ

* `CosmicFormula`
* `PowerSwap`
* `NumberTheory.PowerSums`

へ分柱する設計がよいと読める。
ただし、これは **現在の FLT valuation ボトルネックより優先度は下** じゃ。

---

## 4. 次の戦略

ここから先は、もう「理論の霧を払う」段ではなく、**見えている debt を順に剥がす段** じゃ。
わっちの推奨は次の三段構えじゃ。

### 4.1. 第一手. remaining `_research` caller の残敵一覧を固定する

まずは actual code path 上で `_research` を踏んでいる箇所を、作業単位として固定するのがよい。
現時点では、おおむね次が中心じゃ。

* `PrimitiveBeam` 側の remaining `_research` 呼び出し
* `GcdNextResearch` 冒頭の private primitive valuation 補題
* `CosmicPetalBridgeGNNoWieferichResearch` の primitive-core theorem
* private な legacy boundary receiver 注入

ここを migration queue と見なす。

### 4.2. 第二手. `PrimitiveBeam` を最初の honest migration 対象にする

これは一番筋がよい。理由は、

* 同じファイル内に honest 版と research 版の両方が見えておる
* `Squarefree (GN ...)` 仮定を足した strengthened theorem の方向が既に見えている
* 1 本でも `_research` を剥がせれば、以後の移行パターンが固まる

からじゃ。

狙いは、

* honest 仮定つき theorem を前面に出す
* 旧 theorem を compatibility / research 名へ落とす
* downstream を 1 本ずつ移す

という順で進めることじゃな。

### 4.3. 第三手. `GcdNextResearch` 冒頭の primitive bound を target 分離する

ここはまだ単純には honest へ差し替えにくい。
`d = 3` specialized API は揃ったが、一般形の primitive valuation 補題としては、caller 側に必要仮定が足りぬ可能性がある。

したがってここは、無理に一発で `..._honest` に寄せるより、

* `d = 3` specialized honest path
* `d > 3` research path

へ theorem 名ごと責務分離する方がよい。
つまり、**差し替えより先に target を切る** のが筋じゃ。

---

## 5. 実務ロードマップ

### 5.1. 直近

1. `PrimitiveBeam` の `_research` caller を 1 本選んで honest へ移す
2. `GcdNextResearch` 冒頭の primitive valuation 補題の責務を分離する
3. `CosmicPetalBridgeGNNoWieferichResearch` の primitive-core について、
   clean target と research 依存の境界をさらに明文化する

### 5.2. 次段

1. `ZsigmondyCyclotomicResearch` の remaining `_research` caller を順次棚卸し
2. `Squarefree (GN ...)` を供給できる caller は `..._honest` へ移行
3. 供給できない caller は `_research` のまま残すか、専用 target に切る

### 5.3. その先

1. `d > 3` layer-B stub の本格化
2. Kummer non-first-case existence core の単独攻略
3. 周辺構造として `LPS / PowerSwap / PowerSums / CosmicFormula` の分柱整理を進める

---

## 6. 賢狼の最終判断

いまの snapshot は、かなり良い状態じゃ。
少なくとも次ははっきりしておる。

* `d = 3` valuation 再編は、もう主戦場ではない
* `GcdNextResearch` の debt は `d > 3` に押し出せた
* `ZsigmondyCyclotomicResearch` の research root は theorem 名レベルで可視化済み
* したがって次の本線は **remaining `_research` caller の honest migration** じゃ

ひとことで言えば、

**いまは新しい理論を増やす段ではなく、見えている `_research` 依存を 1 本ずつ剥がして mainline を澄ませる段**

じゃよ。

---

## 7. 補足. FLT 本丸と周辺整備の優先度

周辺の設計文書を読む限り、LPS / PowerSwap / GapContours / CosmicFormula / PowerSums の再配置方針はかなり筋がよい。
特に、

* `CosmicFormula`
* `PowerSwap`
* `NumberTheory.PowerSums`

へ分柱し、FLT には橋だけ残す方針は、美しく、将来の再利用性も高い。

ただし現在の priority はあくまで

\[
\text{FLT valuation / Kummer repair}
\quad\gg\quad
\text{LPS 再配置}
\]

じゃ。
LPS 側は設計が固まりつつあるので、ボトルネック戦線が一段静まってから進めるのがよい。
