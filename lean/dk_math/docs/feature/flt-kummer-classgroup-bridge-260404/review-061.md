# 061. `d = 3` 整理の完了と honest migration の本線化

## 1. 状況分析

いまの盤面は、かなり健全になったぞい。

まず `GcdNextResearch` 側では、`d = 3` の古い上界路線が **研究専用の互換層** へきれいに押し込められた。`padicValNat_d3_upper_bound_of_boundaryReceiver` は `..._research` へ改名され、旧名は deprecated alias になり、さらに legacy な境界注入も private lemma に局所化された。結果として、`GcdNextResearch` 側の direct な `sorry` は **`d > 3` の layer-B stub だけ** だと整理できる。これは大きい。つまり `d = 3` 戦線は、もはや本丸ではなく、互換維持のための薄い殻になったのじゃ。

次に `ZsigmondyCyclotomicResearch` 側でも、research 依存と honest 依存の名前が分離された。`squarefree_implies_padic_val_le_one_research` と `padicValNat_primitive_prime_factor_le_one_research` が立ち、旧 public 名は deprecated alias に落ち、置換先は `..._honest` に向けられた。さらに実コード上の remaining caller も旧名から `_research` 名へ差し替えられておる。つまり今後は、 **どこが未修復の研究依存かが theorem 名だけで見える** 状態になったわけじゃ。

この二つを合わせると、戦況はこう読める。

$$
\text{`d = 3` の整理戦} \approx \text{ほぼ完了}
$$

$$
\text{残る主戦場} = \text{`ZsigmondyCyclotomicResearch` の honest migration}
$$

じゃよ。
前は「どこが古い偽 API に依存しているか」が濁っておった。いまは違う。
**debt の所在地が名前で追える** 。ここが肝じゃ。

## 2. 解説

今回の進展の本質は、証明が増えたことよりも **地図が正しくなったこと** にある。

旧 public 名がそのまま research root を背負っておると、downstream caller から見ると

$$
\text{honest な依存}
\quad\text{と}\quad
\text{research placeholder 依存}
$$

の見分けがつかぬ。
これは戦況判断を鈍らせる。今回それをやめて、

* honest に寄せられるものは `..._honest`
* まだ寄せられぬものは `_research`

へはっきり割った。

また `GcdNextResearch` 側でも、`d = 3` の legacy 境界注入が research-only helper に押し込められたので、今後「`d = 3` がまだ未整理だから general route へ進めない」という言い訳はもう通らぬ。残る `sorry` は `d > 3` stub と `ZsigmondyCyclotomicResearch` の research root だけ、とかなり明快になった。

要するに、いまは **数学の霧を払う段が終わって、残務の帳簿を付け直した段** じゃ。
この手の整理は地味に見えるが、実はかなり強い。次の攻め先を迷わず決められるからの。

## 3. 次の戦略

わっちなら、次は **caller migration の本線化** に入る。
ただし、無差別に全部移すのではなく、三段で攻めるのがよい。

### 3.1. 第一段. remaining `_research` callsite の棚卸しを固定する

今回の report で、実コード上の remaining `_research` 依存箇所はかなり絞られておる。少なくとも

* `PrimitiveBeam.lean` の 2 箇所
* `GcdNextResearch.lean` の research-only boundary receiver 注入
* `CosmicPetalBridgeGNNoWieferichResearch.lean` の primitive-core theorem

が名指しされておる。まずはこの集合を **残敵一覧** として固定し、各 callsite について

$$
\text{Squarefree bridge を供給できるか}
$$

$$
\text{供給できないなら local target 化すべきか}
$$

を一つずつ判定するのじゃ。

### 3.2. 第二段. 移せる caller から `..._honest` へ寄せる

ここが実務の本体じゃ。
特に `PrimitiveBeam` は過去の流れから見て、`Squarefree (GN ...)` 仮定を足せば honest route へ移せる補題がすでに揃っておる。ゆえに、ここは「研究依存を残す理由が本当にあるか」を再点検し、持てる caller から順に `_research` を剥がすのがよい。

戦術としては、

$$
\text{old theorem}
\;\rightsquigarrow\;
\text{new theorem with strengthened hypothesis}
$$

の overload を作り、先に downstream を移し、その後で旧 theorem を compatibility に落とす、という順が安全じゃろう。

### 3.3. 第三段. 移せない caller は target 分離で追跡可能にする

もし `Squarefree (GN ...)` をその場で供給できぬなら、そこで無理に旧 theorem を温存するのはよくない。
そういう箇所は `_research` 名のまま残すか、あるいは専用 target を切って

$$
\text{不足している仮定は何か}
$$

を theorem 名で明示した方がよい。
今回の整理の精神はそこにあるからの。
隠れた debt を増やすより、露出した debt を増やす方がはるかに健全じゃ。

## 4. 推論される最善手

なので次の最善手は、 **`ZsigmondyCyclotomicResearch` 側の remaining `_research` caller を 1 本ずつ honest / research に仕分けて、最初の 1 本を実際に `..._honest` へ移すこと** じゃ。

特に狙い目は `PrimitiveBeam` じゃろう。
理由は三つある。

第一に、すでに squarefree-GN を足した honest 版の方向性が見えておる。
第二に、今回 `_research` 名へ落とされたことで、未修復箇所が目立つ。
第三に、ここを 1 本でも移せれば、「`_research` 名へ落とすだけでなく、実際に剥がせる」ことが示せる。
この一歩は象徴的にも大きい。

## 5. まとめ

いまの戦況はこうじゃ。

* `d = 3` legacy 整理はほぼ完了
* `GcdNextResearch` の direct `sorry` は `d > 3` stub に縮退
* `ZsigmondyCyclotomicResearch` の research root は名前の上でも隔離完了
* 次の本線は **honest migration の実行**

つまり、もはや「どこを直すべきか分からぬ」段ではない。
**どの `_research` を次に剥がすかを選ぶ段** じゃよ。

わっちの提案を一文で言えば、

**次は `PrimitiveBeam` を先頭に、remaining `_research` callsite を 1 本ずつ `..._honest` へ移し、移せぬ箇所だけを target 分離で残す。**

これがいちばん筋がよく、進捗も見えやすい。
