# review-023: ExceptionalExistence concrete 化の利益を descent chain に実装として落とし込み、`NePCoprimeKernel` 直撃路を見限って、真の本丸を三つの open kernel に分解できたこと

## 1. 作業結果

今回の作業で、`TriominoCosmicBranchADescentChain.lean` に

* `primitivePacketDescent_of_gnReducedGap`
* `smallerPacket_of_gnReducedGap_and_peel`

が追加され、どちらも clean に通った。意味としては、

$$
\text{CyclotomicExistence concrete}
\Rightarrow
\text{primitive descent は GNReducedGap 1 本で足りる}
$$

ことが、定理レベルで固定されたということじゃ。さらに

$$
\text{GNReducedGap} + \text{Peel}
\Rightarrow
\text{SmallerPacket}
$$

も clean に書けたので、Branch A の descent 側の依存関係がかなり明瞭になった。

作業ログの要点を一言で言えば、 **「CyclotomicExistence concrete 化の利益を、descent chain にちゃんと落とし込めた」** ということじゃな。History 側でも Session 23 として、その圧縮が整理されておる。

## 2. 状況分析

ここで一番大事なのは、`NePCoprimeKernel` をどう見るかじゃ。

今回のログが示している最重要点は、`NePCoprimeKernel` の TODO 自身に

* comparison-based refuter の active 情報はここで尽きている
* 最終矛盾は descent / minimality / 別 arithmetic kernel へ設計転換して取りに行く必要がある

という趣旨が明記されていることじゃ。
つまり、 **`Coprime(t,s)` と support separation をいくら磨いても、その場で直に `False` までは届かぬ**。ここが今回の決定的な診断じゃ。

ゆえに、前に見えていた

$$
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

という 2-kernel route は、 **条件付き chain としては最短** でも、 **実際の攻略路としては直撃しにくい**。
これは大きい。設計図としての最短路と、実作業としての最短路がズレている、と判明したからじゃ。

## 3. いま本当に攻めるべき面

今回の作業で、Branch A の descent route はきれいに三つへ分解された。

$$
\text{BranchA}:
\quad
\begin{cases}
\neg p \mid t &\Rightarrow \text{GNReducedGapTarget} \
p \mid t &\Rightarrow \text{ValuationPeelPacketFromError} \
\end{cases}
$$

そして Branch B は

$$
\text{NonLiftableGNBridge}
$$

じゃ。
この三正面が、いまの **実戦用の open kernel** じゃよ。

特に重要なのは、`ValuationPeelPacketTarget` 全体が未完なのではなく、ログ分析で

* `TailError` 側は concrete
* 真の穴は `PacketFromError`

と切り分け済みである点じゃ。
つまり p-adic peel 側も、漫然と巨大ではなく、最後の packet 再構成だけが核として残っておる。

## 4. 数学的な意味

今回の二つの新定理は、単なる配線ではない。

`primitivePacketDescent_of_gnReducedGap` の意味は、

$$
\text{primitive prime } q \mid s
$$

を concrete に取れる以上、残る本体は
**(q)-adic descent によって、新しい gap (g') を作れるか**
に尽きる、ということじゃ。

その内容は

$$
g' \cdot GN(p, g', y) = p^p (t \cdot s')^p
$$

で、これは言い換えると

$$
(g' + y)^p = p^p (t \cdot s')^p + y^p
$$

すなわち

$$
x' = p t s', \quad z' = g' + y
$$

に対して

$$
x'^p + y^p = z'^p
$$

を実現する、ということじゃ。
つまり `GNReducedGapTarget` はまさに **Kummer descent の (q)-adic 核心** そのものじゃ。今回の分析がそこまで露出させたのは、かなり大きい前進じゃよ。

## 5. いまの正確な戦況

だから、戦況を正確に言うならこうじゃ。

* **コード上の新規追加は clean**。今回の追加定理はきれいに通っている。
* **comparison 直撃路は理論上はあるが、実務上は本命ではない**。`NePCoprimeKernel` は直接殴るより、descent を内蔵した形でしか落ちぬ気配が強い。
* **descent route は急に見通しが良くなった**。primitive 側は `GNReducedGap` 1 本、peel 側は `PacketFromError` 1 本、Branch B は `NonLiftableGNBridge` 1 本、と分離できた。

この整理は大きい。
前は「本丸は NePCoprimeKernel か？」と見えておったが、いまは

$$
\text{実作業の本丸} =
\text{GNReducedGapTarget},\ \text{PacketFromError},\ \text{NonLiftableGNBridge}
$$

と、かなり具体化されたからじゃ。

## 6. 解説

賢狼の見立てでは、今回の成果は **“証明の幹が変わった”** に近い。

以前は

$$
\text{NePCoprimeKernel}
$$

が巨大な黒箱として立っておって、そこへ突っ込むしかないように見えていた。
だが今回、その内部 comment と descent chain の依存解析を突き合わせた結果、

* comparison 情報だけでは尽きる
* well-founded descent が本体
* primitive 側と peel 側を分けて攻略するのが正しい

と分かった。
これは単なる進捗ではなく、 **「どこを証明すれば勝てるか」の認識が正しく更新された** という意味で、かなり価値が高い。

## 7. 次の一手

わっちの判断では、次の優先順位はこの順じゃ。

## 7.1. GNReducedGapTarget

理由は単純で、ここは

* CyclotomicExistence concrete
* DescentSeed concrete
* QAdicLiftSeed concrete

まで揃っておる。
残りは (g') の構成だけ、という形まで圧縮されておる。
三正面の中で、いちばん **入力 data が揃っている本丸** じゃ。

## 7.2. ValuationPeelPacketFromError

こちらは `TailError` が concrete なので、真の穴は packet 再構成だけじゃ。
GNReducedGap より少し重いが、構造は見えておる。
p-adic peel の最終段として、ここを独立に詰める価値は高い。

## 7.3. NonLiftableGNBridge

Branch B の独立 kernel。
これは並行で進められるが、いまの momentum は Branch A 側にあるから、優先度は少し下げてよいじゃろう。

## 8. 一文でまとめると

**今回の作業結果は、CyclotomicExistence concrete 化の利益を descent chain に実装として落とし込み、`NePCoprimeKernel` 直撃路を見限って、真の本丸を三つの open kernel に分解できたこと** じゃ。
ゆえに、状況はかなり良い。いまはもう霧の中ではなく、敵の城門が三つ見えておる。

次に進むなら、`GNReducedGapTarget` の証明内容を **「入力 concrete data」→「(g') の構成」→「smaller packet」** の 3 層で切った攻略図にしておくのが最も効くぞい。

---

おお、これは良い作業じゃ。
しかも今回は単なる「補題を 2 本増やした」ではなく、 **どこが本丸で、どこがもう通路として固まったか** がかなり鮮明になったぞい。

## 1. 結果の要約

今回 clean に追加できたのは、

* `primitivePacketDescent_of_gnReducedGap`
* `smallerPacket_of_gnReducedGap_and_peel`

の 2 本じゃ。
意味としては、`CyclotomicExistence` が concrete 化された今、primitive 側は **`GNReducedGap` 1 本** で descent が回る、と定理レベルで確定したことになる。さらに peel 側を合わせれば、Branch A の `SmallerPacket` まで clean に到達できる。

これはかなり大きい。
なぜなら以前は

$$
\text{GNReducedGap} + \text{CyclotomicExistence} + \text{ValuationPeel}
$$

と見えていた Branch A 側が、いまは

* primitive 側: `GNReducedGap`
* peel 側: `PacketFromError`

へ、かなりはっきり分離されたからじゃ。

## 2. 作業ログから読める核心

今回のログでいちばん大事なのは、`NePCoprimeKernel` の TODO の読み取りじゃ。
そこには、comparison-based refuter の active 情報は尽きており、最終矛盾は **descent / minimality / 別 arithmetic kernel** に設計転換して取りに行く必要がある、と読める。
つまり

$$
\text{Coprime}(t,s) + \text{support separation}
$$

だけでは、その場で `False` までは届かぬ、という自己診断がコード内に既に書かれておるわけじゃ。

ここが大きい。
前までは

$$
\text{NePCoprimeKernel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

という 2-kernel chain が見えておったので、「なら `NePCoprimeKernel` を殴ればよいのでは」と思いやすかった。
だが今回の分析で、それは **設計上の最短路** ではあっても、 **実作業上の直撃路ではない** とほぼ確定したわけじゃ。

## 3. いまの正しい戦況図

いまの攻略図は、実質こうじゃ。

```text
BranchA
  ├─ ¬ p ∣ t  → GNReducedGapTarget
  │              （CyclotomicExistence concrete, DescentSeed concrete）
  │
  └─ p ∣ t    → ValuationPeelPacketFromError
                 （TailError concrete, 残る穴は PacketFromError）

BranchB
  └─ ¬ p ∣ gap → NonLiftableGNBridge
```

この整理はログにも明示されておる。
とくに

* `primitivePacketDescent_of_gnReducedGap` によって primitive descent の open kernel は `GNReducedGap` のみ
* `ValuationPeel` 側は `TailError + PacketFromError` に割れていて、実質 open は後者 1 本
* BranchB は `NonLiftableGNBridge` の独立 kernel

という 3 本立てじゃ。  

## 4. GNReducedGap 側の数学内容

ここはとても大事なので、少し丁寧に言うぞい。

`GNReducedGapTarget` が求めているのは、

$$
\exists g',\quad g' \cdot GN(p,g',y)=p^p,(t\cdot s')^p
$$

という (g') の構成じゃ。ここで (s' = s/q) じゃな。
この式は宇宙式の恒等式から

$$
(g'+y)^p-y^p=g' \cdot GN(p,g',y)
$$

だから、

$$
(g'+y)^p = p^p,(t s')^p + y^p
$$

となる。
すなわち

$$
x' := p t s',\qquad z' := g'+y
$$

と置けば、

$$
x'^p + y^p = z'^p
$$

という **新しい FLT 形** を作ることになる。
つまり `GNReducedGapTarget` の正体は、まさに **(x/q) への (q)-adic descent を実現する本体** じゃ。ログでも「Kummer descent の q-adic 核心」と整理されておるのは正しい見立てじゃよ。

しかも今回の分析で、

* primitive prime (q) は CyclotomicExistence concrete から得られる
* `DescentSeed` も concrete
* `QAdicLiftSeed` も concrete

と分かっておる。
だから `GNReducedGapTarget` は、いまや **入力データ不足の問題ではなく、(g') の構成そのものだけが残っている** 段階じゃ。

## 5. PacketFromError 側の数学内容

こちらは p-adic peel の最終段じゃ。

ログ分析では、`ValuationPeelPacketTarget` は

* `PeelSeed_default`: concrete
* `PeelTailError_default`: concrete
* `PeelPacketFromError`: open

に割れておる。
つまり (p \mid t) の場合は、error 方程式

$$
pB = C + p^{p-1} t_1^p E
$$

から **smaller packet を再構成する最後の一歩** だけが未了、ということじゃ。

だから peel 側は巨大な闇ではない。
**出口の packet 再構成だけが残っている** と見てよい。

## 6. 状況分析の結論

賢狼の判定をはっきり言うぞい。

### 6.1. 良い知らせ

今回の作業で、Branch A 側の descent route は **本当に攻められる形** に整理された。
`CyclotomicExistence` concrete 化の利益が、単なる理論でなく、`primitivePacketDescent_of_gnReducedGap` という clean theorem に落ちたのが大きい。

### 6.2. 注意点

「FLT 関連の `sorry` は 1 箇所だけ」と見えても、それをそのまま「残り 1 問」と読んではいかぬ。
`NePCoprimeKernel` は comparison だけで直撃できる型ではなく、実際には descent を内蔵した大核じゃ。
ゆえに、 **コード上の `sorry` の個数** と **数学上の open kernel の個数** は別物じゃ。

### 6.3. いまの実戦的 open kernel

実質的には次の 3 本じゃ。

$$
\text{GNReducedGapTarget},\quad
\text{ValuationPeelPacketFromError},\quad
\text{NonLiftableGNBridge}
$$

この三つが、今の **本当に手を入れるべき城門** じゃ。

## 7. 優先順位

わっちの見立ては、やはり変わらぬ。

### 1. `GNReducedGapTarget`

これが最優先じゃ。
理由は、入力がもう concrete に揃っておるからじゃ。残る未解決成分が、最も純粋に「数学の本体」だけになっておる。

### 2. `ValuationPeelPacketFromError`

`TailError` が concrete なので、ここも見通しは悪くない。
ただし packet 再構成は Kummer 的な濃い部分を含むので、GNReducedGap より一段重い。

### 3. `NonLiftableGNBridge`

独立 kernel じゃから並行可能。
ただ、今の momentum は Branch A にあるので、優先は少し下げてよい。

## 8. 一文でまとめると

**今回の作業結果は、CyclotomicExistence concrete 化の利益を descent chain の実定理へ落とし込み、`NePCoprimeKernel` 直撃路を実戦上は退かせて、真の本丸を `GNReducedGapTarget`・`PacketFromError`・`NonLiftableGNBridge` の三正面にまで露出させたこと** じゃ。
これはかなり大きい前進じゃよ。

次は、`GNReducedGapTarget` について
**「入力 concrete data」→「(g') 構成」→「smaller counterexample 化」**
の三段攻略図まで裂いてやるのが良い。

---

よし、`GNReducedGapTarget` の **三段攻略図** を起こすぞい。
いまの状況では、primitive 側はもう

$$
\text{CyclotomicExistence concrete} + \text{DescentSeed concrete}
$$

まで揃っており、`primitivePacketDescent_of_gnReducedGap` が clean に通ったことで、 **open kernel は `GNReducedGapTarget` ただ 1 本** と見てよい。ここが今回の最大の整理じゃ。

## 1. 第1段. 入力 concrete data の固定

ここでは「何が既に揃っていて、何を自由変数として扱うか」を固定する。
いま primitive 側で使える concrete data は、だいたい次の束じゃ。

$$
(p,x,y,z,t,s,q,s')
$$

で、条件は

$$
z-y = p^{p-1} t^p,\qquad
GN(p,z-y,y) = p,s^p,\qquad
q \mid s,\qquad s' = s/q,
$$

さらに

$$
\neg p \mid t,\qquad q \ne p,\qquad \gcd(q,y)=1,\qquad q \nmid t
$$

のような primitive prime 条件が乗る。
そして今回の concrete 化で、`CyclotomicExistence` 側からこの (q) が取り出せる。加えて `DescentSeed` と `QAdicLiftSeed` も concrete と分析されておる。つまり、**入力不足ではなく、構成本体だけが残っている** 段階じゃ。

この段でやるべき補題は 1 本に尽きる。

```text id="qiqngd"
InputCompression:
  Pack + normal form + primitive q
  → GNReducedGapTarget の仮定列を 1 つの bundle に束ねる
```

Lean 的には、「hpack」「hp_dvd_gap」「hgap」「hsGN」「hcop」「hWieferich」「hqprime」… と散らばっている入力を、1 つの局所構造に縮約するのがよい。
ここは数学ではなく、作業効率の問題じゃ。

## 2. 第2段. 核心構成 (g') の生成

ここが本丸じゃ。
`GNReducedGapTarget` の中身は

$$
\exists g',\quad g' \cdot GN(p,g',y)=p^p,(t s')^p
$$

を作ることじゃな。
宇宙式の恒等式から、これはそのまま

$$
(g'+y)^p - y^p = p^p,(t s')^p
$$

と同値で、さらに

$$
x' := p t s',\qquad z' := g'+y
$$

と置けば

$$
x'^p + y^p = z'^p
$$

になる。
つまり第2段の本質は、**(x' = x/q) に対して新しい (p) 乗根 (z') を構成すること** じゃ。ログでも、ここが Kummer descent の (q)-adic 核心と分析されておる。

この段は、さらに 2 層に割るのがよい。

### 2.1. q-adic root existence 層

まず作るべきは

$$
(x/q)^p + y^p
$$

が完全 (p) 乗になる、という existence の芯じゃ。
ここで concrete にあるのが `QAdicLiftSeed` の

$$
\omega \in \mathbb{Z}/q\mathbb{Z},\qquad \omega^p=1,\qquad \omega \ne 1
$$

という data じゃ。
だからこの層の狙いは、

```text id="krvfvc"
QAdicLiftCore:
  q-adic lift seed + q^p ∣ GN + primitive conditions
  → ∃ z', z'^p = p^p (t s')^p + y^p
```

という形にすることじゃ。

### 2.2. gap への変換層

(z') が作れたら、

$$
g' := z' - y
$$

と置いてよい。
すると自動的に

$$
g' \cdot GN(p,g',y)=z'^p-y^p=p^p,(t s')^p
$$

が出る。
ゆえに、数学的な真の難所は「(g') を直接作る」ことではなく、**(z') を作ること** じゃ。
これはかなり大事な視点転換じゃよ。
`GNReducedGapTarget` を gap の問題として見るより、 **perfect (p)-th root existence** の問題として見るほうが整理しやすい。

## 3. 第3段. 出口として smaller counterexample へ落とす

第2段で (g') か (z') が出来れば、出口はかなり機械的じゃ。

$$
z' = g' + y,\qquad x' = p t s'
$$

で、

$$
x'^p + y^p = z'^p
$$

を持つ新しい realization seed ができる。
そこから既存の restore chain に流せば、smaller packet、smaller counterexample へ行ける。実際ログでも

$$
\text{GNReducedGapTarget}
\to \text{PthRootReduced}
\to \text{RealizationSeed}
\to \text{SmallerCounterexample}
$$

という spine が見えておる。

この段で必要なのは、主に「小ささ」の確認じゃ。

$$
x' = x/q < x
$$

は明らかじゃが、Lean 上で本当に使うのはたいてい

$$
z' < z
$$

の方じゃろう。
ゆえに出口層では、

```text id="wvrwvh"
RealizationToSmaller:
  z'^p = x'^p + y^p
  and x' = x/q
  → z' < z
  → smaller packet
```

という補題に分離しておくのがよい。
ここは arithmetic core というより、既存 well-founded descent へ接続する橋じゃ。

## 4. まとめた攻略図

```text id="odg4qg"
[第1段 入力固定]
  Pack + normal form + primitive q + DescentSeed
    ↓
  concrete bundle 化

[第2段 核心構成]
  q-adic lift data
    ↓
  ∃ z', z'^p = p^p (t s')^p + y^p
    ↓
  g' := z' - y
    ↓
  g' * GN(p,g',y) = p^p (t s')^p

[第3段 出口]
  x' := p t s', z' := g' + y
    ↓
  x'^p + y^p = z'^p
    ↓
  z' < z
    ↓
  smaller packet / smaller counterexample
```

## 5. 実際の作業順

わっちなら、次はこの順で書く。

### 5.1

`GNReducedGapInputBundle` 的な圧縮補題を作る。
これは数学ではなく、入力整理じゃ。

### 5.2

本丸補題として

```text id="tjuigb"
qAdicLift_to_pthRootReduced
```

のような名で、

$$
\exists z',\ z'^p = p^p (t s')^p + y^p
$$

を直接目標化する。
ここが真の核心じゃ。

### 5.3

そこから

```text id="5bsyhy"
gnReducedGap_of_pthRootReduced
```

で (g' = z' - y) に落とす。
こうすれば `GNReducedGapTarget` 自体は薄い wrapper になる。

### 5.4

最後に

```text id="n6psvi"
smallerCounterexample_of_gnReducedGap
```

で既存 descent chain に戻す。

## 6. ひとことで言うと

`GNReducedGapTarget` は **「(g') を作る問題」ではなく、「(x/q) に対応する新しい (p) 乗根 (z') を作る問題」** と見たほうが、圧倒的に攻めやすい。
この見方に立つと、

* 第1段は入力整理
* 第2段は q-adic lift による (z') 構成
* 第3段は smaller counterexample への出口

の三段にきれいに裂けるのじゃ。

次はこの三段を、そのまま Lean の補題名の雛形にして書き起こすとよい。
