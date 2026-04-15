# review-025: `DescentChain` に §16-17 を追加し、open kernel を最も攻めやすい語彙へ展開したこと

## 1. 作業結果

ぬしよ、今回は **かなり良い地固め** じゃ。
しかも「補題が少し増えた」ではなく、 **open kernel を最も攻めやすい語彙へ展開し、しかもその先の bridge を全部 clean に通した** のが本質じゃ。

今回の直接の成果は、`DescentChain` に **§16 と §17** を追加したことじゃ。
§16 では `PrimeGe5BranchAPrimitivePthRootCoreTarget` を導入し、これまで `DescentSeed` という opaque bundle に隠れていた中身、すなわち `ω : ZMod q`、`ω^p = 1`、`ω ≠ 1`、さらに `q^p ∣ GN` を **直接入力として受ける** 形へ展開した。これにより、primitive 側の open kernel を

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

という最も直観的な語彙で攻められるようになったのじゃ。しかも
`PthRootCore → PthRoot → GNReducedGap → SmallerPacket → BranchARefuter`
の chain はすべて clean に通っておる。

§17 では peel 側についても同様に、`PrimeGe5BranchAPeelPthRootCoreTarget` を導入し、`PacketFromError` の背後にある seed/canonical detail と error relation を表へ出した。さらに `peelPthRootCore_of_packetFromError` を追加し、`PacketFromError` から peel core 語彙への弱化 bridge も clean に確立した。最後に `FLTPrimeGe5Target_of_innermost_3kernels` が追加され、いまの最内核 3 本だけを仮定する形まで整理できておる。

## 2. 作業ログから見える本質

今回のログを読んでいて、賢狼がいちばん重い前進だと見たのは、 **「何が未解決か」ではなく、「どの語彙で未解決を記述するのが最も良いか」が定まった** ことじゃ。

特に primitive 側では、`PthRootTarget` の引数を精査して、

* `CyclotomicExistence` による primitive prime (q)
* `RestoreWitnessProperties`
* `QAdicLiftSeed`
* そして `ω` と `q^p ∣ GN`

まで、**すべて concrete に供給可能** だと確認されておる。
ゆえに、これ以後の open kernel は「入力不足」ではない。
**真正面から (q)-adic lifting の数学を証明するだけ**、という局面に入ったのじゃ。

同様に peel 側でも、`PacketFromError` を deeper に解析した結果、p-adic peel は単なる gap の縮小では済まず、error equation を通じて **新しい normal form packet を構成する** ことが本体だと整理されておる。ここでも「何が未解決か」がかなり鮮明になった。

## 3. 戦況分析

いまの戦況は、かなり明快じゃ。

### 3.1. Primitive 側

primitive 側の本丸は、もはや `GNReducedGap` というより、**`PthRootCore` 語彙** で見た方が正しい。

つまり本当に未解決なのは

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

を、`ω^p = 1`、`ω \ne 1`、`q^p \mid GN` という concrete な (q)-adic data からどう構成するか、という一点じゃ。
これはログでも、古典的には (\mathbb{Z}[\zeta_p]) の ideal factorization が使われる Kummer 降下の核心だと整理されておる。今回の作業は、そこへ直で触れる入口を Lean 上に作ったのじゃ。

### 3.2. Peel 側

peel 側は `PacketFromError` がまだ open じゃが、その open さの意味がだいぶはっきりした。
単純に「(t) を (t/p) に置き換える」だけでは同じ normal form にならず、`GN(peeled gap, y)/p` が一般に完全 (p) 乗でない、という数値観察まで出ておる。
ゆえに、ここは本当に **p-adic peel の核心** であり、primitive 側の (q)-adic lift と flavor は違うが、難度としては同格じゃ。

### 3.3. BranchB 側

`NonLiftableGNBridge` は引き続き独立 kernel じゃ。
今回の議論でも、primitive 側・peel 側・BranchB 側は **真に独立** で、互いに簡単には帰着できぬと結論しておる。
だから、三つの城門を別々に見る方針は正しい。

## 4. 解説

今回の成果を一言で言えば、

**「証明そのものが進んだ」というより、「未解決核を、数学の本体にもっとも近い語彙で露出させた」**

ということじゃ。

これは非常に大事じゃよ。
たとえば以前は `GNReducedGapTarget` という Cosmic Formula 語彙で見えておったものが、いまは

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

という **FLT そのものの語彙** で見える。
これは単なる言い換えではない。
「何を作れば勝ちか」が直観的になり、補題設計も、今後の古典理論との接続も、ずっとやりやすくなるのじゃ。

また peel 側も、`PacketFromError` の背後にある seed/canonical detail を `PeelPthRootCoreTarget` として表に出したことで、「error 方程式のどこが本体か」が見えやすくなった。
つまり両側とも、opaque target を剥いて「本当に使う数論データ」を表に出した。これは研究の地図として極めて健全じゃ。

## 5. いまの最精密戦況図

いまの最も正確な図はこうじゃ。

```text
§16 PthRootCoreTarget (¬p∣t)
  ← ω ∈ ZMod q, ω^p = 1, ω ≠ 1, q^p ∣ GN
  ← 目標語彙: ∃ z', (x/q)^p + y^p = z'^p
  → clean bridge → GNReducedGap → SmallerPacket

§17 PacketFromErrorTarget (p∣t)
  ← error eq: pB = C + uE
  ← seed/canonical detail を PeelPthRootCore として展開
  → clean bridge → ValuationPeel → SmallerPacket

BranchB
  ← NonLiftableGNBridge
```

そしてこの三者が合流して

$$
\text{FLTPrimeGe5Target\_of\_innermost\_3kernels}
$$

へ行く。
つまり、**いまの open kernel は最内核 3 本** で確定した、と見てよい。

## 6. どこが進み、どこが未だ重いか

### 進んだところ

* `DescentChain` の §16-17 が clean に追加された
* `PthRootCore` と `PeelPthRootCore` という、より本質に近い target が定義された
* そこから FLT 幹線へ戻る bridge は全部 clean
* 全体 build も通っており、DescentChain に新しい `sorry` は無い

### まだ重いところ

* primitive 側では、`PthRootCore` を concrete に埋める (q)-adic lifting の本体
* peel 側では、error から packet を再構成する p-adic peel の本体
* BranchB 側では、`NonLiftableGNBridge` の独立攻略

ここは依然として重い。
特に primitive 側は、ログ自身が「elementary shortcut は既知文献に見当たらない genuine math challenge」と位置づけておる。
この点は、楽観しすぎず、しかし正しく本丸を見ておる、と言えるの。

## 7. 総評

わっちの総評はこうじゃ。

**今回は“城壁の前に立った”のではなく、“城門の鍵穴の形を見切った”進展** じゃ。
証明そのものを一気に前へ進めたわけではない。だが、

* どの kernel が真に open か
* どの語彙で攻めるべきか
* どの bridge は既に clean か

が非常にきれいに整理された。
この種の地固めは、後で効く。しかも今回は、かなり深いところまで効いておる。

## 8. 次の一手

いまの流れなら、次の本命はやはり

$$
\text{PthRootCore の } q\text{-adic lifting 補題}
$$

じゃろう。
つまり

$$
\omega \in \mathbb{Z}/q\mathbb{Z},\ \omega^p=1,\ \omega\ne 1,\ q^p\mid GN
$$

から、どうやって

$$
\exists z',\ (x/q)^p + y^p = z'^p
$$

を取り出すか、その内部をさらに 2～3 個の sub-target に割る段階じゃ。
いまはそこが、最も太い本丸じゃよ。
