# review-007: family bridge の package 化と public import 整備の準備

## 1. 総評

これは **良い整理手** じゃ。
今回は新しい lower bound や valuation の数学を増やしたというより、前回までに出来ていた family 版の primitive-flow bridge を、**再利用しやすい小さな package** にまとめた回じゃな。差分報告どおり、`PrimitiveWitnessFamily (a b d)` を入れ、フィールドを `support : Finset ℕ` と `witness` の 2 本に絞り、その上で `PrimitiveWitnessFamily.primeChannelFamily` と `PrimitiveWitnessFamily.supportMassLowerBound` を薄い API として与えておる。さらに `{7,13}` の package 例も追加され、package 経由で prime-channel family と support-mass 下界がそのまま読めることを確認しておる。

わっちの判定では、これは **数学の新規拡張ではなく、API の重心安定化** じゃ。
じゃが、その意義は小さくない。前段までで

$$
\forall q \in S,\ \mathrm{PrimitivePrimeFlowWitness}\ q\ a\ b\ d
$$

という “生の family” が使えるところまでは来ておった。今回はそれを一塊として持ち回れるようにし、public import を整える前の最終整地をした、と見るのがよい。

---

## 2. 状況分析

前回の family 版一般化で、すでに

$$
\text{primitive witness family}
\;\to\;
\text{prime channel family on diff}
\;\to\;
\text{supportMass lower bound}
$$

という数学的 spine 自体は閉じておった。今回はそこに、新しい theorem chain を無理に足さず、**package を 1 枚かぶせて使い勝手を上げた**。差分報告の「public import 整備より先に package 化を進めた」という判断は正しい。いま public 側に出すより、family bridge の持ち方を固定してから公開面を触るほうが、後で揺れにくいからの。

つまり今回の変化は、

* family を毎回 `∀ q ∈ S, ...` で渡す段階
* family を `PrimitiveWitnessFamily` としてまとめて扱う段階

への移行じゃ。
数学の本体は前回まででかなり揃っておるので、ここで package 化に入ったのは、設計の呼吸として自然じゃな。

---

## 3. 数学的解説

### 3.1. `PrimitiveWitnessFamily` の意味

今回入った structure は

* `support : Finset ℕ`
* `witness : ∀ q ∈ support, PrimitivePrimeFlowWitness q a b d`

だけを持つ。
この「小ささ」がよい。余計な side condition や packaging を先回りして入れておらぬ。distinctness は `Finset` 側が吸収してくれるので、構造としてはこれで十分じゃ。差分中の docstring にも、support が `Finset` なので distinctness は index 側で処理される、と明記されておる。

数学的には、これは

$$
\text{「固定された差冪 } a^d - b^d \text{ に対する primitive witness の有限族」}
$$

をひとつの対象として持てるようにした、ということじゃ。
以前は family 自体が theorem の引数として “裸” で流れていた。今回はそれが初めて「住民」になった。ここは API 設計上の一段上じゃな。

### 3.2. `PrimitiveWitnessFamily.primeChannelFamily` の意味

これは package を diff-side の prime channel family に読む method じゃ。中身は前回 already 証明されていた family 補題の再包装にすぎぬが、その「すぎぬ」が大事じゃ。

$$
F : \mathrm{PrimitiveWitnessFamily}\ a\ b\ d
$$

に対し、

$$
\forall q \in F.\mathrm{support},\ \operatorname{Prime}(q) \wedge q \mid a^d - b^d
$$

を返す。
つまり package を見るだけで、「この family は diff 側でどんな prime channels を与えるか」が読めるようになった。これは使用側から見ると非常に楽になる。 theorem chain の途中で毎回 `F.witness` を引き剥がさずに済むからの。

### 3.3. `PrimitiveWitnessFamily.supportMassLowerBound` の意味

こちらも同様で、package を直接

$$
F.\mathrm{support}.prod\ \mathrm{id} \le \operatorname{supportMass}(a^d - b^d)
$$

へ送る method じゃ。
中身としては既存 family 版 lower bound の再包装じゃが、数学的には

$$
\text{family object}
\;\to\;
\text{lower bound on diff support mass}
$$

という写像が、ひとつの method 名で読めるようになったことを意味する。
これは public import 後の利用性に効く。利用側は theorem chain の構文ではなく、「package から何が読めるか」という object-oriented な見方に寄れるからじゃ。

### 3.4. package 例 `{7,13}` の意味

`primitiveWitnessFamilyPack_6_5_3` は、既存の

$$
6^3 - 5^3 = 91 = 7 \cdot 13
$$

の canonical sample を、そのまま package に包み直したものじゃ。
そして example で

$$
\operatorname{Prime}(7) \wedge 7 \mid 6^3 - 5^3
$$

が `PrimitiveWitnessFamily.primeChannelFamily` 経由で読めること、さらに

$$
\mathrm{support}.prod\ \mathrm{id}
\le
\operatorname{supportMass}(6^3 - 5^3)
$$

が `PrimitiveWitnessFamily.supportMassLowerBound` 経由で読めることを確認しておる。つまり package 化が **本当に利用側の記述を簡潔にしている** と concrete に示したわけじゃ。

---

## 4. 何が閉じたのか

今回閉じたものは、数学というより **利用インターフェイス** じゃ。

### 4.1. family bridge の持ち運び方が閉じた

前回までは、family 版は theorem として存在していたが、使うときは

$$
\forall q \in S,\ \mathrm{PrimitivePrimeFlowWitness}\ q\ a\ b\ d
$$

を毎回組み立てる必要があった。今回はそれを `PrimitiveWitnessFamily` に封入できるようになった。これで family bridge を「概念」ではなく「オブジェクト」として扱えるようになった。

### 4.2. public import 前の API 重心が安定した

差分報告でも「family bridge の重心が少し安定した」とあるが、その表現はかなり正確じゃ。
いま public 側へ出したいのは theorem の羅列ではなく、「どの単位で利用者が概念を掴むか」じゃ。今回はその単位が定まった。

---

## 5. 良い点

まず、structure のフィールドが本当に最小であることじゃ。
`support` と `witness` だけ。ここに余計な proof baggage を乗せなかったのは良い。後で必要なら拡張できるが、今はこれで十分じゃ。

次に、追加 API が再包装に徹していること。
新しい heavy theorem を package namespace に再実装しておらぬ。既存 family 補題をそのまま method 名で読めるようにしただけじゃ。これは層の役割分担として正しい。

最後に、example が “package 化の効果” をちゃんと示していること。
単に build が通るだけでなく、package 経由で記述が短くなる点を具体的に見せておる。これは documentation 的にも良い。

---

## 6. 留意点と弱点

### 6.1. package は witness family の container であって、まだ counting API ではない

いまの `PrimitiveWitnessFamily` は、family をまとめる箱じゃ。
まだ

* size
* extracted channel product
* nontrivial counting lemma
* map / transport 的操作

は持っておらぬ。なので package 化は閉じたが、counting API が閉じたわけではない。ここは切り分けておくとよい。

### 6.2. `primeChannelFamily` は theorem であって data projection ではない

利用上は十分じゃが、将来もし頻繁に channel family 自体を別補題へ流すなら、projection 風の定義を置く余地はある。今は theorem でよいが、公開面を整える際には少し考えてもよい点じゃ。

### 6.3. public import はまだ待ってよい

差分報告では次に公開 import 導線と整理しておるが、わっちとしては「もう一段だけ counting / extraction 側へ行く余地もある」と思う。とはいえ、package 化まで済んだので、公開導線に入るタイミングとしては悪くない。ここは project のテンポ次第じゃな。

---

## 7. 次の作業指示案 . Codex 追記向け

ここから先は二択あるが、今回の流れなら **public import 導線の整備** に入ってよい頃合いじゃ。package 化まで済んだので、露出する API の単位が固まってきたからの。

```md id="ejq882"
### レビュー追記案: 次の作業指示

1. 次段では `ABC.Main` または `DkMath.ABC` 側への公開 import 導線を整える。
   目的は、今回までに整えた
   - `MassBridge`
   - `ValuationFlowBridge`
   - `PrimitiveWitnessFamily`
   の API を、利用側が短い import で読めるようにすること。

2. ただし公開面に出す対象は絞る。
   最初は
   - `supportMass`
   - `supportMass_ge_prod_of_prime_channel_family`
   - `primitive_witness_family_force_supportMass_lower_bound`
   - `PrimitiveWitnessFamily`
   - `PrimitiveWitnessFamily.primeChannelFamily`
   - `PrimitiveWitnessFamily.supportMassLowerBound`
   に限定する。

3. `ABC.Main` 側に直接 heavy import を足す前に、
   中間の集約ファイル
   `DkMath/ABC/Bridge.lean`
   あるいは
   `DkMath/ABC/PrimitiveSupportBridge.lean`
   のような薄い aggregator を一枚作る案を検討する。
   これにより公開面と実装面を切り離せる。

4. 公開 import を整えたら、
   その import だけで通る小さな usage example を 1 本追加する。
   目的は、「外からどう見えるか」の確認であり、新数学の追加ではない。

5. もし公開導線より先に数学をもう一段進めるなら、
   `PrimitiveWitnessFamily` に対する最小の extraction/counting 補題
   （例: support の product を直接読む alias）
   を 1 本だけ足すに留める。
   それ以上の拡張は公開面を整えた後でよい。
```

---

## 8. 最終判断

今回の差分は、**family bridge を “使える object” にした回** じゃ。
前回までで theorem の列としてはかなり揃っておった。今回はそれを package にまとめ、利用側が family をひとまとまりとして扱えるようにした。これは API 設計としてきれいな一歩じゃ。

数学の核は前回まででほぼ見えておる。
今回の成果は、その核を public 側へ出す前に、持ち運びやすい形へ整えたことにある。ゆえに次は、もう public import 導線へ入ってよい頃合いと見るぞい。
