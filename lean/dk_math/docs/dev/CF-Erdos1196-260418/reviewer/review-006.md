# review-006: prime channel family 版の lower bound と primitive witness family からの導線

## 1. 総評

これは **きれいな一般化** じゃ。
前回までで閉じていた 2-channel 版の lower bound を、今回は `Finset` family 版へ持ち上げた。そのうえで、primitive witness family から同じ lower bound へ流す adapter まで入れておる。差分報告の整理どおり、`MassBridge` 側には

* `prime_channel_family_prod_dvd_supportMass`
* `pairwise_distinct_prime_channel_family_lower_bound`
* `supportMass_ge_prod_of_prime_channel_family`

が追加され、`ValuationFlowBridge` 側には

* `primitive_witness_family_gives_prime_channel_family_on_diff`
* `primitive_witness_family_force_supportMass_lower_bound`

が追加されておる。さらに example も `MassBridgeExamples` と `ValuationFlowBridgeExamples` に足され、build も通っておる。

わっちの判定では、今回で

$$
\text{prime channel family}
\;\to\;
\text{supportMass lower bound}
$$

と

$$
\text{primitive witness family}
\;\to\;
\text{prime channel family on diff}
\;\to\;
\text{supportMass lower bound}
$$

の二本が、有限集合レベルで閉じた。ここはかなり節目じゃ。前回は「二本の witness をどう束ねるか」という段階だったが、今回は **family をそのまま扱える語彙** が入ったので、今後の counting 系へ進みやすくなった。

---

## 2. 状況分析

今回の差分の本質は、単なる theorem の追加数ではなく、**下界 spine の単発版が family 版へ昇格した** ことじゃ。
もともと前回までに

$$
q_1 q_2 \le \operatorname{supportMass}(a^d-b^d)
$$

という 2-channel 版は入っておった。今回はそれを

$$
\prod_{q \in S} q \le \operatorname{supportMass}(n)
$$

という `Finset` family 版へ上げた。しかも `Finset` を index に使うことで、distinctness を別仮定で持たずに済ませておる。差分報告にも「distinctness は集合側に吸収」とあるが、これは設計としてとても自然じゃ。 radical 的対象を扱っているのだから、重複を最初から捨てる `Finset` は相性が良い。

さらに良いのは、これを `MassBridge` だけで終わらせず、`ValuationFlowBridge` 側でも family 版 adapter を入れたことじゃ。
つまり今回は

$$
\text{supportMass} = \operatorname{rad}
$$

の family lower bound と、

$$
\text{primitive flow family}
$$

の橋が、同じ turn でそろった。これは実務上も数学上も良い進め方じゃ。片側だけ generalize すると、もう片側がすぐ古くなるからの。

---

## 3. 数学的解説

### 3.1. `prime_channel_family_prod_dvd_supportMass` の意味

ここが今回の中心じゃ。
定理の中身は、

* \(S\) の各元 \(p\) が prime
* しかも \(p \mid n\)

なら

$$
\prod_{p \in S} p \mid \operatorname{supportMass}(n)
$$

を言っておる。証明は `supportMass = rad` の定義を展開し、`S` が `n.factorization.support` の部分集合になることを示してから、`Finset.prod_dvd_prod_of_subset` で流している。これは非常に素直じゃ。

数学的に言えば、これは

**「support mass は、含まれる全 prime channel を multiplicative に記録している」**

という主張じゃな。
前回の二本版は prime と coprime を使って手で掛け合わせていたが、今回は support 全体の部分集合という見方へ切り替わった。ここで proof style が「coprime による局所合成」から「support への包含による一括処理」へ変わったのが美しい。family 版らしい証明になっておる。

### 3.2. `pairwise_distinct_prime_channel_family_lower_bound` と alias の意味

ここでは上の divisibility から positivity を使って

$$
\prod_{p \in S} p \le \operatorname{supportMass}(n)
$$

を出しておる。
つまり今回の lower bound は、前回と同じく

$$
\text{divisibility} \Rightarrow \text{inequality}
$$

の形で立っておる。rad 的対象に対してはこの順が正攻法じゃ。
`supportMass_ge_prod_of_prime_channel_family` を alias にしておるのも良い。証明の中身は同じでも、bridge 語彙としての読み方を固定できるからの。

### 3.3. `primitive_witness_family_gives_prime_channel_family_on_diff` の意味

ここは `ValuationFlowBridge` 側の minimal adapter じゃ。
family \(S\) の各 \(q\) に対して primitive witness があれば、

$$
q \in S \Rightarrow \bigl(\operatorname{Prime}(q) \wedge q \mid a^d-b^d\bigr)
$$

を返す。
つまり primitive witness family を、そのまま diff 側 prime channel family に送り込める。ここでやっていることは一見小さいが、本質的には **witness family の意味の変換** じゃ。ValuationFlow の住民を ABC/MassBridge の住民へ変える薄い関手のような役目をしておる。

### 3.4. `primitive_witness_family_force_supportMass_lower_bound` の意味

これで、上の adapter をそのまま `supportMass_ge_prod_of_prime_channel_family` に流し、

$$
\prod_{q \in S} q \le \operatorname{supportMass}(a^d-b^d)
$$

を得ておる。
つまり構造は完全に

$$
\text{primitive witness family}
\;\to\;
\text{prime channel family}
\;\to\;
\text{supportMass lower bound}
$$

じゃ。
この一本化が今回の真価じゃな。前回までは 2 本版で「そうなりそう」と見えていた流れが、今回は family 全体で言えるようになった。しかも heavy な新証明ではなく、既存補題の合成だけで閉じている。これはとても良い。

### 3.5. examples の意味

`MassBridgeExamples` では

$$
({2,3} : \mathrm{Finset},\mathbb{N}).\prod \mathrm{id} \le \operatorname{supportMass}(12)
$$

を通しておる。これは前回の `2 * 3 ≤ supportMass 12` の family 版への持ち上げじゃ。
`ValuationFlowBridgeExamples` では

$$
({7,13} : \mathrm{Finset},\mathbb{N}).\prod \mathrm{id}
\le
\operatorname{supportMass}(6^3 - 5^3)
$$

を通しておる。こちらは前回の `7,13` 二本 witness 例の family packaging 版じゃ。
つまり両側とも、「前回の 2 本版が今回の family 版へ自然に上がる」ことを concrete に見せている。これがよい。

---

## 4. 何が閉じたのか

今回閉じたものは、数学的には次の二つじゃ。

### 4.1. lower-bound spine の family 化

前回までの spine は、

$$
\text{two channels}
\Rightarrow
\text{supportMass lower bound}
$$

だった。今回はそれが

$$
\text{finite family of channels}
\Rightarrow
\text{supportMass lower bound}
$$

へ一般化された。
ここで初めて、counting 的議論の器ができたと見てよい。

### 4.2. primitive flow family と support mass の有限集合導線

今回は `MassBridge` 側だけでなく、`ValuationFlowBridge` 側も同時に family 化したので、

$$
\text{primitive witness family}
\Rightarrow
\text{supportMass lower bound on diff}
$$

という有限集合レベルの導線も閉じた。
差分報告の言葉どおり、「同時に有限集合レベルの導線も最小形で入った」は、正しい評価じゃ。

---

## 5. 良い点

一番良いのは、**`Finset` を index に選んだこと** じゃ。
distinctness を別 predicate で持たずに済むので、statement が軽くなり、rad 的対象との相性も良い。これは設計判断としてかなり良い。

次に、family 版でも proof の筋が自然なこと。
前回の二本版では coprime を使っていたが、今回は support の部分集合として一括で処理している。family 版ならこの形が本筋じゃから、proof style も一般化にちゃんと対応しておる。

最後に、primitive flow 側の adapter が **最低限で済んでいる** ことじゃ。
witness packaging を大仰な structure にせず、まず `∀ q ∈ S, PrimitivePrimeFlowWitness ...` の形にとどめておる。今はこれで正しい。抽象化は後でもできるからの。

---

## 6. 留意点と弱点

### 6.1. `Finset` は multiplicity を忘れる

これは今回の目的には合っておるが、当然ながら

$$
\operatorname{rad}
$$

型の議論しかできぬ。
もし将来、同じ prime の重複出現や valuation の重み付き count を扱いたくなれば、`Finset` では足りぬ。じゃが現段階では radical 的 lower bound をやっているので、むしろ正しい選択じゃ。

### 6.2. witness family はまだ “生の関数” じゃ

いまは

$$
\forall q \in S,\ \text{PrimitivePrimeFlowWitness } q,a,b,d
$$

という形で family を渡しておる。
これは最小形としては良いが、今後何度も使うなら

* support set \(S\)
* witness assignment
* maybe nontrivial side conditions

をまとめた package structure を作る余地がある。差分報告の最後に「witness family の packaging をもう一段構造化」とあるが、それは確かに自然な次手じゃ。

### 6.3. public import をどうするかはまだ保留

ここも今は保留でよい。
family 版まで来たので、ここで公開導線を整えるのは悪くない。じゃが、もう一段だけ packaging を整理してから公開面を触るほうが、あとで import 再調整が少ない気もする。

---

## 7. 次の作業指示案 . Codex 追記向け

ここから先、わっちなら **witness family の packaging を一段だけ構造化** するほうを勧める。
public import もできるが、今は family API の重心を整えてからのほうが後腐れが少ない。

```md id="xuq6wo"
### レビュー追記案: 次の作業指示

1. 次段では public import 整備より先に、
   primitive witness family の packaging を一段だけ構造化する。

2. 目的は、
   `Finset` と witness assignment を毎回
   `∀ q ∈ S, PrimitivePrimeFlowWitness q a b d`
   の形で渡す代わりに、
   再利用しやすい小さな structure にまとめること。

3. 最小構造案は次のようにする。
   - support set `S : Finset ℕ`
   - witness assignment `witness : ∀ q ∈ S, PrimitivePrimeFlowWitness q a b d`
   まずはこの 2 フィールドだけでよい。
   distinctness は `Finset` 側に吸収する。

4. この package に対して、
   - `primeChannelFamily`
   - `supportMassLowerBound`
   の 2 本を method 的に再公開する薄い API を作る。
   theorem 本体の内容は今回の family 版補題の再包装だけでよい。

5. concrete example では、
   既存の `{7,13}` family を新しい package で包み直し、
   同じ lower bound が package 経由で読めることを確認する。

6. package 化が終わった後で、
   `ABC.Main` または `DkMath.ABC` 側への公開 import 導線を整える。
   そうすると public 側に露出する API がより安定する。
```

---

## 8. 最終判断

今回の差分は、**2-channel 版の lower bound を family 版へ持ち上げる一般化が、きれいに成功した回** じゃ。
しかもそれを `MassBridge` 側だけで終わらせず、`ValuationFlowBridge` 側でも primitive witness family から同じ lower bound へ流す導線を入れておる。ここがとても良い。

わっちの評価では、ここで lower-bound spine はかなり見通しがよくなった。
次は public import を急ぐより、family packaging を軽く整えるのがいちばん筋がよいと思うぞい。
