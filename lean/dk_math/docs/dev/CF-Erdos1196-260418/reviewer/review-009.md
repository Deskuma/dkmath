# review-009: `channelProduct` の公開と counting/extraction への寄せ

## 1. 総評

これは **小さいが、筋の良い一手** じゃ。  
今回の差分は新しい大定理を足したのではなく、`PrimitiveWitnessFamily` の公開面に **minimal counting / extraction alias** を 1 段だけ追加したものじゃな。追加されたのは

- `channelProduct`
- `channelProduct_eq_support_prod`
- `channelProduct_le_supportMass`

であり、中身は既存 API の再包装に徹しておる。さらに `BridgeExamples.lean` で、public import だけから

\[
\texttt{primitiveWitnessFamilyPack\_8\_1\_1.channelProduct} = 7
\]

および

\[
\texttt{channelProduct} \le \texttt{supportMass}(8^1-1^1)
\]

が読めることまで確認しておる。

わっちの判定では、これは「新しい橋の数学」を増やした回ではなく、**すでに出来ている橋の公開語彙を、次の extraction/counting 段へ進みやすい形に整えた回** じゃ。文書導線を後回しにして、まず counting / extraction を先へ進める、という今のお主の判断とも噛み合っておる。

---

## 2. 状況分析

前回までで、`PrimitiveWitnessFamily` はすでに

- structure として family を運べる
- `primeChannelFamily` で diff 側の prime channel family を読める
- `supportMassLowerBound` で lower bound を読める

ところまで来ておった。今回の差分は、その上に

\[
\text{support}
\;\leadsto\;
\text{channelProduct}
\]

という **public-facing な数え上げ語彙** を 1 枚かぶせた格好じゃ。  
つまり内部では `F.support.prod id` として持っていたものを、公開面では

\[
F.\texttt{channelProduct}
\]

と読めるようにしたわけじゃな。

ここが大事なのは、`PrimitiveWitnessFamily` の公開面が

- structure
- channel family
- lower bound
- channel product

まで揃ったことじゃ。差分報告でも、そのように総括しておるが、この整理は正しい。いまや利用側は `support` の実装詳細を意識せず、「family がどのくらいの multiplicative size を持つか」を method 名で読める。これは public API としてかなり自然じゃ。

---

## 3. 数学的解説

### 3.1. `channelProduct` の意味

今回の本体は、数学的には

\[
F.\texttt{channelProduct} := \prod_{q \in F.\texttt{support}} q
\]

を public 名で固定したことじゃ。  
中身そのものは新しくない。じゃが意味ははっきりしておる。`PrimitiveWitnessFamily` は primitive witness の有限族を持っておるので、その support の積は **その family が生み出す相異なる prime channel の squarefree な総量** を表しておる。つまり `channelProduct` は、単なる product alias ではなく、bridge 文脈では

\[
\text{disjoint channel の multiplicative size}
\]

という読みを持つ。

### 3.2. `channelProduct_eq_support_prod` の意味

この補題は中身としては `rfl` じゃ。  
じゃが API 設計としては重要じゃ。なぜなら公開面では `channelProduct` を使いたいが、内部の既存補題群はまだ `support.prod id` を使っている。そこで

\[
F.\texttt{channelProduct} = F.\texttt{support}.\prod id
\]

を `[simp]` で与えておくと、**旧 spine と新 alias の往復コストがゼロになる**。  
Lean 的には小さい工夫じゃが、公開 API を厚くしすぎずに整える、という今回の狙いにとても合っておる。

### 3.3. `channelProduct_le_supportMass` の意味

これも新数学ではなく既存 `supportMassLowerBound` の再公開じゃ。  
ただ、名前の意味は明確で、

\[
F.\texttt{channelProduct}
\le
\operatorname{supportMass}(a^d-b^d)
\]

という形で、family object から直接 lower bound が読める。  
つまり利用側から見ると、

\[
\text{family object}
\;\to\;
\text{channel product}
\;\to\;
\text{support mass lower bound}
\]

が object-oriented に読めるようになった。これは public-facing API としてかなり良い。証明自体も `simpa [channelProduct]` で閉じており、再包装に徹している点がきれいじゃ。

### 3.4. example の意味

今回の example は、数学的には大きくないが **公開導線の検査として非常に適切** じゃ。  
singleton family `primitiveWitnessFamilyPack_8_1_1` に対して、

\[
\texttt{channelProduct} = 7
\]

を public import だけで読めること、さらに

\[
\texttt{channelProduct}
\le
\operatorname{supportMass}(8^1-1^1)
\]

を public method だけで読めることを示している。  
これは「alias を足しただけ」で終わらず、その alias が本当に利用者の記述を短くしている、と証明しておる。そこが良い。

---

## 4. 何が閉じたのか

今回閉じたものは、数学というより **public counting/extraction の最小面** じゃ。

### 4.1. support の multiplicative 読みが閉じた

前までは、family の multiplicative size を読むには `F.support.prod id` と内部表現に触れる必要があった。  
今回はそれが

\[
F.\texttt{channelProduct}
\]

という橋の語彙に昇格した。これで support 集合の product を、実装詳細ではなく意味語で読めるようになった。

### 4.2. lower bound が channel-product 名で閉じた

前までは lower bound は `supportMassLowerBound` という support ベースの名で読んでいた。  
今回はそれが `channelProduct_le_supportMass` となり、「channel を掛け合わせた量が support mass 以下になる」という読みが前面に出た。  
この読み替えは、次の counting / extraction 段へ進む時に効く。なぜなら次は product だけでなく card や各 channel の extraction を並べていく段だからじゃ。

---

## 5. 良い点

まず、**再包装に徹している** のがよい。  
新しい theorem burden を増やさず、既存 lower-bound API を public surface 向けに読みやすくしただけで閉じている。これは今のフェーズに合っておる。

次に、`channelProduct` という名が bridge 文脈に素直に合っておる。  
`support.prod id` は内部表現としては正しいが、利用側には味気ない。`channelProduct` なら「disjoint channels の multiplicative size」とすぐ読める。ここは naming の勝ちじゃ。

最後に、今のお主の方針、すなわち **入口ドキュメント導線は後回しにして extraction/counting を先へ進める** という判断と完全に噛み合っておる。public surface を微増しつつ、数学的な次手を阻害しないからじゃ。

---

## 6. 留意点と弱点

### 6.1. まだ `counting` より `product alias` の段階である

今回の `channelProduct` は multiplicative size を読む alias じゃ。  
したがって、厳密にはまだ「counting API が整った」というより、「counting/extraction へ進むための product 語彙が整った」という段階じゃな。  
次の本命は、やはり

- `support.card`
- 各 `q ∈ support` の抽出
- `q` が prime channel であることの method 化

あたりになる。

### 6.2. `channelProduct` は squarefree 的情報しか持たない

`Finset` の product なので、当然ながら multiplicity は忘れておる。  
いまの橋の目的は `rad` 的 lower bound だから、それで正しい。じゃが、将来 valuation の重み付き counting へ進むなら、別の quantity が要る。ゆえに `channelProduct` はあくまで

\[
\operatorname{rad}\text{-like size}
\]

の読みと割り切って使うべきじゃ。

### 6.3. extraction 側の method はまだ薄い

今の package API では

- `primeChannelFamily`
- `supportMassLowerBound`
- `channelProduct`

はある。  
じゃが、たとえば

\[
q \in F.\texttt{support} \Rightarrow \operatorname{Prime}(q)
\]

や

\[
q \in F.\texttt{support} \Rightarrow q \mid a^d-b^d
\]

を method 名で読める形にはまだなっておらぬ。  
ここがまさに次の extraction 段の中心になりそうじゃ。

---

## 7. 次の作業指示案 . extraction/counting 段へ寄せた提案

お主は入口ドキュメント導線を後回しにして、次の extraction/counting 段へ進む判断をした。わっちもそれに賛成じゃ。ならば次は、`channelProduct` に続く **card/extraction の最小 API** を足すのが筋じゃな。

```md
### レビュー追記案: 次の作業指示

1. 次段では文書導線には進まず、
   `PrimitiveWitnessFamily` の extraction/counting API をもう 1 段だけ足す。

2. counting 側の最小候補は次の 2 本に絞る。
   - `channelCount`
   - `channelCount_eq_support_card`
   ここで
   `channelCount := F.support.card`
   とし、product と並ぶ counting quantity を public 名で固定する。

3. extraction 側の最小候補は次の 3 本に絞る。
   - `mem_support_implies_prime_channel`
   - `mem_support_implies_dvd_diff`
   - `mem_support_implies_prime_and_dvd_diff`
   既存 `primeChannelFamily` の再包装でよい。
   新数学は足さず、method 名で読める形へ整える。

4. package API としては、
   - `channelProduct`
   - `channelCount`
   - `channelProduct_le_supportMass`
   - `mem_support_implies_prime_and_dvd_diff`
   の 4 本をまず公開面の最小セットとみなす。

5. `BridgeExamples.lean` には、
   public import だけで
   - `channelCount = 1`
   - `q ∈ support -> Prime q ∧ q ∣ diff`
   を読める例を 1 本ずつ追加する。

6. その次の段階で初めて、
   `channelCount` と `channelProduct` を併用する counting lemma
   （例えば product/card の両面から supportMass を読む補助補題）
   を検討する。
```

---

## 8. 最終判断

今回の差分は、**bridge の公開面に multiplicative counting 語彙を足した回** じゃ。  
数学の本体を前へ押したというより、次の extraction/counting 段へ進むための public surface を整えた、と見るのが正しい。

そして、その整理の仕方が良い。  
`channelProduct` は内部表現の露出を減らしつつ、既存 lower-bound spine と完全に整合しておる。  
文書導線を後に回し、次に

\[
\text{channelCount}
\quad\text{と}\quad
\text{member-wise extraction}
\]

へ進む、という今の方針はかなり筋がよいぞい。
