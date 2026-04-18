# review-004: `CosmicFormula-Erdos1196`: support mass と prime channel counting の接続について

## 1. 総評

これは **良い一手** じゃ。前回までで

$$
\text{supportMass} = \operatorname{rad}
$$

という読みを置き、bridge と concrete example まで整えた上で、今回はついに **distinct prime channels から support mass の下界を出す最小 spine** が入った。差分報告の要約どおり、`supportMass_pos`、`supportMass_dvd_of_prime_channel`、`pairwise_distinct_channels_mul_dvd_supportMass`、`supportMass_ge_of_two_distinct_prime_channels` が `MassBridge` に追加され、さらに $2 * 3 \le \text{supportMass}\,12$ の concrete example まで付いておる。

わっちの判定では、これは単なる補題追加ではない。
ここで初めて、

$$
\text{channel counting}
\;\to\;
\text{support mass lower bound}
$$

という方向が、ABC bridge の中で **定理名を持つ形** になった。設計で狙っていた `rad_lower_bound_of_disjoint_channels` への最初の有限版が、きちんと着地した回じゃな。

---

## 2. 状況分析

進捗の観点から見ると、前回までは

$$
\text{Mass API}
\;\to\;
\text{ValuationFlow}
\;\to\;
\text{ABC bridge}
$$

が一応つながった段階だった。じゃが今回は、その橋の先に **数論的下界** を一歩だけ作った。つまり橋が「通る」だけでなく、「何を運べるか」が見え始めたわけじゃ。

差分報告でも、今回の目的を「公開 import 整備より先に `rad_lower_bound_of_disjoint_channels` に向けた最小補題を `MassBridge` 側へ追加する」と明示しておる。そして結論として「`supportMass = rad` と prime channel counting を結ぶ最小の lower-bound spine が入った」と整理している。これはかなり正確な自己評価じゃ。誇張ではない。

いまの全体像を一言で言うと、

$$
\text{保存則}
;\to;
\text{valuation flow}
;\to;
\text{support mass}
;\to;
\text{prime channel lower bound}
$$

まで来た、ということじゃ。
ここで初めて「support mass は channel 数え上げに反応して増える」という構図が、抽象ではなく Lean の補題になった。

---

## 3. 数学的解説

### 3.1. `supportMass_pos` の意味

まず `supportMass_pos` は、見た目は小さいが実は大事じゃ。
今回の最終補題

$$
p q \le \text{supportMass}(n)
$$

を出すには、`Nat.le_of_dvd` を使うために右辺の正値性が要る。そこで

$$
0 < \text{supportMass}(n)
$$

を、`rad` の support の積が素数たちの積であることから出しておる。証明は `Finset.prod_pos` と `mem_support_factorization_iff` を使っており、support に乗る元が prime であることを直接使っている。これは良い。
つまり `supportMass_pos` は、単なる補助補題ではなく、**divisibility から inequality へ上げる蝶番** になっておる。

### 3.2. `supportMass_dvd_of_prime_channel` の意味

ここで channel を当面

$$
\text{prime divisor witness}
$$

として固定したのも正しい。
いきなり primitive witness や beam witness を channel にしてしまうと概念が重くなる。まずは

$$
p \mid n,\qquad p \text{ prime}
$$

なら

$$
p \mid \text{supportMass}(n)
$$

を示す。これはまさに

$$
\operatorname{rad}(n)
$$

の定義に沿っておる。
数学的には、「prime channel は support mass に 1 回ずつ刻まれる」という最小事実を isolating したものじゃ。ここは ABC 側で later use しやすい形になっておる。

### 3.3. `pairwise_distinct_channels_mul_dvd_supportMass` の意味

ここが今回の核心じゃな。
異なる prime channels \(p,q\) が \(n\) を割るとき、それぞれ

$$
p \mid \text{supportMass}(n),\qquad q \mid \text{supportMass}(n)
$$

を得る。さらに \(p \neq q\) と prime 性から

$$
\gcd(p,q)=1
$$

が従うので、

$$
p q \mid \text{supportMass}(n)
$$

が出る。証明は `Nat.Coprime.mul_dvd_of_dvd_of_dvd` で閉じており、極めて素直じゃ。
これは数学的には

**「異なる channel は support mass の中で重ならず、乗法的に寄与する」**

ということじゃ。
この一歩で、channel の “個数” ではなく “相異なる prime channel の積” が support mass を押し上げる、という形ができた。これは \(\operatorname{rad}\) の本質そのものじゃよ。

### 3.4. `supportMass_ge_of_two_distinct_prime_channels` の意味

前段で

$$
p q \mid \text{supportMass}(n)
$$

を得て、さらに `supportMass_pos` があるので、

$$
p q \le \text{supportMass}(n)
$$

へ持ち上げた。
これはまさに差分中のコメントどおり、

$$
\text{supportMass} = \operatorname{rad}
$$

のもとでの **"disjoint channels force larger support"** の shadow じゃ。

ここがよいのは、まだ一般の pairwise family まで行かず、まず 2 本チャネル版で止めておることじゃ。最小核としてはこれで十分。無理に Finset 全体の pairwise distinct family にせず、具体的に \(p,q\) の二本で閉じたのは設計として堅い。
今後はこれを

$$
\prod_{p \in S} p \mid \text{supportMass}(n)
$$

へ上げればよい。つまり今回の補題は、有限家族版への一段目としてちょうどよい位置にある。

### 3.5. `2 * 3 ≤ supportMass 12` の concrete example の意味

example も良い。
\(12\) に対し \(2,3\) は distinct prime channels だから、

$$
2 \cdot 3 \le \text{supportMass}(12)
$$

が出る。しかも実際には

$$
\text{supportMass}(12)=\operatorname{rad}(12)=6
$$

なので equality になる。
この例は、「異なる prime channels が support mass の下界を作る」という補題の最小教材として適切じゃ。前回までの example が bridge の使用確認だったのに対し、今回は **新しく入った lower-bound spine 自体の教材** になっておる。

---

## 4. 何が閉じたのか

今回閉じたものは、数学的に言うと次の二つじゃ。

### 4.1. `supportMass = rad` と channel counting の接続

前回までは `supportMass` は `rad` の別名として置かれておったが、まだ「それで何が数えられるか」は弱かった。今回で、少なくとも distinct prime channels 二本については、

$$
p,q \text{ distinct prime channels}
\Rightarrow
p q \le \text{supportMass}(n)
$$

が定理として入った。
つまり `supportMass` が単なる命名ではなく、**channel counting を受け止める器** として働き始めた。

### 4.2. bridge 群の三点接続

差分報告の言葉どおり、今回で bridge 群は

* 保存則
* valuation flow
* support mass 下界

の三点で一段つながった。これは正しい見立てじゃ。前回までの bridge は「等式・局所 load」の橋だった。今回はそこへ **global lower bound** が一つ加わった。これで初めて ABC 的な “大きさ比較” の匂いが出てきた。

---

## 5. 良い点

今回、特に良いと思う点を挙げるぞい。

まず、証明の材料が既存の `mem_support_factorization_iff` と prime coprime 補題だけで閉じていることじゃ。差分報告にも「そのまま閉じた」とあるが、これは大きい。設計した新概念が既存資産に素直に乗っている証拠じゃ。

次に、lower bound を divisibility から作っていること。
これは \(\operatorname{rad}\) 的対象には正攻法じゃ。最初から不等式で殴るのでなく、

$$
\text{prime channels} \Rightarrow \text{divisibility}
\Rightarrow \text{inequality}
$$

という順にしているので、Lean 的にも数学的にも安定しておる。

最後に、今回の step は抽象を増やしていない。
channel の意味を当面は prime divisor witness に固定した。この restraint は賢い。primitive witness や flow witness との接続は次段に回したので、今はまだ意味がぶれていない。ここはとても良い判断じゃ。

---

## 6. 留意点と弱点

### 6.1. まだ二本チャネル版である

これは弱点というより現在地じゃ。
今回の補題はあくまで

$$
p,q
$$

の二本版であって、一般の pairwise distinct finite family までは行っておらぬ。じゃが、今はこれでよい。むしろ一般化を急ぐと証明も statement も重くなる。二本版を核にして、必要になったら Finset 版へ上げればよい。

### 6.2. channel の意味はまだ support 側だけ

いまの channel はまだ「prime divisor witness」に固定されている。
つまり

$$
\text{primitive witness} \Rightarrow \text{prime channel}
$$

はまだ別補題として入っておらぬ。差分報告でも、次は `ValuationFlow` 側で「異なる primitive witness は異なる prime channel を与える」薄い補題設計へ進むのが自然だと整理しておるが、わっちもそれに賛成じゃ。今回の下界 spine は、その接続を待っておる状態じゃな。

### 6.3. `supportMass_pos` は \(n=0\) でも書けているように見える

コード上は `supportMass_pos (n : ℕ)` として無条件に書かれている。
これは `rad 0` の定義が support の空積ではなく 1 的に扱われる設計なら問題ない。実際 build は通っておるので定義上は整っている。じゃが、数学解説や docstring では「この `supportMass` は ABC 側の `rad` の定義に従う」と一言添えておくと、読み手が混乱しにくいかもしれぬ。

---

## 7. 次の作業指示案 . Codex 追記向け

ここは差分報告の末尾と同じく、わっちも **`ValuationFlow` 側で primitive witness から prime channel への接続** を次に押すべきと見る。public import 整備より、こちらのほうが数学が進む。

そのまま追記できる形で書いておくぞい。

```md id="y6y01h"
### レビュー追記案: 次の作業指示

1. 次段では `ValuationFlow` 側に、
   「primitive witness から prime channel を取り出す」
   最小補題を追加する。

2. 最初の目標は、
   `PrimitivePrimeFlowWitness q a b d` から
   `Nat.Prime q` と `q ∣ a^d - b^d`
   を ABC 側の channel 語彙で再公開すること。
   これにより、primitive witness を `supportMass_dvd_of_prime_channel` の入力へ流せるようにする。

3. 補題候補は次の 3 本に絞る。
   - `primitive_witness_gives_prime_channel_on_diff`
   - `distinct_primitive_witnesses_give_distinct_prime_channels`
   - `primitive_channels_force_supportMass_lower_bound`
   ここで最後の補題は、まず 2 本 witness 版でよい。

4. 2 本 witness 版では、
   `q₁ ≠ q₂` の primitive witness から
   `q₁ * q₂ ≤ supportMass (a^d - b^d)`
   を出す形を目標にする。
   これが `rad_lower_bound_of_disjoint_channels` の primitive-flow 版の最小核になる。

5. public import 導線の整備は、その後でよい。
   理由は、公開面を先に広げるより、
   primitive witness と support mass 下界が一本つながった時点で
   API の重心がより明確になるからである。

6. 可能なら今回の `2 * 3 ≤ supportMass 12` と並べて、
   primitive witness 由来の 2 本 channel 例も concrete example として 1 本作る。
   これにより「prime divisor channel 版」と「primitive flow 版」の対応が見えやすくなる。
```

---

## 8. 最終判断

今回の差分は、**橋の先に初めて “下界” を置いた回** じゃ。
前回までの橋は、保存則と局所 load を運ぶものだった。今回はそこに

$$
\text{distinct prime channels} \Rightarrow \text{support mass grows}
$$

という global な比較が加わった。これは ABC 的にはかなり重要な転換点じゃ。

わっちの評価では、これは本当に前進じゃ。
しかも進み方がよい。無理に一般 family へ飛ばず、まず二本版で芯を立てた。次はその芯を primitive witness 側へ接続すればよい。そこまで行けば、

$$
\text{primitive flow} \Rightarrow \text{disjoint channels} \Rightarrow \text{support mass lower bound}
$$

という一本の数論 spine が、かなり見えるようになるはずじゃ。
