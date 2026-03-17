# Samples/LPS ドキュメント (Review: 2026/03/17 21:28)

## LPS予想の考察実験場

cid: 69b94466-6630-83aa-8773-0684c02cf16d
cdt: 2026-03-17 12:09:15
udt: 2026-03-17 12:16:02

> 🐺賢狼:

かなり見えてきたぞい。`Samples/LPS` は **LPS 予想を直接証明する本丸** ではなく、
**「同じ Big を保ったまま内部の分解と充填性がどう変わるか」** を観測する実験塔として組まれておる。
とくに `216, 64, 125` あたりの標本が、かなり意図的じゃ。

> 🐺賢狼:

## 1. 結論

`lean/dk_math/DkMath/Samples/LPS` は、 **古典的 LPS 予想そのものを正面から定式化して証明するモジュール** ではない。
むしろ、

\[
\text{Big} \;=\; \text{Core} + \text{Beam} + \text{Gap}
\]

という分解を土台にして、 **「同じ完成値 Big に対し、内部の差分 residual が何個の \(d\) 乗和で埋まるか」** を観測するための実験層じゃ。設計書でも、一般理論をいきなり閉じるのでなく、 **戻り道を確保する局所核** を Lean に固定するのが狙いと明言されておる。 fileciteturn2file0

## 2. `Samples/LPS` 全体の役目

設計書にあるとおり、このディレクトリの主役は次の 8 本じゃ。

`BigFamily / BigFamilyInt / PowerSwap / GapFillRank / BigFamilyExamples / Exchange / PowerSwapBranch / GapContours`

そして役割分担はかなり明快で、
`BigFamily` が分解の骨格、
`GapFillRank` が「何項で埋まるか」の観測器、
`PowerSwap` と `PowerSwapBranch` が \(a^b=b^a\) の離散・連続の橋、
`GapContours` がその等高線幾何、
`BigFamilyExamples` が concrete な標本群、という並びになっておる。 fileciteturn3file4

この時点で、賢狼の見立てでは LPS という看板の中身は

\[
\text{equal sums of like powers}
\]

をいきなり一般形で殴るのでなく、
**差分・残差・充填最小項数のプロファイル** を先に掴む方式じゃな。たわけた特攻ではなく、かなり慎重な足場固めじゃ。

## 3. `BigFamily.lean` と `BigFamilyInt.lean`

ここが土台じゃ。

自然数版 `BigFamily.lean` では

\[
\mathrm{big}(d,x,u)=(x+u)^d,\quad
\mathrm{gap}(d,x,u)=u^d,\quad
\mathrm{body}=\mathrm{big}-\mathrm{gap},\quad
\mathrm{core}=x^d,\quad
\mathrm{beam}=\mathrm{body}-\mathrm{core}
\]

を定義しておる。
そのうえで、

\[
\mathrm{big}=\mathrm{body}+\mathrm{gap},\qquad
\mathrm{body}=\mathrm{core}+\mathrm{beam},\qquad
\mathrm{big}=\mathrm{core}+\mathrm{beam}+\mathrm{gap}
\]

という分解を定理化しておる。これは設計書の **確定層** と一致する。 fileciteturn3file4

ただし `Nat` では減算が切り捨てを起こす。ゆえに `core ≤ body` のような仮定が要る場面が出る。そこで `BigFamilyInt.lean` が重要になる。こちらは `ℤ` 上で同じ分解を作るので、`body + gap = big` や `beam + core = body` を **仮定なしで** 戻せる。設計書も「差分観測は可能なら `BigFamilyInt` 側で扱う」と注意しておる。 fileciteturn3file2

ここ、実装の筋がよい。
`Nat` で見たい量と `ℤ` で扱うべき差分を分けておるので、後で証明がぬかるみに沈みにくい。

## 4. `GapFillRank.lean`

ここでは LPS 的な「何個の \(d\) 乗項で書けるか」を、まず最小限の述語として置いておる。

核は

\[
\texttt{FillableByPowSumExact}\; d\, n\, r
\]

で、これは「\(n\) がちょうど \(r\) 個の \(d\) 乗和で表せる」という意味じゃ。
さらに

\[
\texttt{FillableByPowSumLE}
\]

で「高々 \(r\) 個」も定義しておる。設計書でも、この観測述語が `GapFillRank` の中心として挙げられておる。 fileciteturn3file4

実例としては、

\[
16=4^2,\qquad
25=3^2+4^2,\qquad
216=6^3,\qquad
216=3^3+4^3+5^3
\]

を Lean で固定しておる。
とくに

\[
3^3+4^3+5^3=6^3
\]

は、この塔の顔じゃな。LPS の香りがむんむんする古典標本で、`same Big` に対して複数の filling があることを示す入口になっておる。

さらに

\[
\texttt{fillable\_exact\_of\_exact\_le}
\]

で、\(k\) 項表示があれば 0 を足して \(r\) 項表示へ延長できることも押さえておる。これは地味じゃが、観測用 API としては大事な梁じゃ。

## 5. `PowerSwap.lean` と `Exchange.lean`

### 5.1. `PowerSwap.lean`

これは離散版の

\[
a^b=b^a
\]

を `PowerSwap a b` として定義したもの。
`(2,4)` と `(4,2)` の古典例、対称性、`PowerSwap a 1` なら \(a=1\) まで置いておる。
設計書でもこれは「離散標本、対称性、基本例」と整理されておる。 fileciteturn3file4

### 5.2. `Exchange.lean`

こやつは実に重要で、

\[
A=a^t \Rightarrow A^m=a^{tm}
\]

を `exchange_condition_minimal_nat` / `exchange_condition_minimal_int` として固定しておる。
設計書でも、これは **粗視化↔微視化交換の最小核** とされておる。 fileciteturn2file0

つまり、`4^2 = 2^4` や `27^2 = 3^6` を、単なる数合わせでなく、

- 粗い基底 \(A\)
- 細かい基底 \(a\)
- 束数 \(t\)
- 観測次数 \(m\)

の交換として読む枠組みじゃ。
この見方は LPS の「左辺何項、右辺何項」問題を、指数の束ね方・ほどき方の問題へ横滑りさせる。なかなか狡猾で面白い。

## 6. `PowerSwapBranch.lean`

ここは連続世界じゃ。
正実数 branch として

\[
x(t)=t^{1/(t-1)},\qquad
y(t)=t^{t/(t-1)},\qquad t>0,\ t\neq 1
\]

を定義しておる。設計書でも、これが `PowerSwapBranch` の核とされておる。 fileciteturn2file0

実装上の見どころは 3 つある。

第一に、

\[
x(t)=\exp\!\left(\frac{\log t}{t-1}\right),\qquad
y(t)=\exp\!\left(\frac{t\log t}{t-1}\right)
\]

へ書き換える補題をまず立てておる。
これで `Real.rpow` の癖を `exp/log` へ押し込める。

第二に、`t → 1` の極限をちゃんと証明しておることじゃ。
`HasDerivAt Real.log 1 1` から slope の極限を使って

\[
\frac{\log t}{t-1}\to 1,\qquad
\frac{t\log t}{t-1}\to 1
\]

を出し、そこから

\[
(x(t),y(t))\to (e,e)
\]

を示しておる。これはただの気分ではない。Lean 上でちゃんと微分の道具を使っておる。

第三に、branch 上で

\[
y(t)=t\,x(t)
\]

を出し、それを踏み台に

\[
x(t)^{y(t)}=y(t)^{x(t)}
\]

を一般 \(t\) で証明しておる。
つまりここは、`(2,4)` の離散例を連続曲線へ持ち上げ、その中心が `(e,e)` であることまで固定した層じゃ。設計書でも `(2,4),(4,2)` と `(e,e)` の幾何が中核扱いになっておる。 fileciteturn3file5

## 7. `GapContours.lean`

ここは `PowerSwapBranch` の幾何化じゃ。

定義は

\[
U=y\log x,\qquad V=x\log y,
\qquad p=\frac{U+V}{2},\qquad q=U-V
\]

で、さらに

\[
F(x,y)=x^y-y^x
\]

を置く。これは設計書どおりじゃ。 fileciteturn3file5

実装ではつぎを押さえておる。

\[
F=e^U-e^V
\]

\[
F=2e^p\sinh\!\left(\frac q2\right)
\]

\[
q=xy\left(\frac{\log x}{x}-\frac{\log y}{y}\right)
\]

最後の式は、設計書で `gapQ_eq_xy_mul_Hdiff` として明示されておる重点補題じゃ。 fileciteturn3file6

さらに `(e,e)` で

\[
q=0,\qquad F(e,e)=0
\]

を示し、局所モデル候補として

\[
v^2-u^2
\]

型の二次主部 `gapQuadraticModel` を置いておる。
留意点として、ここは **候補モデルの固定** まではしておるが、「真の二次展開を完全証明した」わけではない。設計書でも、この近傍二次近似は後回し扱いじゃ。 fileciteturn3file2

## 8. `BigFamilyExamples.lean` がいちばん LPS らしい

ここが実験塔の中心じゃ。

### 8.1. 何を観測しているか

`ObservedMinOne d n` を「1 項で埋まる」、
`ObservedMinTwo d n` を「1 項では埋まらず、2 項で埋まる」として置いておる。

つまり完全な `FillRank` をまだ一般定義しておらず、
**観測上の最小項数が 1 か 2 か** を見る、軽量 API じゃ。これも設計書の方針どおり。 fileciteturn3file6

### 8.2. 主標本

立方では 3 組、平方では 1 組が入っておる。

\[
216 \to 91/64,\qquad
64 \to 35/27,\qquad
125 \to 65/64
\]

そして平方版は

\[
25 \to 13/9
\]

じゃ。これらは設計書でも固定済み標本として列挙されておる。 fileciteturn2file0

実際の中身はこうじゃ。

\[
216-125=91=3^3+4^3,\quad 91 \text{ は 1 個の立方ではない}
\]

\[
216-152=64=4^3
\]

ゆえに、 **同じ Big = 216** でも Body の選び方で residual の observed minimum が

- 2 項必要
- 1 項で足りる

に分かれる。

同様に

\[
25-12=13=2^2+3^2,\quad 13 \text{ は平方 1 項でない}
\]

\[
25-16=9=3^2
\]

や、

\[
64-29=35=2^3+3^3,\qquad 64-37=27=3^3
\]

\[
125-60=65=1^3+4^3,\qquad 125-61=64=4^3
\]

も用意されておる。

この「same Big, different observed minimum profile」が、`BigFamilyExamples` の真の主題じゃ。設計書でもそのように位置づけられておる。 fileciteturn3file4

### 8.3. 総括定理

それを束ねたのが

```lean
cube_observed_min_split_reproduced_three_samples
```

で、立方次数 \(d=3\) について、この profile 分岐が 3 標本で再現することをまとめておる。設計書でもこれが総括定理として掲げられておる。 fileciteturn2file0

## 9. これを LPS 予想としてどう読むか

ここが肝じゃな。

古典的 LPS は「同じ \(k\) 乗和の等式」で、非自明解の最小項数や存在を問う方向の話じゃ。
このコードはまだ、その全体命題を `def` して一般指数で攻めてはおらぬ。

代わりに、次のような **局所観測問題** に落としておる。

\[
\text{fixed Big} - \text{chosen Body} = \text{residual}
\]

この residual が

- 1 個の \(d\) 乗で埋まるか
- 2 個で初めて埋まるか
- 3 個必要か

を調べる。
つまり LPS の巨大な森を、まず **residual の fillability landscape** に分解して地図を描いておるわけじゃ。

これは賢いやり方じゃよ。
いきなり「一般 \(k\) で不可能」などと息巻くと、だいたい泥沼で足を取られる。
まず小さい concrete な residual たちに、1 項型の rigid 島と 2 項型の diffuse 島がどう現れるかを見る。設計書でも profile 地形仮説として、その見方が明示されておる。 fileciteturn2file0

## 10. いまの到達点と、まだ無いもの

### あるもの

- Big/Body/Gap/Core/Beam の骨格
- `ℤ` 版差分観測
- \(a^b=b^a\) の離散・連続 branch
- `(e,e)` を中心とする等高線座標
- exact / at-most \(d\) 乗和充填の述語
- same Big における observed minimum profile 分岐の concrete 標本

### まだ無いもの

- 古典 LPS 命題そのものの一般定義
- 一般 \(d\) に対する完全な最小項数 `FillRank`
- observed minimum の一般理論
- Big/Body の選び方と profile 分岐を結ぶ必要十分条件
- `GapContours` の二次近似の完全証明
- これらを FLT や一般 equal-sum-of-like-powers の impossibility theorem へ押し上げる本丸

つまり、 **実験塔としては筋が通っておるが、まだ“定理の城”ではない**。
されど、基礎梁はちゃんと組まれておる。変に背伸びしたハリボテではないのがよい。

## 11. 賢狼の総評

この `Samples/LPS` をひと言で言うなら、

**「LPS 予想の周辺を、Big 固定・residual 観測・PowerSwap 幾何で分解している研究用サンドボックス」**

じゃな。 fileciteturn3file2

とくによい点は 3 つ。

第一に、自然数の切り捨て減算を嫌って `BigFamilyInt` を別に立てたこと。
第二に、`PowerSwap` を離散例で止めず、branch と `(e,e)` 幾何まで伸ばしたこと。
第三に、`same Big` で profile が分岐する標本を複数本押さえ、単なる一発芸で終わっておらぬこと。

逆に留意点は、LPS の名に引っ張られて「もう一般理論がある」と見誤ると危ういところじゃ。
現状はまだ **観測枠の整備** が主で、一般定理はこれから。そこを曖昧にすると、数学が急に霧になる。霧は狼でも噛めぬのでな。

次にやるなら、`BigFamilyExamples` の標本を **統一 schema** に書き直し、
`ObservedMinOne/Two` を `GapFillRank.lean` へ昇格できる形へ整理するのが、いちばん筋が良い。
