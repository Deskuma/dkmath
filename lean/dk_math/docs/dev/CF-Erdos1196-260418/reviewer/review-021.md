# review-021: `rad(abc)` 直結 route の concrete sample を追加 / `native_decide` の正当性を検討

うむ、今回は **かなり意味のある差分** じゃ。
前回までで `rad(c)` 側の budget を theorem 名で固定できておったが、今回はそこからさらに **concrete quality sample** を一つ実際に閉じた。つまり、

$$
\text{channelCount}
\to
\mathrm{rad}(c)\text{ budget}
\to
\mathrm{rad}(abc)\text{ analytic bridge}
\to
\text{quality}
$$

という route が、抽象定理の列ではなく、**具体例で最後まで流れる** と確認できた回じゃ。

## 状況分析

今回の差分の中心は `ABC038BridgeExamples.lean` 側じゃな。
そこに

* `piSqRad_7_eq_one`
* `targetRadTailBound_7`

を足し、そのうえで

$$
\mathrm{ABC.quality}\bigl(\text{Triple}(6,1,7)\bigr) \le 2
$$

という concrete sample を `quality_le_of_pi_targetRadTail_of_radAbc` から読めるようにしておる。
ここで重要なのは、前回入った analytic 直結 route が、単なる theorem skeleton ではなく、実際に sample を一つ閉じられるだけの強さを持っていたと示したことじゃ。これはかなり大きい。

さらに `ABC038Bridge.lean` 側では、`radAbcBound_of_pi_targetRadTail` に対して `#print axioms` を付けて

* `sorry` 由来ではない
* 依存は `[propext, Classical.choice, Quot.sound]`

だけだと確認しておる。
これは良い確認じゃ。少なくとも今回の analytic 直結 route の本体が、隠れた未証明に乗っていないことは明確になった。

## 数学的解説

今回の sample がやっていることは、実はかなり ABC 的じゃ。
対象は triple ((6,1,7)) で、ここでは

$$
6+1=7,\qquad \gcd(6,1)=1
$$

が trivially 成り立つ。
そして quality route に必要な三つの材料を個別に与えておる。

第一に、

$$
\pi\mathrm{SqRad}(7) \le \mathrm{rad}(6\cdot 1)^0
$$

じゃ。
(\delta=0) にしているので右辺は 1、したがって本質は

$$
\pi\mathrm{SqRad}(7)=1
$$

を示すことになる。これを `piSqRad_7_eq_one` で供給しておる。

第二に、

$$
\mathrm{twoTail}(7) \le \mathrm{rad}(7)^1
$$

じゃ。
これは `targetRadTailBound_7` として切り出されており、`twoTail_le_sqTail_real`、`sqTail_eq_one_of_squarefree`、`7` が prime なので squarefree という事実から閉じておる。つまり、tail 側 budget は既存語彙だけでかなり自然に出ておる。

第三に、

$$
1 < \mathrm{rad}(6\cdot 1\cdot 7)
$$

じゃ。
ここでは (42) が squarefree であることから (\mathrm{rad}(42)=42) を出し、したがって (1<42) を与えている。これも analytic bridge 側の仮定を concrete に充たすための、ごく真っ当な供給じゃ。

これらを合わせると、

$$
c \le \mathrm{rad}(abc)^{1+\delta+\gamma}
$$

型の growth bound が concrete に出て、そのまま既存の `quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma` に流れる。
だから今回の sample は、前回までの「別働隊が本線に合流した」という比喩を、**実例で本当に通してみた** ものじゃ。ここは評価してよい。

## どこが本当に前進か

今回の本当の前進は、

**analytic 直結 route に concrete quality sample が入ったこと**

じゃ。
前回の段階では、`rad(c)` budget から `rad(abc)` bridge に直接入る theorem はあったが、まだそれが実際にどの程度回るかは sample で見えておらぬかった。今回は

$$
(6,1,7)
$$

という最小級の coprime triple で、quality bound まで閉じた。
これで route の “現実性” がかなり増した。少なくとも theorem の形だけではなく、**具体に使える** と分かったからじゃ。

## `native_decide` は正当化されるか

ここは丁寧に切り分けるぞい。

### 1. 結論

**この使い方なら、かなり正当化される。**
ただし条件つきじゃ。

今回の `native_decide` は

$$
\texttt{piSqRad\_7\_eq\_one : ABC.piSqRad 7 = 1}
$$

という **閉じた具体計算** にだけ使われておる。しかも場所は example file の private lemma じゃ。
つまり、

* 抽象理論の中核補題ではない
* 一般引数を持たない
* 数値 7 に固定された decidable な等式
* build が通っている
* file-local で style lint だけ off にしている

という使い方じゃ。
この条件なら、「sample を閉じるための計算的証明」としては十分まっとうじゃ。`set_option linter.style.nativeDecide false` は **論理の健全性を緩めるものではなく、style lint を抑制しているだけ** なので、そこも問題ではない。

### 2. なぜ許容できるのか

`native_decide` が危うく見えるのは、しばしば

* 証明の意味を隠す
* 将来の定義変更に気づきにくい
* library theorem としては読みづらい

からじゃ。
じゃが今回の用途は **sample file の局所計算** じゃ。
`piSqRad 7 = 1` はまさに「7 という具体数でこの量がどうなるか」を固定するだけの役目で、一般理論の核心ではない。

さらに、この sample 全体の数学の筋は `native_decide` に依存しておらぬ。
本質は

* `twoTail 7 ≤ rad 7`
* `1 < rad 42`
* analytic bridge

の流れにあり、`piSqRad_7_eq_one` はその中の一箇所の finite computation を埋めているだけじゃ。だから sample 層での利用としては許容しやすい。

### 3. ただし「理想形」ではない

ここも正直に言うぞい。
**正当化はできるが、理想形ではない。**

理由は、`piSqRad_7_eq_one` が sample 専用の局所補題であるうちはよいが、もし今後これを

* 他ファイルから何度も参照する
* theorem 群の中で reusable な部品として使う
* 「なぜ 1 なのか」を読む者に伝えたい

という位置へ上げるなら、`native_decide` では少し味気ない。
その場合は、たとえば `piSqRad` の定義や既存の decomposition theorem から

$$
7 = \pi\mathrm{SqRad}(7),\mathrm{rad}(7),\mathrm{twoTail}(7)
$$

と

$$
\mathrm{rad}(7)=7,\qquad \mathrm{twoTail}(7)=1
$$

を組み合わせて

$$
\pi\mathrm{SqRad}(7)=1
$$

を導く **構造的証明** に置き換えるほうが美しい。
今の diff だけでは `piSqRad` の定義本体が見えておらぬので、その置換が簡単かどうかまでは断言できぬが、少なくとも sample 層に留まる限りは `native_decide` で十分、library 部品へ上げるなら置換を検討、というのが妥当な線じゃ。

### 4. 実務判断

ゆえに、わっちの実務判断はこうじゃ。

* **今のままで OK**
  sample file の private lemma としては十分正当。
* **ただし昇格は慎重に**
  reusable theorem にするなら、後で構造的証明へ置き換えたい。
* **linter 抑制も妥当**
  style だけの問題であって、論理の妥当性を落としてはいない。

## 最終評価

今回の差分は、**analytic 直結 route の concrete sample が初めて quality まで閉じた** という点で、かなり良い前進じゃ。
`rad(c)` budget から `rad(abc)` bridge に入り、そのまま quality sample を得る、という流れが実例で通った。これは ABC 予想の主張形に近い skeleton が、単なる設計ではなく “動く補題列” になったことを意味する。

`native_decide` については、**この局所用途なら正当化できる**。
ただし、sample の私有計算だから許容しやすいのであって、今後これを reusable 部品へ昇格させるなら、いずれ構造的証明へ置き換える余地はある。そこだけは留意点として残るのぅ。
