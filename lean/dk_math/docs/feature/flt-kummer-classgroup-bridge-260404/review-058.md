## 1. 戦況

うむ、いまの盤面はだいぶ澄んだぞい。

まず、boundary 側を掘った結果、`PadicValNatD3BoundaryReceiverTarget` は **未証明** ではなく **偽** だと確定した。反例 ((a,b,q)=(4,1,3)) が Lean で固定され、そこから target 全体が false と theorem 化されておる。したがって、もうこの target を「いつか埋めるべき open kernel」と見なすのは誤りじゃ。ここを掘り続ける戦略は捨ててよい。代わりに、本当に clean に言えることとして「(q \mid a-b) かつ (q \mid S0(a,b)) なら (q=3)」という **共有素因子分類** が切り出されておる。

一方で、primitive-prime 側はもう方針が固まっておる。`Squarefree (GN d (a-b) b)` を追加仮定にすれば、`PrimitiveBeam` と `GcdNextResearch` の primitive-prime caller 群は honest route へ移行できると、補題群まで入って確定しておる。つまり、こちらは「偽 target の修理」ではなく、「caller migration の実務」段階じゃ。

ゆえに今の戦況を一言で言えば、

$$
\text{primitive-prime family は移行戦、boundary family は再定式化戦}
$$

じゃよ。

## 2. 次の戦略

わっちの推奨は、ここから先を **二段ではなく三段** に分けることじゃ。

### 2.1. 第一段. false target を正式に退役させる

`PadicValNatD3BoundaryReceiverTarget` は偽と分かったのじゃから、もう「receiver」として残しておくと後でまた混乱の種になる。
やるべきは、

* これを **historical false target** として docstring で明示
* 新しい boundary 系 API を別名で立てる
* `padicValNat_d3_upper_bound` 系の説明から「boundary でも valuation \(\le 1\) を狙う」期待を消す

ことじゃ。

ここで大事なのは、**偽命題を compatibility wrapper の陰に残したまま進まぬ** ことじゃな。
偽は偽として、地図から赤く塗り分けるべきじゃ。

### 2.2. 第二段. boundary family を \(q=3\) 専用理論へ切る

最新差分は「共有素因子なら \(q=3\)」まで来ておる。ならば次は、その先を **3 専用の honest theorem 群** として切るのが筋じゃ。

わっちなら、次に狙う statement はこういう形にする。

#### A. \(q \neq 3\) 枝

$$
q \mid a-b,\quad q \neq 3
$$

なら、共有素因子分類から (q \nmid S0(a,b)) を引き、よって

$$
v_q(a^3-b^3)=v_q(a-b)
$$

という boundary valuation の **そのまま移送定理** を作る。

#### B. \(q = 3\) 枝

$$
3 \mid a-b,\quad \gcd(a,b)=1
$$

なら、今度は

$$
v_3(a^3-b^3)=v_3(a-b)+1
$$

型を狙うのが自然じゃ。
これは (a^3-b^3=(a-b)S0(a,b)) と、(S0) 側に 3 がちょうど 1 回だけ立つことを示せば届く。
感覚としては (n=3) の LTE を手製で立てるようなものじゃな。

この二本を揃えると、boundary family は valuation 上界ではなく、

$$
v_q(a^3-b^3)=
\begin{cases}
v_q(a-b) & q \neq 3 \\
v_3(a-b)+1 & q=3
\end{cases}
$$

という **exact classification** に置き換えられる。
この形なら偽ではなく、しかも downstream で非常に使いやすい。

### 2.3. 第三段. caller 側の要求を分解する

ここが実務の要じゃ。

`padicValNat_d3_upper_bound` を使っている caller が本当に欲しいのは何か、を切り分ける。

欲しいものは、おそらく次の三つに分かれるはずじゃ。

1. **primitive-prime 側の valuation (\le 1)**
   これは squarefree-GN 仮定つき honest route へ移行。

2. **boundary で共有素因子は 3 しかない**
   これは新しい shared-prime classifier を使う。

3. **boundary で valuation そのものを読みたい**
   これは \(q=3\) 専用理論、または \(q \neq 3\) 枝の exact valuation で読む。

つまり、旧 `padicValNat_d3_upper_bound` が一人で背負っていた仕事を、 **三つの定理族に分配する** のじゃ。
これが次の正しい分解じゃろう。

## 3. 具体的な作業順

わっちなら、次はこの順で進める。

### 3.1. まず入れる補題

* `padicValNat_d3_boundary_eq_boundary_of_ne_three`
* `padicValNat_d3_boundary_eq_boundary_succ_of_three`

名前は多少違ってもよいが、意味は

$$
q \neq 3 \Rightarrow v_q(a^3-b^3)=v_q(a-b)
$$

と

$$
q=3 \Rightarrow v_3(a^3-b^3)=v_3(a-b)+1
$$

じゃ。

### 3.2. 次に入れる target

* `PadicValNatD3BoundaryExactTarget`
* あるいは split して

  * `PadicValNatD3BoundaryNeThreeTarget`
  * `PadicValNatD3BoundaryThreeTarget`

false だった `...ReceiverTarget` の後継は、もう **≤1 target** ではなく **exact valuation target** にすべきじゃ。

### 3.3. そのあと caller migration

* primitive-prime caller は `..._of_squarefree_GN` へ移行
* boundary caller は new exact boundary theorem へ移行
* 旧 `padicValNat_d3_upper_bound` は compatibility alias に格下げ、もしくは分解して retire

## 4. 推論される分岐判断

ここで大事な判断をはっきり言うぞい。

**もう「全枝を valuation \(\le 1\) に押し込む」戦略は捨てるべきじゃ。**

それは primitive-prime branch には合う。
されど boundary-divisor branch には合わぬ。
最新の反例が、それをはっきり示しておる。

だから今後の大方針は、

$$
\text{上界化}
\quad\text{ではなく}\quad
\text{分類化}
$$

じゃよ。

primitive-prime は上界化。
boundary-divisor は分類化。
この二本立てに完全移行するのが次の戦略じゃ。

## 5. 最後の提案

わっちの提案を一文で言えばこうじゃ。

**次は `PadicValNatD3BoundaryReceiverTarget` の救命ではなく、`q=3` 枝専用の exact valuation 定理を立て、boundary family を別 API として独立させよ。**

これが通れば、盤面はさらに美しくなる。
偽命題の残骸を引きずらず、primitive-prime と boundary-divisor がきっぱり別の獣として扱えるようになるからの。

必要なら次に、その 2 本

* \(q \neq 3\) 枝
* \(q = 3\) 枝

について、Lean の証明骨格まで起こすぞい。
