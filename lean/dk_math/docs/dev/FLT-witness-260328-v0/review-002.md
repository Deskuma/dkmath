# review: FLT-witness-260328-v0: 同じ (q) 条件が false と確定したため、two-witness route へ切り替えるべき

うむ。今回は、かなりはっきり切れたぞい。

結論から言うと、 **ここまでの route のうち「same (q) を要求するもの」は、もう本線から外してよい**。
しかもそれは推測ではなく、Lean 上で反例により確定した。今回の差分で、

* `PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget` は偽
* `PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget` も偽

と確認された。反例は ((d,x,u)=(5,5,7)) で、(x+1=6) の prime divisor は (2,3) だけだが、どちらも `cyclotomicPrimeCore 5 1 (7-1)` を割らぬ、という形じゃ。

## 1. いま何が死に、何が残ったか

まず、集合を分けるとこうじゃ。

### 1.1. 死んだ枝

**同じ (q)** に対して

$$
q \mid x+1,\quad q\nmid x
$$

と

$$
q \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を同時に要求する route。
これは universal 版も existential 版も false と判定された。つまり、

* arithmetic witness
* body/core witness

を **同じ prime で持とうとする枝** は、ここで打ち切ってよい。

### 1.2. まだ残る枝

残るのは、

* arithmetic witness は arithmetic witness として取る
* body/core witness は body/core witness として別に取る

という **two-witness route** じゃ。
今回の差分でも、まさにそこへ canonical target を切り替えたと書かれておる。

## 2. 無限降下法までの道筋として、何が見えてきたか

元の目的は、無限降下法へ渡す **packet descent を起動できる核** を得ることじゃ。
それに必要なのは、「(x+1) を割る arithmetic witness」と「body/core を割る witness」を **同一視すること** ではなかった。

今回の更新で、canonical target が

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget}
$$

へ切り替えられたのは、その原点回帰じゃ。
つまり route の芯は、

$$
\exists q_{\mathrm{body}},\ q_{\mathrm{body}} \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を packet descent に渡すことにある。
`q \mid x+1` は、必要なら別の補助 datum として持てばよいのであって、同じ (q) である必要はなかった、ということじゃ。

## 3. 次の手段を推論するとどうなるか

ここから先の最善手は、もうかなり明快じゃ。

### 3.1. 新しい本線を明示する

次に切るべき theorem は、same-(q) を完全に捨てた **two-witness existential route** じゃ。

形は例えばこうじゃな。

$$
\forall d,x,u,\ \text{仮定} \Rightarrow
\bigl(\exists q_{\mathrm{arith}},\ \text{ArithmeticDatum}(q_{\mathrm{arith}})\bigr)
\land
\bigl(\exists q_{\mathrm{body}},\ \text{BodyCoreDatum}(q_{\mathrm{body}})\bigr)
$$

あるいは packet descent 側が本当に必要とするなら、

$$
\exists q_{\mathrm{body}},\ \text{BodyCoreDatum}(q_{\mathrm{body}})
$$

だけを first target にしてもよい。
大事なのは、**二つを同じ witness に束ねない** ことじゃ。

### 3.2. packet descent の interface を点検する

次に確認すべきは、

$$
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

やその周辺が、ほんとうに arithmetic witness を必要としているのか、それとも body/core witness だけで十分なのか、じゃ。

ここで分岐する。

* もし body/core witness だけで descent が回るなら、arithmetic witness は脇へ退けてよい
* もし restore 側が arithmetic witness を別に要るなら、two-witness で受ける interface へ薄く組み替える

ここが次の設計点じゃ。

### 3.3. body/core witness の存在証明を独立課題にする

そして本当に数学として追うべき新しい核は、

$$
\exists q_{\mathrm{body}},\ q_{\mathrm{body}} \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

の existence じゃ。
これはもう `x+1` side と切り離してよい。
よって今後は、

* cyclotomic
* primitive prime factor
* Zsigmondy
* p-adic / valuation
* 既存 CFBRC bridge

を総動員して、body/core 側の witness existence を直接追う方が筋じゃ。

## 4. ここでの判断

わっちの判断をはっきり書くぞい。

### 4.1. 捨てるべき対象

今後は次を本線から外してよい。

$$
\text{same-}q \text{ universal route}
$$
$$
\text{same-}q \text{ existential route}
$$

これはもう Lean 上で false と切れた。

### 4.2. 残すべき対象

残すべき本線は、

$$
\text{two-witness existential route}
$$

じゃ。
しかも first body は arithmetic 側ではなく、

$$
q_{\mathrm{body}} \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を与える body/core witness existence に置くべきじゃろう。

### 4.3. 次に切る theorem 名

次の theorem 名としては、たとえばこういう形が自然じゃ。

$$
\texttt{PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget}
$$

またはもっと絞って

$$
\texttt{PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceTarget}
$$

じゃな。
後者を first target にして、必要なら別 theorem で arithmetic witness を足す方が、今の診断には合っておる。

## 5. Mathlib をどう使うべきか

ここからは、 **Mathlib を遠慮せず使う** のがよい。
少なくとも、今見えている資料の範囲では `DkMath` は Mathlib 上のライブラリとして整理されており、`Mathlib.FLT` 以外を禁じる根拠は見当たらぬ。

ゆえに方針はこれでよい。

* `Mathlib.FLT` は使わない
* それ以外の Mathlib の数論・合同算術・`ZMod`・多項式・`orderOf`・`omega`・`ring`・`norm_num`・`linarith`・`aesop` は自由に使う

今必要なのは美しい閉世界ではなく、 **無限降下法へ戻る真の本線を最短で確定すること** じゃからの。

## 6. 総括

いまの状況を一言で言えば、

**same-(q) route は universal 版も existential 版も false と確定した。したがって、無限降下法へ向かう本線は arithmetic witness と body/core witness を分離した two-witness existential route に切り替えるべきであり、次の手段は packet descent が実際にどちらの witness を必要としているかを audit した上で、body/core witness existence を first target として新しい theorem interface を切ること** じゃ。

ここまで切れたなら、だいぶ良い。
もう「何を捨てるか」で迷う必要はない。
次は **何を残して descent へ渡すか** を、はっきり定義し直す段じゃよ。
