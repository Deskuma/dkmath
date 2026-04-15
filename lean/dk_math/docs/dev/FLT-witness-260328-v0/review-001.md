# review: FLT-witness-260328-v0: 補正は正しいが、まだ同じ (q) 条件が残っているのは要注意

うむ。補正は正しい。しかも、かなり大事な補正じゃ。

いまの更新で、前の universal な datum-local core route は **反例で偽** と Lean 上で確定され、その後の canonical target が

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget}
$$

へ切り替わった。
つまり、「固定した datum のすべての (q) で core を返す」路線は捨てて、**body/core witness を持つ (q) の存在** を主役に戻したわけじゃ。これは、無限降下法へ向かう発想としては筋が良い。

## 1. そもそも何を目指していたか

元の目的は、わっちの見立てではこれじゃ。

$$
\text{Branch A exceptional の仮定}
\Longrightarrow
\text{primitive packet descent を起動できる witness}
$$

すなわち、無限降下法へ渡す **一個の良い素数 witness** を作ることじゃ。
途中で route が膨れて、

$$
q \mid x+1,\ q\nmid x
$$

という arithmetic 側の (q) を、そのまま

$$
q \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

の (q) と同一視し始めた。そこがズレじゃった。今回の更新は、そのズレを修正して、datum を

* arithmetic datum
* body/core datum

に分け、canonical target を existential witness 側へ戻した。ここは良い補正じゃ。

## 2. ただし、まだ一段だけ注意が要る

ここが肝じゃ。

今回の新 target は

$$
\forall d,x,u,\ \text{仮定} \Rightarrow
\exists q,\
\texttt{PrimeGe5BranchAExceptionalPracticalArithmeticDatum}\ d\ x\ u\ q
\land
\texttt{PrimeGe5BranchAExceptionalPracticalBodyCoreDatum}\ d\ x\ u\ q
$$

という形じゃ。
つまり datum は分離されたが、**まだ同じ (q)** に

* (q \mid x+1,\ q\nmid x)
* (q \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1))

の両方を要求しておる。

前の universal theorem が偽だった本質は、「same (q) を arithmetic 側と body/core 側で共有させたこと」にあった。
だから今回の補正は正しい方向じゃが、**まだ same (q) 条件が残っておる** なら、次に真っ先に切るべきはここじゃ。

## 3. 無限降下法までの道のりとして見た、ここからの推論

わっちなら、ここから先は三段で考える。

### 3.1. 第1段. 新 canonical target が本当に残るかを即検査する

前の反例

$$
(d,x,u,q)=(5,5,7,2)
$$

で universal theorem は潰れた。
ならば次は、

$$
(d,x,u)=(5,5,7)
$$

に対して **どの prime (q \mid x+1)** でも core/body witness になれないかどうかを、その場で Lean で切るべきじゃ。
もし (x+1=6) の prime 因子 (2,3) のどちらも

$$
q \nmid \operatorname{cyclotomicPrimeCore}(5,1,6)
$$

なら、新しい existential `BodyCoreWitness` route も偽じゃ。
これはもう臆せず、さっさと切るべき段じゃな。

### 3.2. 第2段. もし偽なら、same (q) 条件を捨てる

その場合、残すべき命題はこれじゃ。

$$
\exists q_{\mathrm{core}},\
q_{\mathrm{core}} \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

と

$$
\exists q_{\mathrm{arith}},\
q_{\mathrm{arith}} \mid x+1,\ q_{\mathrm{arith}} \nmid x
$$

を **別 witness** として持つ route じゃ。
つまり arithmetic datum と body/core datum を分けるだけでなく、**witness も分ける**。
わっちは、無限降下法の本来の姿はこちらだと思うておる。
前者は core/body 側の primitive packet seed、後者は boundary/arithmetic 側の補助情報じゃ。 same (q) を要求する必然は、まだ見えておらぬ。

### 3.3. 第3段. restore / packet descent の interface を見直す

もし現 `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` や packet descent wrapper が、暗黙に same (q) を要求しておるなら、そこが真の refactor 点じゃ。
言い換えると、次に見るべきは theorem 名の整理ではなく、

$$
\text{packet descent が本当に必要としているデータは何か}
$$

の切り分けじゃ。
無限降下法へ必要なのが core witness なら、restore theorem は **arithmetic datum と core witness を別引数で受ける** 形へ薄く組み替えるのが筋じゃろう。

## 4. いま本当に検査すべきこと

なので、ここからの展開として最優先なのは、これ一つじゃ。

$$
\neg \texttt{PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget}
$$

が、同じ ((d,x,u)=(5,5,7)) で出るかどうかを Lean で確定すること。
今回の更新で反例検査の流儀はすでに入っておる。 `selectedCoreOnDatumConcrete` を false にしたのと同じやり方で、今度は existential target も即切れるはずじゃ。

これが false なら、次の canonical target はもう明白で、

$$
\text{same-}q \text{ existential}
$$

ではなく

$$
\text{two-witness existential}
$$

へ行くべきじゃ。

## 5. わっちの推奨する新しい本線

無限降下法まで意識するなら、わっちはこう組み替える。

まず arithmetic 側は

$$
\exists q_{\mathrm{arith}},\
q_{\mathrm{arith}} \mid x+1,\ q_{\mathrm{arith}} \nmid x
$$

として隔離する。
次に body/core 側は

$$
\exists q_{\mathrm{core}},\
q_{\mathrm{core}} \mid \operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を別に持つ。
そして packet descent の入口は

$$
(q_{\mathrm{arith}}, q_{\mathrm{core}})
$$

の二本立てで組む。
もし将来、両者が一致する十分条件が別に見つかれば、そのとき special theorem として合流させればよい。
最初から same (q) を本線にすると、また偽枝を育てる危険がある。

## 6. Mathlib について

ここから先は、**Mathlib を遠慮せず使う** のがよい。
避けるべきは `Mathlib.FLT` 本体だけで十分じゃ。
今回みたいな反例検査、素因数、合同算術、`decide`、`norm_num`、`omega`、`ring`、`linarith` は、むしろどんどん使うべきじゃ。
いま必要なのは「DkMath だけで美しく閉じる」ことではなく、**偽枝を最短で刈り、降下の本線だけを残すこと** だからの。

## 7. 総括

いまの補正は正しい。
だが、その補正の次にやるべきことも、もう明白じゃ。

**`PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget` が same (q) の existential として本当に真かを、前と同じ反例型で即検査する。**
それが false なら、無限降下法への本線は

$$
\text{same-}q \text{ route}
$$

ではなく

$$
\text{arithmetic witness} ;+; \text{body/core witness}
$$

の **二本立て existential route** へ切り替える。
そこまで行って初めて、元の目的、すなわち無限降下法へ渡す道が真っ直ぐ見えるはずじゃ。

この賢狼の見立てでは、次の一手は theorem を増やすことではない。
**偽か真かを即断し、その結果に従って route を二本 witness へ分解するかどうかを決める。**
これじゃよ。
