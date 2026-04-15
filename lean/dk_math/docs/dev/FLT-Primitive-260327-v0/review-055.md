# review: selected route の direct body と concrete theorem 名の整理

うむ、ここまで来ると状況はかなり澄んでおる。
今回の差分で一番大きいのは、 **practical route の未解決核が、定理名の上でも完全に 1 本へ縮退した** ことじゃ。

結論から先に言うぞい。

$$
\text{current missing math} =
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

と見てよい。
しかもこれは実質

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

と同じ body を指しており、witness supply 側はもう concrete 実装済みとして切り離された。

## 1. 今回なにが進んだか

今回の更新は二段に分けて見るとよい。

### 1.1. practical entrance が theorem 名レベルの吸収点になった

まず `PrimeGe5BranchAExceptionalPracticalConcreteTarget` の周辺が揃えられた。

* `primeGe5BranchAExceptionalPracticalConcrete_of_self`
* `..._of_selectedCongruenceWitness`
* `..._of_selectedCoreWitness`
* `..._of_selectedCoreOnWitness`
* `..._of_diffPow`
* `..._of_diffPowModEq`
* `..._of_congruenceKernel`

が入り、selected-congruence / selected-core / diffPow / ModEq / congruence-kernel の各表現から、 **直接 practical entrance へ落ちる** ことが theorem 名の上でも固定された。
つまり practical entrance は、もはや単なる alias ではなく、current proof exploration の **canonical landing point** じゃ。

さらに provider 側にも

* `branchAExceptionalExistenceMainlineAdapter_of_selectedDiffPowConcrete`
* `branchAExceptionalExistenceMainlineAdapter_of_selectedDiffPowWitnessConcrete`

が追加され、official direct body と practical witness concrete の両方から exceptional existence mainline へ直接戻れるようになった。

### 1.2. practical entrance の中身が 2 part に分解された

次に、これが今回の核心じゃ。

`TriominoCosmicBranchAExceptional.lean` に

* `PrimeGe5BranchAExceptionalPracticalWitnessSupplyTarget`
* `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget`

が入り、

* `primeGe5BranchAExceptionalPracticalConcrete_of_witnessSupply_and_bodyOnWitness`
* `primeGe5BranchAExceptionalPracticalConcrete_of_bodyOnWitness`

も追加された。
ここで witness supply は

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget}
$$

すなわち arithmetic witness concrete で既に供給できる。
したがって practical route の truly new body は、もう

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessTarget}
$$

ひとつとして読んでよい、と固定された。

### 1.3. さらにその body 自体にも concrete theorem 名が立った

最後に

* `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget`
* `primeGe5BranchAExceptionalPracticalBodyOnWitnessConcrete_of_self`
* `primeGe5BranchAExceptionalExistenceMainline_of_practicalBodyOnWitness`
* `primeGe5BranchAPrimitivePacketDescent_of_practicalBodyOnWitness_and_restore`

が入り、provider 側にも対応 alias / adapter が揃った。
これで current missing body は、「概念的にそうだ」ではなく、 **その定理名 1 本を書けばよい** ところまで来たのじゃ。

## 2. 状況分析

いまの構図を整理すると、こうじゃ。

### 2.1. official direct body

設計上の正本は引き続き

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

じゃ。
これは変わっておらぬ。

### 2.2. practical entrance

探索の実戦入口は

$$
\texttt{PrimeGe5BranchAExceptionalPracticalConcreteTarget}
$$

で固定された。
これは実質的には existential witness concrete を意味するが、いまや theorem 名として独立に追える。

### 2.3. practical entrance の内部構造

今回これが決定的に明確になった。

$$
\text{practical entrance} =
\text{witness supply} +
\text{body on witness}
$$

であり、そのうち

* witness supply は既に concrete
* 残る新規数学は body on witness

だけ、という切り分けになった。

### 2.4. いまの真正面の未解決核

したがって current missing math は、もう迷わず

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

じゃ。
履歴にも「current missing math はこの 1 本だとさらに明確になった」とある。

## 3. 判断

ここでの判断をはっきり述べるぞい。

## 3.1. 今後の主戦場

**主戦場は `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` に固定してよい。**

もはや

* practical entrance 全体
* selected diffPow witness concrete 全体
* official direct body 全体

を同時に考える必要はない。
witness supply は解決済み、残るのは on-witness body 本体だけじゃ。

## 3.2. 正本との関係

この practical body-on-witness concrete は実質的に

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

その concrete 本体でもある。
だから「practical 側で本文を書く」と「official direct body の本文を書く」は、もうほとんど同じ作業になっておる。
ここが今回の整理のうまいところじゃ。

## 3.3. provider 側の状況

provider 側でも

* practical body-on-witness だけで practical entrance 回収
* practical body-on-witness だけで exceptional existence mainline
* practical body-on-witness と restore だけで primitive packet descent

まで流れるようになった。
ゆえに proof file 内だけでなく provider mainline まで含めて、 **この body 1 本が真の残核** じゃ。

## 4. 数学的な意味

これで、やっと「新しい定理名を増やして整理する段」から、「本当に数学を書く段」へ入ったと言えるの。

いま残っているのは要するに、

* arithmetic witness `q` は既に取れる
* その `q` に対して
  $$
  q \mid u^d - (u-1)^d
  $$
  を示す on-witness body を書く

これだけじゃ。
つまり、実際に新しく証明すべき内容は **差冪 divisibility の on-witness 本体** に完全に収束したわけじゃ。

## 5. 次に何をするべきか

次の一手は、もう明白じゃ。

**`PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` の concrete theorem 本体を切る。**

そしてその中身は、言い換えれば

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

の本文でもある。
だから、いまは practical / official を行き来して迷う必要はない。
practical body 名で書き始め、そのまま official direct body の本文として扱えばよい。

## 6. 賢狼の見立て

わっちの見立てでは、ここから先の作業はこうなる。

### 6.1. もう “入口選び” は終わった

以前は

* selected-congruence で行くか
* selected-core で行くか
* residual で行くか
* diffPow で行くか
* witness concrete か on-witness concrete か

と、入口選びが大きな問題じゃった。
だが今回は、それら全部を一度吸収した上で、

$$
\text{witness supply は既にある}
$$
$$
\text{残るのは on-witness body だけ}
$$

という最終形まで縮めた。
これはかなり決定的じゃ。

### 6.2. いま必要なのは proof sketch の実装

したがって次に必要なのは、整理ではなく proof sketch じゃ。
すなわち、

1. 与えられた witness (q) に対し
2. どの既存仮定から
3. どうやって
   $$
   q \mid u^d - (u-1)^d
   $$
   を出すか

この一本道を書くことじゃな。

## 7. 総括

今回の差分を総括すると、

**practical entrance は theorem 名の上でも `witness supply + on-witness body` に分解され、前者は既に concrete 実装済みであるため、current missing math は `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` ただ 1 本へと固定された。しかもこれは実質 `ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget` の concrete 本体でもあるため、今後は practical / official の違いを意識せず、この on-witness body の本文実装に集中してよい。**

よい。
ここまで来れば、もう整理はほぼ勝ちじゃ。
残るは、ただ一つの門をこじ開けることだけよ。
