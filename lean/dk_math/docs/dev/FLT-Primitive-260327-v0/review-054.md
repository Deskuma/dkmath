# review: selected route の direct body と concrete theorem 名の整理

うむ、ここまで来ると、もはや「枝を増やした」のではなく、 **入口と正本を二層に分けて固定した** と言うのが正しいの。

今回の状況を一言で言えば、

$$
\text{official direct body}
\neq
\text{practical entrance}
$$

を、proof file 側と provider 側の両方で明示した段じゃ。
そして現在の判断はかなり明快じゃ。

* **正本** は
  $$
  \texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
  $$
* **実戦入口** は
  $$
  \texttt{PrimeGe5BranchAExceptionalPracticalConcreteTarget}
  $$
  すなわち実質
  $$
  \texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget}
  $$
  じゃ。

## 1. 今回なにが進んだか

今回の更新は、単に橋を増やしただけではない。
**「どこに本文を書くか」と「どこから実際に攻めるか」を分離し、その両方を downstream まで通した** のが本質じゃ。

### 1.1. provider 側にも二本立てを反映

まず `TriominoCosmicGapInvariant.lean` 側に

* `BranchASelectedDiffPowConcreteAdapterTarget`
* `BranchASelectedDiffPowWitnessConcreteAdapterTarget`

が入り、さらに

* `branchAPrimitivePacketDescentAdapter_of_selectedDiffPowConcrete_and_restore`
* `branchAPrimitivePacketDescentAdapter_of_selectedDiffPowWitnessConcrete_and_restore`

が追加された。
これで proof file 側の

* `SelectedDiffPowOnWitnessConcrete`
* `SelectedDiffPowWitnessConcrete`

の両方が、provider mainline の splice point としても同じ粒度で扱えるようになった。

### 1.2. practical diffPow witness が selected-core からも戻れるようになった

次に `TriominoCosmicBranchAExceptional.lean` 側で

* `...selectedDiffPowWitness_of_selectedCoreWitness`
* `...selectedDiffPowWitness_of_selectedCoreOnWitness`
* `...SelectedDiffPowWitnessConcrete_of_selectedCoreWitness`
* `...SelectedDiffPowWitnessConcrete_of_selectedCoreOnWitness`

が追加された。
要するに、

$$
q \mid \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
$$

から

$$
q \mid u^d - (u-1)^d
$$

を直接回収する橋が入り、practical entrance が selected-core 側からも直接使えるようになったわけじゃ。

### 1.3. practical diffPow witness が selected-congruence からも戻れるようになった

さらに

* `...selectedDiffPowWitness_of_selectedCongruenceWitness`
* `...selectedDiffPowWitnessConcrete_of_selectedCongruenceWitness`

と、その downstream が追加された。
これで practical entrance は

* selected-core
* selected-congruence
* diffPow
* ModEq
* congruence kernel

のいずれの表現からでも戻れる。
つまり **現在の探索中の上流表現を気にせず、一旦 practical entrance に落として考えてよい** 段になった。

### 1.4. practical entrance 自体が theorem 名として固定された

最後にもっとも重要なのは、

* `PrimeGe5BranchAExceptionalPracticalConcreteTarget`

が追加され、

* `...practicalConcrete_of_selectedDiffPowConcrete`
* `...Mainline_of_practicalConcrete`
* `...PacketDescent_of_practicalConcrete_and_restore`

まで入ったことじゃ。
加えて provider 側にも

* `BranchAExceptionalPracticalConcreteAdapterTarget`
* `BranchAExceptionalExistenceMainlineAdapterTarget`
* `branchAPrimitivePacketDescentAdapter_of_practicalConcrete_and_restore`
* `branchAExceptionalExistenceMainlineAdapter_of_practicalConcrete`

が揃った。

これは大きい。
つまり code 上でも、 **official direct body は残しつつ、実際の proof 探索で使う practical entrance を別名で固定した** のじゃ。

## 2. 状況分析

いまの構造は、かなり整理されておる。

### 2.1. official direct body

proof file の正本は依然として

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

じゃ。
これは universal on-witness の concrete 名であり、設計上の正式名称じゃ。

### 2.2. practical entrance

しかし実際に本文探索で使う入口は

$$
\texttt{PrimeGe5BranchAExceptionalPracticalConcreteTarget}
$$

すなわち実質

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget}
$$

へ寄せてよい、と固定された。
履歴でも明確に「official direct body は残すが、実際の proof 探索はまず existential witness 版のこちらを入口として進めてよい」と書かれておる。

### 2.3. practical entrance への流入路

現在この practical entrance へは、

* selected-congruence
* selected-core witness
* selected-core on-witness
* diffPow
* diffPow ModEq
* congruence kernel
* official direct body

のどれからでも戻れるようになった。
この意味で practical entrance は、 **current proof exploration の吸収点** と言ってよい。

### 2.4. downstream の配線

さらに、

* exceptional existence mainline
* primitive packet descent
* provider 側 adapter
* provider 側 exceptional existence mainline

まで、practical entrance から直接流せる。
だから今後は、上流でどう来たかを忘れて、まず practical entrance に落としてから先へ流す、という作業手順が可能になった。

## 3. 判断

ここでの判断は、かなりはっきりしておる。

## 3.1. 設計上の正本

**正本は引き続き**
$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$
**じゃ。**

これは変えぬ方がよい。
理由は、on-witness の universal な形が proof file の正式な direct body として一番整っているからじゃ。

## 3.2. 実戦上の入口

**実戦入口は**
$$
\texttt{PrimeGe5BranchAExceptionalPracticalConcreteTarget}
$$
**で固定してよい。**

実質的には `SelectedDiffPowWitnessConcrete` じゃが、この practical entrance 名を立てたことで、

* code 上の意図が見える
* downstream の mainline / adapter へ直結する
* 「まずここを書けばよい」が明文化された

という利点がある。

## 3.3. 次に本文を書く場所

したがって、いま「どこに本文を書くべきか」という問いに対するわっちの判断はこうじゃ。

* **正式な定着先** としては
  `ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget`
* **実際に最初に本文を試す場所** としては
  `PrimeGe5BranchAExceptionalPracticalConcreteTarget`

じゃ。
この二段構えが、いま最も自然じゃ。

## 4. なぜこの判断がよいか

理由は単純で、practical entrance は

* arithmetic witness と直に噛み
* congruence/core/diffPow のどこからでも落とせて
* mainline/provider まで一気に通る

からじゃ。
つまり proof body を起こす時に必要な「前後の圧縮率」が最も高い。

一方で official direct body は、定理体系の見通しとしては美しいが、最初に手を入れるには少し抽象度が高い。
だから、

$$
\text{探索} \to \text{practical entrance},\qquad
\text{定着} \to \text{official direct body}
$$

という分業が最も理にかなっておる。

## 5. 次に何をするべきか

履歴どおり、次の課題は

* `ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget`
* あるいは `PrimeGe5BranchAExceptionalPracticalConcreteTarget`

の concrete theorem 本体を切ることじゃ。

わっちのおすすめは、いまは practical entrance 名で直接書き始めることじゃな。
なぜなら、それが現時点で最も「本文までの距離」が短いからじゃ。

書き始めの形も、かなり見えておる。

$$
\text{与えられた } d,x,u \text{ に対し witness } q \text{ を arithmetic side で取り、}
$$
$$
q \mid u^d - (u-1)^d
$$
を示す。

ここまで書ければ、mainline も provider 側 adapter ももう流れる。

## 6. 総括

今回の差分を総括すると、

**official direct body と practical entrance がコード上で明確に分離・固定され、practical entrance である `PrimeGe5BranchAExceptionalPracticalConcreteTarget` は selected-congruence / selected-core / diffPow の各表現から直接戻れる current proof exploration の吸収点になった。したがって、次に concrete 本体を起こすべき第一候補は practical entrance 側であり、official direct body はその後の定着先として保つのが自然である。**

よい。
ここまで来れば、もう迷路ではないの。
入口は二つあるが、歩き始める道は一つに見えてきた。
