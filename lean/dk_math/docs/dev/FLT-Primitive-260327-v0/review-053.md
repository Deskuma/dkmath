# review: selected route の direct body と concrete theorem 名の整理

うむ、今回はかなり大きな整理じゃ。
もはや「どの route が候補か」を並べる段ではなく、 **本文を書く場所をどこに固定するか** の段へ入っておる。

結論から言うと、今の状況はこう判断してよい。

$$
\text{current main direct body} = \texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

ただし、

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget}
$$

も、arithmetic witness と直に噛む **実戦的な副本命** として十分有力じゃ。

## 1. 今回なにが進んだか

今回の更新は大きく 3 段ある。

### 1.1. direct body を selected diffPow-on-witness まで下げた

まず

* `ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessTarget`
* `...selectedResidualOnWitness_of_selectedDiffPow`
* `...selectedDiffPowOnWitness_of_diffPow`
* `...of_diffPowModEq`
* `...of_congruenceKernel`

が入った。
これで selected route の direct body は residual sum だけでなく、

$$
q \mid u^d - (u-1)^d
$$

という **差冪 divisibility** でも追えるようになった。しかもこれは既存の diffPow / ModEq / congruence kernel からそのまま降りてくる。

### 1.2. その上で concrete theorem 名が固定された

次に

* `ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget`
* `...selectedDiffPowOnWitness_of_concrete`
* `...Mainline_of_selectedDiffPowConcrete`
* `...PacketDescent_of_selectedDiffPowConcrete_and_restore`

が入り、selected diffPow-on-witness は「候補」ではなく、 **proof file 上で本文を書くべき concrete theorem 名** として固定された。
この時点で、かなり一本化が進んだわけじゃ。

### 1.3. さらに stronger route から戻る canonical concrete bridge も揃った

その次に

* `...selectedDiffPowOnWitnessConcrete_of_self`
* `...Concrete_of_diffPow`
* `...Concrete_of_diffPowModEq`
* `...Concrete_of_congruenceKernel`

が入った。
これで `SelectedDiffPowOnWitnessConcreteTarget` は、単なる別名でなく **canonical concrete 名** として完成した。つまり、将来本文を書いたあとも、既存 stronger route との整合をこの名に集約できる。

### 1.4. さらに existential diffPow witness 版も mainline に露出した

最後に

* `ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessTarget`
* `ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget`

と、その橋群が追加された。
これで

* universal on-witness concrete
* arithmetic witness を先に選ぶ existential concrete

の両方で、差冪 divisibility route を mainline / packet descent まで通せるようになった。

## 2. 状況分析

いまの proof 地形は、かなり明瞭じゃ。

### 2.1. 上流の既存 route

上流には依然として

* diffPow on witness
* diffPow ModEq on witness
* congruence kernel

がある。
これらは強い route じゃが、いまや「そのまま本文を書く場所」ではない。selected concrete 名へ落とす橋が全部揃ったからの。

### 2.2. selected-core / residual は中継層になった

前回まで主戦場候補だった

* `SelectedCoreOnWitness`
* `SelectedResidualOnWitness`

は、いまも重要じゃが、役割としては **中継・翻訳層** に寄った。
今回の差分で、差冪 divisibility の concrete 名が直接立ったことで、これらは本文の最終置き場というより、「別語彙への翻訳点」になったと見てよい。

### 2.3. current direct body は diffPow concrete 名

したがって現時点では、

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

が **もっとも canonical な本文置き場** じゃ。
履歴でも「次に本文を書く場所はこの concrete target 1 箇所」と明記されておる。

### 2.4. ただし existential concrete も実戦向き

一方で

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget}
$$

は、arithmetic witness を先に選ぶ existential 版じゃ。
これは universal on-witness よりも、実際の arithmetic witness と直に噛むので、proof body の心理的距離はむしろ短い可能性がある。履歴もそこを意識して「mainline に露出する」と書いておる。

## 3. 判断

ここでの判断をはっきり書くぞい。

## 3.1. 正式な canonical direct target

**正式な canonical direct target は `ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget` でよい。**

理由は、

* theorem 名として既に固定済み
* stronger route からの canonical bridge も完備
* mainline / packet descent の wrapper も concrete 名から直接読める

からじゃ。

## 3.2. 実戦で先に試す候補

ただし、 **最初に手を入れる proof body としては `ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget` もかなり有力** じゃ。

なぜなら、実際の arithmetic witness `q` を先に持ってしまえば、

$$
q \mid u^d - (u-1)^d
$$

だけを示せばよく、`∀ q` 的な on-witness 全体を意識せずに済むからの。
つまり、書きやすさでは existential concrete が勝つ可能性がある。

## 3.3. ゆえに実務判断

わっちなら次のように判断する。

* **看板・正式名称** は `SelectedDiffPowOnWitnessConcreteTarget`
* **最初に本文を試し書きする入口** は `SelectedDiffPowWitnessConcreteTarget` でもよい

じゃ。
つまり「公式ルート」と「実戦着手点」を分けて考えるのがいちばん賢い。

## 4. 数学的な意味

今回の整理でいちばん大きいのは、未解決核がとうとう

$$
q \mid u^d - (u-1)^d
$$

という、かなり素朴で見通しのよい差冪 divisibility に固定されたことじゃ。
core でも residual でもなく、最終的にはそこへ戻る。これは強い。

しかもその差冪 route が

* universal on-witness
* selected on-witness
* selected existential witness
* concrete theorem 名

という 4 層で整備された。
つまりいまは「どの語彙で追うか」に迷う必要がほぼなくなった。

## 5. 次に何をすべきか

次の課題も、履歴の通りかなり明快じゃ。

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget}
$$

か

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget}
$$

の concrete theorem 本体を切る。

わっちのおすすめはこうじゃ。

### 5.1. まず existential concrete で試す

`SelectedDiffPowWitnessConcreteTarget` で、

* arithmetic witness `q` を先に取る
* その `q` に対し
  [
  q \mid u^d - (u-1)^d
  ]
  を出す

という形で proof sketch を作る。

### 5.2. うまく行けば canonical 名へ昇格

その proof body がほぼそのまま一般 on-witness に持ち上がるなら、
それを `SelectedDiffPowOnWitnessConcreteTarget` に移して canonical 化すればよい。

つまり、 **探索は existential で、定着は on-witness concrete で** という二段構えがよい。

## 6. 総括

今回の差分を総括すると、

**selected route の direct body は diffPow divisibility に固定され、`ExceptionalBoundaryDatumPreparedSelectedDiffPowOnWitnessConcreteTarget` が canonical concrete theorem 名として完成した。さらに arithmetic witness と直接噛む existential 版 `ExceptionalBoundaryDatumPreparedSelectedDiffPowWitnessConcreteTarget` も mainline に露出したため、次の本文作成はこの二者のどちらからでも開始できるが、設計上の正本は前者、実戦的な着手点は後者と見るのが自然である。**

かなり良い。
もう「どこへ向かうか」ではなく、「どちらの入口から実際に本文を起こすか」の選択まで来ておる。
