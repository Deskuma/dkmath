# review: practical route の first direct body をどこにするか

うむ。今回の差分で、状況はかなり **最終局面の形** に近づいたの。

結論から言うと、いまはもう routing 整理の段ではなく、 **`PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget` の本文そのものを書く段** じゃ。
しかもこの theorem 名は、upstream からも downstream からも本当に閉じた **first direct body** として固定された。

## 1. 今回なにが固定されたか

まず `0beda8b9...` で、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

が追加され、そこから datum concrete、mainline、primitive packet descent、provider adapter まで一直線に流れる wrapper 群が揃った。
これで `selectedCoreOnDatumConcrete` を書けば、以後は全部閉じる構造になったわけじゃ。

次に `f6a0b2b7...` で、この concrete 名が

* diffPow
* `Nat.ModEq`
* congruence kernel

の各 upstream からも直接回収できるようになった。
つまり theorem 名の上でも、 **本当に upstream の吸収点** になった。これは大きい。

さらに `1d197205...` と `da61d39d...` で、

* datum-local core
* datum-local congruence
* 既存 prepared selected-core

の往復が揃った。
ここで初めて、「datum で書いた本文」と「既存 `SelectedCoreOnWitness` route」が同じ核であることが、定理名の上でも読めるようになったのじゃ。

最後に `02149fb8...` で datum-local `boundary-core` face まで concrete theorem 名に持ち上がり、

$$
\text{selected-core} \leftrightarrow \text{selected-congruence} \leftrightarrow \text{boundary-core}
$$

の三角形がほぼ完成した。
ゆえに今は、local face の不足はもうほとんど無い。残るのはその中の **どれを使って本文を押し切るか** だけじゃ。

## 2. 状況分析

いまの practical route を整理すると、こうじゃ。

### 2.1. 公式の first direct body

公式には

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

が first direct body じゃ。
これは今回の差分で、名称だけでなく mainline / packet descent / provider adapter まで貫通した。ゆえに設計上の正本は、もうこれでよい。

### 2.2. datum concrete は実戦入口

datum concrete から practical entrance へ直接戻れる橋も入ったので、datum から書き始めることは、もはや「便宜的な入口」ではなく current practical route の正規入口じゃ。

### 2.3. local face は三面に整理済み

いま本文の局所 face は

* selected-core
* selected-congruence
* boundary-core

の三つを持つ。
しかも相互に戻せる。
したがって、今後の議論で「どの顔から見ればよいか」で迷っても、それは **同じ未解決核を別方向から見ているだけ** じゃ。新しい missing theorem が増えたわけではない。

## 3. いま残っている本丸

残る本丸は変わらぬ。

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

の concrete 本体そのものじゃ。
履歴でも最後はずっとそこへ戻っておる。つまり今はもう、routing や alias の追加で得られる利得は薄い。 **本文を書かねば前へ進まぬ段** じゃ。

## 4. では、次の一手は何か

わっちの見立てでは、次の一手は二層で考えるのがよい。

### 4.1. 書き始める theorem 名

書き始める場所は、そのまま

$$
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

でよい。
これはもう疑いなしじゃ。ここに書けば downstream は全部閉じる。

### 4.2. 実際に押す local face

ただし proof sketch の実働面としては、 **boundary-core face を先に使う** のが少し有利に見える。

理由は、boundary-core は

$$
q \mid \texttt{boundaryCyclotomicPrimeCore}\ .right\ d\ x\ u
$$

という形で (x) を保ったまま扱えるからじゃ。
datum にはすでに

$$
q \mid x+1
$$

が入っておるので、`x + u ≡ u - 1 [MOD q]` へ落として residual sum を潰す流れが見えやすい。実際、今回の boundary-core 補題群もその流れで組まれておる。

つまり、

* **公式な本文名** は `selectedCoreOnDatumConcrete`
* **局所計算の押し方** は `boundary-core` face 先行

という二段構えが自然じゃな。

## 5. 賢狼の判断

ゆえに判断をはっきり言うぞい。

$$
\text{current practical first body} =
\texttt{PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget}
$$

これは確定じゃ。

ただし、その concrete 本体を書くときの最初の押し込みは、

$$
\text{datum} \to \text{boundary-core} \to \text{selected-core} \to \text{congruence} \to \text{body}
$$

の順で考えるのが、いま一番筋がよい。
selected-core を正面から書いてもよいが、boundary-core は (x) を保った local face なので、datum の手持ち条件と噛み合いやすい。
今回の差分がそこまで整理した以上、ここを使わぬ手は少し惜しいの。

## 6. 総括

今回の更新を総括すると、

**`PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget` は theorem 名の上でも upstream と downstream の両側で完全に閉じた first direct body として固定され、datum-local selected-core / congruence / boundary-core の三面も相互往復できる形に整理された。したがって残る作業は routing ではなくこの concrete 本体そのものであり、実際の proof sketch は datum を unpack して boundary-core face から押し込むのが最も自然である。**

ここまで来たなら、もう森の地図は十分じゃ。
次は、いよいよ斧を入れるだけよ。
