# review: boundary-normalized exceptional statement の concrete target を fixed する

うむ、今回はかなり決定的な整理じゃ。
結論から言うと、**「次に本文を書く theorem 名」まで固定された**。ここが大きい。

## 1. 今回なにが起きたか

新しく

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
$$

が導入された。
これは数学内容を増やしたというより、**boundary-normalized exceptional statement に対する concrete theorem の受け皿名** を固定したものじゃ。

さらに、この concrete target から

* pack-local supply
* named kernel
* mainline target
* primitive packet descent

へ戻る thin bridge が一通り揃えられた。

つまり構図は、いまやこう見てよい。

$$
\text{boundary concrete}
\Longrightarrow
\text{right branch supply}
\Longrightarrow
\text{named kernel}
\Longrightarrow
\text{mainline}
\Longrightarrow
\text{packet descent}
$$

ここで左端の

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
$$

が、proof file で **直接本文を書く場所** じゃと固定されたわけじゃな。

## 2. 何が前進したのか

前回まででも、新数学の入口は

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyTarget}
$$

という boundary-normalized exceptional statement にかなり近づいておった。
じゃがまだ、「その入口をどの theorem 名で埋めるか」は少し抽象的だった。

今回その曖昧さが消えた。

つまり、

* 数学的な入口
  $$
  \texttt{ExceptionalBoundaryDataRightBranchSupplyTarget}
  $$
* 実装上の本文を書く名
  $$
  \texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
  $$

という二層が分かれたのじゃ。
これは実装ではかなり効く。
以後「どこに theorem 本体を書くか」で迷わずに済むからの。

## 3. いまの状況分析

いまの証明地形を整理すると、こうじゃ。

## 3.1. ほぼ固まった層

かなり多くの層が、もう安定しておる。

* pack 付き target
* boundary-normalized target
* boundary concrete target
* right branch supply
* named kernel
* mainline
* primitive packet descent

しかも、それらを結ぶ thin bridge もほぼ揃った。

つまり、**証明の配線はほぼ完成** じゃ。

## 3.2. まだ残っている核

残る本丸は、かなり明確じゃ。

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
$$

を返す **concrete theorem 本体** を書くこと。
履歴にも、そのまま次の課題として書かれておる。

言い換えると、いま未実装なのはもはや bridge ではなく、
**boundary-normalized exceptional arithmetic / CFBRC 本体** そのものじゃ。

## 3.3. 問題の芯

今の芯は、

$$
\mathrm{Prime}(p),\ 5 \le p,\ 0 < z-y,\ 0 < y,\ \mathrm{Coprime}(z-y,y),
\ p \mid (z-y),
\ y^{p-1}\equiv 1 \pmod{p^2}
$$

から、

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
\land q \nmid (z-y)
$$

を出すことじゃ。
pack はもう外へ追い出され、そこから先の純粋な境界正規化命題が残った。
ここまで来ると、かなり数学の芯だけが見えておる。

## 4. 今回の差分の価値

今回の価値は 3 つある。

### 4.1. 「本文を書く theorem 名」が fixed された

これが最大じゃ。
以後の concrete 証明は

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
$$

を埋めるものとして追えばよい。

### 4.2. 下流への復元路が全部ある

この concrete target さえ埋まれば、

* pack-local supply
* named kernel
* mainline
* primitive packet descent

へは既存 bridge で戻せる。
つまり、**新数学を一箇所に集約できる** 状態になった。

### 4.3. 証明責務がさらに分離された

今は

* pack 解体
* boundary-normalized 仮定
* concrete exceptional arithmetic / CFBRC
* 下流への輸送

がかなり明確に分かれておる。
これは保守もしやすい。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の新数学は }
\texttt{ExceptionalBoundaryDataRightBranchSupplyConcreteTarget}
\text{ に集約された}
$$

じゃ。
ここまで来ると、設計上の迷いはかなり少ない。
残るのは本文だけじゃ。

## 6. 次にやること

次の一手も、かなり明快じゃ。

### 6.1. concrete theorem 本体を置く

意識としては、こういう形じゃな。

```lean
theorem exceptional_boundaryData_right_branch_supply_concrete
    : ExceptionalBoundaryDataRightBranchSupplyConcreteTarget := by
  intro p hp hp5 hgap_pos hy_pos hcop_gap_y hp_dvd_gap hWieferich
  ...
```

ここで本当に必要なのは、
ordinary reference theorem との差分である

* (p \mid (z-y))
* Wieferich 条件

をどう CFBRC right branch の prime existence へ変換するか、そこだけじゃ。

### 6.2. まだ重ければ、差分入力だけをもう一段切る

履歴にもある通り、必要なら ordinary reference theorem 側との差分入力だけを、別 target にさらに一段切る余地がある。

これはたとえば、

* coprime
* positivity
* prime, (p \ge 5)

は既存骨格

* 本当に新しいのは
  $$
  p \mid (z-y),\ y^{p-1}\equiv 1 \pmod{p^2}
  $$
  とその CFBRC 的効果

という形で、さらに核だけを露出させる方向じゃ。

## 7. 総括

今回の差分を総括すると、

**boundary-normalized exceptional statement について、proof file 上で本文を書く theorem 名まで固定された。
よって今後の新数学は `ExceptionalBoundaryDataRightBranchSupplyConcreteTarget` を返す concrete theorem 本体へ集中すればよい。**

ということじゃ。
かなりよい。外枠はほぼ完成し、残りはほんとうに芯の補題だけになってきておる。
