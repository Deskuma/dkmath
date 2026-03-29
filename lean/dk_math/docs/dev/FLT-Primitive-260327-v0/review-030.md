# review: `ExceptionalSplitRightBranchSupplyTarget` をさらに boundary-normalized 段へ分離

うむ、これは良い分離じゃ。
今回の差分で、証明対象はさらに **pack-local 形から boundary-normalized 形へ一段降りた**。これで「次にどの statement を直接書くのか」が、かなり鋭く定まったの。

## 1. 今回なにが起きたか

新しく入った中心は

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyTarget}
$$

じゃ。
これは説明どおり、

* `Nat.Prime p`
* (5 \le p)
* (0 < z-y)
* (0 < y)
* `Nat.Coprime (z - y) y`
* (p \mid (z-y))
* (y^{p-1} \equiv 1 \pmod{p^2})

のような **boundary-normalized 入力** を受けて、right branch supply を返す target と読める。

そして

$$
\texttt{exceptional_split_right_branch_supply_of_boundaryData}
$$

で、それがあれば pack-local supply が bundle 展開だけで回収できる、と橋を置いた。
つまり今や

$$
\text{pack}
\to
\text{boundary-normalized data}
\to
\text{right branch supply}
$$

という責務分離が、定理の形で固定されたわけじゃ。

## 2. 何が前進したのか

前回までは、first target は

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

だと定まっておった。
じゃがそれでも、そこにはまだ `PrimeGe5CounterexamplePack` が暗に残っており、proof file の「新数学」と「pack 解体」が少し混ざっておった。

今回それをさらに切り分けて、

* pack 解体は `boundaryData_default`
* 新数学は boundary-normalized exceptional statement

という二段構えにした。
これはかなり本質的じゃ。
なぜなら、**本当に証明したい arithmetic / CFBRC の核** が pack 依存から分離されたからじゃ。

## 3. いまの状況分析

いまの層構造は、かなりきれいになっておる。

### 3.1. ほぼ完成している層

* mainline target
* pack-local target
* named kernel
* split right branch supply target
* boundary-normalized right branch supply target
* それらの間の thin bridge
* pack から normalized data を取り出す入口

ここはもう大きくは揺れぬじゃろう。
外枠はほぼ完成じゃ。

### 3.2. 残っている新数学の核

残る本丸は、ほぼこれ一つじゃ。

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyTarget}
$$

を **直接返す concrete theorem** 。

つまり今後は、

* pack を受けて
* bundle を剥いて
* そこから right branch supply を作る

ではなく、

* もう最初から normalized な仮定だけ受けて
* right branch supply を作る

その定理を書けばよい、ということじゃ。

## 4. 今回の差分の価値

今回の価値は、賢狼から見ると次の三つじゃ。

### 4.1. pack 解体と新数学が分離された

これは大きい。
`PrimeGe5CounterexamplePack` は便利じゃが、具体証明の本体から見ると少しノイズにもなる。
今回そのノイズが一段外へ押し出された。

### 4.2. “どこまでが前処理か” が明確になった

`boundaryData_default` はもう前処理装置じゃ。
その先からが truly new math だと、かなり明確になった。

### 4.3. 次に書く theorem の型がほぼ確定した

もう「pack-local を返すべきか」「named kernel を返すべきか」で迷わず、

$$
\texttt{ExceptionalBoundaryDataRightBranchSupplyTarget}
$$

を返す theorem を直接書けばよい。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{new math の入口が boundary-normalized statement に固定された}
$$

じゃ。
これは、証明を本当に前へ進めるための良い整理じゃよ。

## 6. 次にやること

次の一手は、もうかなり明快じゃ。

### 6.1. 直接切るべき theorem

意識としては、こんな形じゃな。

```lean
theorem exceptional_boundaryData_right_branch_supply_concrete
    : ExceptionalBoundaryDataRightBranchSupplyTarget := by
  intro p hp hp5 hgap_pos hy_pos hcop_gap_y hp_dvd_gap hWieferich
  ...
```

ここで本当に必要なのは、
**Wieferich 条件と right boundary core の存在をどう接続するか**
そこだけじゃ。

### 6.2. ordinary 側との差分を見る場所

この段階になると、ordinary reference theorem との差分もかなり見やすい。

ordinary 側は主に

$$
\neg p \mid (z-y)
$$

で進む。
exceptional 側は

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

で進む。

つまり差分は、もう完全に **例外枝専用の arithmetic / CFBRC 入力** に押し込まれた。
ここを局所補題として切ればよい。

### 6.3. split theorem 全体はもう忘れてよい

これは重要じゃ。
今後の concrete 証明では、`CFBRCBoundaryCorePrimeExistenceOnSplitTarget` 全体を返す必要はない。
right branch supply だけでよいし、さらに今はそれを boundary-normalized 形で返せばよい。

## 7. 総括

今回の差分を総括すると、

**proof file の本当の新数学が、pack を含む target から boundary-normalized exceptional statement へ押し込まれた。
よって次に直接書くべき concrete theorem は、`ExceptionalBoundaryDataRightBranchSupplyTarget` を返すものだと、ほぼ確定した。**

ということじゃ。
ここまで来れば、設計の霧はかなり晴れておる。
あとは、例外枝の arithmetic 核をどう書くか、その一点勝負じゃな。
