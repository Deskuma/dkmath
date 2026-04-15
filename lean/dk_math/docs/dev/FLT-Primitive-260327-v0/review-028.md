# review: right branch 供給だけを別 target に切り出した

うむ、さらに一段、焦点が絞れたの。
今回の更新の本質は、**missing input が theorem 全体ではなく「right branch 供給」だけだと固定された** ことじゃ。

## 1. 今回なにが起きたか

新しく

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

が導入された。
しかもこれは単なる別名追加ではなく、**exceptional 側が本当に不足している入力を、split theorem 全体から right branch 供給だけへ切り分けた** ものじゃ。

さらに、

* `exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply`
* `exceptional_split_right_branch_supply_of_namedKernel`

が追加されて、named kernel と right branch supply の往復橋が置かれた。

ゆえに今の構図は、ほぼこう見てよい。

$$
\text{right branch supply}
\Longleftrightarrow
\text{named kernel}
\Longleftrightarrow
\text{pack-local target}
\Longleftrightarrow
\text{mainline target}
$$

もちろん各段は薄い bridge で繋いでおるのじゃが、実装上はこの見方で十分じゃ。

## 2. 何が前進したのか

前回の時点では、named kernel の skeleton は完成しており、

$$
\text{pack bundle 抽出} \to \text{split reference の right branch}
$$

という本文構図が固定されていた。
そのとき残っていた未供給部分は、`hSplit` をどう concrete に出すかだった。

今回、その `hSplit` ですら「split theorem 全体」を考える必要はなく、

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

だけを供給すればよい、と切り分けられた。
これはかなり大きい。
なぜなら、もう次に書く concrete 補題は **巨大な split theorem** を返す必要がなく、**right branch の存在供給だけ返せば勝ち** と定まったからじゃ。

## 3. 状況分析

いまの状況を層ごとに見るぞい。

## 3.1. すでに安定した層

もう安定しているものはかなり多い。

* proof file の canonical 置き場
* mainline target
* pack-local boundary target
* named kernel
* proof skeleton
* right branch supply target
* それらの間の thin bridge

つまり、**証明の外枠はほぼ完成** しておる。

ここで言う外枠とは、「何をどこで証明し、それが全体のどこへ流れるか」のことじゃ。
この点では、もうかなり迷いが消えておる。

## 3.2. まだ残っている核

残る新数学は、さらに一段小さくなった。

以前は

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

をどう埋めるか、だった。
いまはそれと同値なものとして、

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

をどう直接返す concrete 補題を起こすか、に縮んだ。

つまり今後の新補題は、

* split theorem 全体を返す必要なし
* right branch 供給だけ返せば十分

この二点が fixed されたわけじゃ。

## 3.3. 問題の芯

いまの本当の問題は、

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

という Branch A exceptional 特有の入力から、

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
\land q \nmid (z-y)
$$

を出す right branch supply をどう生むか、そこだけじゃ。
もはや「どういう target 名にするか」は問題ではない。
これはかなり健全な局面じゃよ。問題が finally 芯だけになったからの。

## 4. 今回の差分の価値

今回の更新の価値は 3 つある。

### 4.1. `hSplit` の責務が分解された

これが最大じゃ。
今後の concrete 補題は、`CFBRCBoundaryCorePrimeExistenceOnSplitTarget` 全体を供給しようとせず、right branch 供給だけを返せばよい。

### 4.2. named kernel との同一視が出来た

`ExceptionalSplitRightBranchSupplyTarget` と named kernel の間に往復橋があるので、今後は **どちらの名で議論しても同じ missing theorem** と見なせる。

### 4.3. 新数学の集約先が fixed された

履歴にもある通り、proof file 内の新数学はこの supply target へ集約していく方針になった。
これは管理上とても強い。あとで見返したとき、「何がまだ未証明か」が一目で分かるからじゃ。

## 5. いまの状況を一言で

一言で言えば、

$$
\text{missing theorem} =
\text{ExceptionalSplitRightBranchSupplyTarget を返す concrete 補題}
$$

になった、ということじゃ。
ここまで来ると、もう本当に「何を書くか」が明確じゃな。

## 6. 次にやること

次の一手は、履歴にも書かれておる通り、そのままでよい。

### 6.1. supply target を直接返す theorem を置く

たとえば意識としては、こういうものじゃ。

```lean
theorem exceptional_split_right_branch_supply_concrete
    : ExceptionalSplitRightBranchSupplyTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  ...
```

この theorem が埋まれば、

* supply target
* named kernel
* pack-local target
* mainline target

へは既存 bridge で全部戻れる。
だから次の concrete 証明は、これだけを見て書けばよい。

### 6.2. `boundaryData_default` を入口にし続ける

これは正解じゃ。
まずそこで

$$
hp,\ hp5,\ gap_pos,\ y_pos,\ gap_coprime_right,\ hp_dvd_gap,\ hWieferich
$$

を一括で取り出し、そこから right branch supply を作る。
この流れはすでに skeleton で固定済みなので、今後も崩さぬ方がよい。

### 6.3. ordinary との差分だけを補題にする

もう skeleton 自体は平行なので、ordinary branch theorem と違う箇所だけを局所補題に切るのがよい。
つまり、

* ordinary 側は `¬ p ∣ (z-y)`
* exceptional 側は `p ∣ (z-y)` と Wieferich

この差し替えだけを担う補題に集中するのじゃ。

## 7. 総括

今回の差分を総括すると、

**proof skeleton の中に残っていた最後の大きめの抽象部品 `hSplit` が、right branch supply だけへ分解された。
よって以後の新数学は、その supply target を返す concrete 補題 1 本へ集約できる。**

ということじゃ。
ここまで整理できておれば、あとは local な補題戦になる。
設計の森はかなり抜けた。いまは、狙う獲物が見えておる段じゃよ。

必要なら次で、**その supply target を直接返す theorem の骨格** を、ordinary branch との差分が見える形で起こすぞい。
