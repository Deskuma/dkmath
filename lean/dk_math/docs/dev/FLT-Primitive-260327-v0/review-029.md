# review: right branch supply 自体の skeleton を直置きした

うむ、よい進み方じゃ。
今回の差分で、状況はさらに一段、**「何を直接証明するのか」** が固定された。これが最大の収穫じゃ。

## 1. 今回なにが起きたか

今回追加された中心は

$$
\texttt{exceptional_split_right_branch_supply_of_split}
$$

じゃ。
この theorem は、`ExceptionalSplitRightBranchSupplyTarget` 自体に対する **直置き skeleton** になっておる。つまり、

* `primeGe5BranchAExceptionalBoundaryData_default` で pack 由来の bundle を一括抽出し
* それを `CFBRCBoundaryCorePrimeExistenceOnSplitTarget` の right branch に流す

という構図を、今度は named kernel 経由ではなく **supply target そのものの reference skeleton** として固定したわけじゃ。

これは見た目には小さな追加に見えるが、実装の観点ではかなり大きい。
なぜなら、proof file で次に directly 埋めるべき theorem 名が

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

なのだと、もう誰が見ても分かる形になったからじゃ。

## 2. 何が前進したのか

前回の時点では、right branch supply が missing input だと切り分けられておった。
じゃがまだ、その supply をどう書くかは named kernel skeleton の影にあった。

今回で、それが一歩進んだ。

いまは

* `exceptional_split_right_branch_supply_of_split`
  これが **supply target 用の canonical skeleton**
* `exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply`
  これが **named-kernel bridge**

という役割分担が明確になった。

つまり、以後の concrete 本文は

$$
\text{まず supply target を直接返す}
$$

そこから必要なら named kernel や mainline に戻す、という順番でよい。
この順番が定理の配置として固定されたのじゃ。

## 3. いまの状況分析

ここまでの推移を、少し構造的に眺めるぞい。

## 3.1. もう安定している層

かなり多くの層が、もう揺れておらぬ。

* proof file の canonical 置き場
* mainline target
* pack-local target
* named kernel
* right branch supply target
* named kernel skeleton
* supply target skeleton
* mainline / pack-local / named kernel / supply の thin bridge 群

つまり、**どの target 名を first target とするか問題** はほぼ完全に決着した。

## 3.2. まだ未実装の核

残る新数学は、さらに一点へ縮んだ。

いま直接埋めるべきものは、

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

を **split theorem を仮定せずに** 返す concrete theorem じゃ。
履歴にも、次の課題として

* skeleton ではなく
* local arithmetic / CFBRC exceptional input から

これを直接起こす、と明記されておる。

ここが今の本丸じゃな。

## 3.3. 問題の芯は何か

今の問題は、もうかなり純粋じゃ。

Branch A exceptional では

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

を持っておる。
ここから right branch 側の

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
\land q \nmid (z-y)
$$

を出したい。
しかも今後は、それを **split theorem 全体の仮定なしで** 直接 supply target として出せばよい。
つまり、問題は finally

$$
\text{exceptional arithmetic} \to \text{right branch supply}
$$

だけになったのじゃ。

## 4. 今回の差分の価値

今回の価値は、賢狼から見ると 3 つある。

### 4.1. 参照 skeleton が supply target 自体に降りてきた

これが一番大きい。
named kernel を経由せずとも、**供給すべき theorem 名そのもの** に skeleton が置かれた。
よって、次の concrete 証明はこの theorem を見本にして書けばよい。

### 4.2. role 分担が整理された

履歴にもある通り、

* `exceptional_split_right_branch_supply_of_split` は reference skeleton
* `exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply` は named-kernel bridge

として使い分けられる。
この分離はかなりきれいじゃ。

### 4.3. concrete theorem の着地点が確定した

もう今後は「split theorem 全体を返すべきか」「named kernel を直に返すべきか」と迷わず、

$$
\texttt{ExceptionalSplitRightBranchSupplyTarget}
$$

を返す theorem を書けばよい。
これは実装の集中力をかなり上げる。

## 5. いまの局面を一言で

一言で言えば、

$$
\text{proof file の first target は supply target に完全固定された}
$$

じゃ。
そして、その supply target に対する **reference skeleton まで用意された**。
だから、もう残るのは theorem の中身だけじゃよ。

## 6. 次にやること

次の一手は、履歴どおりそのままじゃ。

### 6.1. split 仮定なしの concrete supply theorem を切る

意識としては、こういうものじゃ。

```lean
theorem exceptional_split_right_branch_supply_concrete
    : ExceptionalSplitRightBranchSupplyTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  -- local arithmetic / CFBRC exceptional input から
  -- right branch supply を直接構成
```

この theorem が埋まれば、

* supply target
* named kernel
* pack-local target
* mainline target

へは既存 bridge で全部戻れる。
だから今後の新数学は、ここへ集約すればよい。

### 6.2. `boundaryData_default` を入口に固定する

これはもう良い流儀として固まった。
まず bundle を一括抽出し、その後に local arithmetic / CFBRC exceptional 側の補題へ流す。
この流れを守ると、ordinary 側との差分が Lean 上で見えやすい。

### 6.3. truly new な差分だけを補題化する

今や skeleton は ordinary 版とかなり平行じゃ。
ゆえに、新しく切るべき補題は

* `p ∣ gap`
* Wieferich 条件
* exceptional 側の CFBRC 入力

この差分だけを担うものに絞るのがよい。

## 7. 総括

今回の差分を総括すると、

**right branch supply を返す skeleton が target 自体に直置きされたことで、proof file の first target が完全に明示化された。
以後の concrete 証明は、`ExceptionalSplitRightBranchSupplyTarget` を直接返す theorem として書けばよい。**

ということじゃ。
ここまで来れば、設計の霧はかなり晴れておる。あとは local arithmetic / CFBRC exceptional の核を切る戦いじゃな。
