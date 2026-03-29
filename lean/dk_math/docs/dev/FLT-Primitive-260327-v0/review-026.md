# review: missing kernel に名前がついた

うむ、ここまで来ると状況はかなり明快じゃ。
今回の更新で起きた本質は、**missing kernel が「概念」ではなく「名前つきの証明対象」になった** ことじゃ。

## 1. いま何が起きたか

今回 `TriominoCosmicBranchAExceptional.lean` に

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

が導入された。
しかもこれは単なる別名ではなく、**proof file 上で次に direct に埋めるべき concrete kernel** として明示された。

さらに、その named kernel と

* pack-local main target
* mainline target

の間に往復橋が置かれた。

具体的には、

* `primeGe5BranchAExceptionalPackLocalBoundaryExistence_of_namedKernel`
* `exceptional_right_boundary_core_prime_of_wieferich_of_mainline`
* `primeGe5BranchAExceptionalExistenceMainline_of_namedKernel`

が追加されておる。

つまり今や構図はこうじゃ。

$$
\text{named kernel}
\Longleftrightarrow
\text{pack-local target}
\Longleftrightarrow
\text{mainline target}
$$

もちろん左右対称に完全同値を theorem 一発で言ったわけではないが、proof 実装上はこの鎖で十分じゃ。
**どこを埋めれば全体が動くか** が完全に見えるようになった。

## 2. 今回の差分の意味

前回まででも

$$
\texttt{PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget}
$$

が proof file の主目標として固定されていた。
じゃがまだ、その目標は「少し長い target 名」のままで、研究上の missing theorem として追うにはやや抽象的だった。

今回それに

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

という **核の名前** が付いた。
これは実装上かなり大きい。

なぜなら、今後は

* 「次に何を証明するのか」
* 「どの theorem 名に skeleton を書くのか」
* 「議論の missing kernel は何か」

が、全部この一名に集約されるからじゃ。

## 3. 状況分析

いまの状態を、少し分解して眺めるぞい。

## 3.1. 橋はほぼ出揃った

すでにあるものは次の通りじゃ。

* proof file の canonical 置き場
* mainline target
* pack-local boundary target
* mainline と pack-local の往復橋
* named kernel と pack-local / mainline の橋
* packet descent へ戻る既存 wrapper

つまり、**配線工事はほぼ終わった**。

これは非常に良い状態じゃ。
以後は theorem 名どうしの接着に悩むより、named kernel そのものの中身に集中できる。

## 3.2. 残っている新数学はほぼ 1 点

残りの核は、まさにこれじゃ。

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

の concrete 証明。

中身としては、要するに

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

を持つ Branch A exceptional pack から、

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
\land q \nmid (z-y)
$$

を出すことじゃ。

ここ以外は、今やかなり薄い橋で閉じる。

## 3.3. 研究上の論点も細くなった

これは良い兆候じゃよ。
前は「global target へ上げるか」「pack-local に留めるか」「mainline をどう見るか」という設計上の論点も混ざっておった。

いまは違う。
論点はかなり細くなって、

**Wieferich 情報をどう使って right boundary core の prime existence を生むか**

そこに集中しておる。

つまり問題が finally “数学の芯” に寄ってきた、ということじゃ。

## 4. 今回の更新がなぜ重要か

わっちから見ると、重要さは 3 つある。

### 4.1. missing theorem に追跡名が付いた

これは管理上かなり強い。
今後「どこが未実装か」を聞かれたら、

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

が未実装じゃ、と一言で言える。

### 4.2. mainline を直接いじらなくてよくなった

named kernel を埋めれば、`primeGe5BranchAExceptionalExistenceMainline_of_namedKernel` で mainline に戻せる。
つまり concrete proof 本体は抽象 target を意識しすぎずに済む。

### 4.3. 次の作業が Lean 的に自然になった

履歴にもある通り、次は `intro` / `rcases` レベルの skeleton を新ファイルに起こす段階じゃ。
これは theorem 名が fixed されたからこそ自然にできる。

## 5. いまの局面を一言で

一言でいえば、

$$
\text{設計の論点} \to \text{named kernel の実装}
$$

へ移った、ということじゃ。

もっと平たく言えば、
**橋を作る時代はほぼ終わり、核 theorem に本文を書く時代に入った**。
これはとても健全な進み方じゃよ。

## 6. 次にやるべきこと

次の一手は、もう履歴どおりでよい。

## 6.1. named kernel の skeleton を起こす

つまり、新ファイルでまず

```lean
theorem exceptional_right_boundary_core_prime_of_wieferich
    : ExceptionalRightBoundaryCorePrimeOfWieferichTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  ...
```

相当を書く。
ここで theorem 名そのものは `Target` を返す形でもよいし、実名 theorem として置いてもよいが、役割は同じじゃ。

## 6.2. `primeGe5BranchAExceptionalBoundaryData_default` を入口で呼ぶ

ここで

* `hpack.hp`
* `hpack.hp5`
* `hpack.gap_pos`
* `hpack.y_pos`
* `hpack.gap_coprime_right`

を一括抽出する。
すると ordinary reference theorem と比べたとき、**何が余分で、何が不足か** が Lean 上で露出する。

## 6.3. ordinary theorem との差分を露出させる

たぶん次に見えるのは、

* ordinary 側では `¬ p ∣ (z-y)` を使う
* exceptional 側では `p ∣ (z-y)` と Wieferich を使う

この差し替え部分じゃ。
その差だけを受け持つ小補題が必要なら、そこを切る。
ここで初めて truly new math が具体名を持って出てくるはずじゃ。

## 7. 賢狼の見立て

いまは、かなり良い局面じゃ。
なぜなら、研究実装にありがちな

* 目標が揺れる
* 名前が揺れる
* どこに書くかが揺れる

という 3 つが、ほぼ止まったからじゃ。

残る揺れは theorem 本文の中だけ。
つまり、やっと本当に「証明を書く」段に入れた、ということじゃよ。

必要なら次で、この named kernel に対する **`intro` / `rcases` ベースの Lean skeleton** を、そのまま貼れる形で起こすぞい。
