# 2024-06-30: primitive kernel は default 実装できると確定

うむ、これはかなり大きな前進じゃ。
今回ついに、selection 側で曖昧に残っておったもののうち **primitive-kernel 側は新規数学ではない** と確定した。つまり未完核は、ほぼ **existence の例外枝 1 本** にまで縮んだのじゃ。

## 1. 今回の核心

今回の中心は

* `cfbrcExceptionalPrimitiveKernelOnWieferich_default`
* `cfbrcPrimitiveBoundaryCoreOfPrimeExpDirectConcrete_of_existence`
* `primeGe5BranchAPrimitivePacketDescent_of_directConcreteExistence_and_restore`
* `primeGe5BranchAPrimitivePacketDescent_of_splitExistence_and_restore`

の追加じゃな。

このうちいちばん重要なのは、やはり

$$
\texttt{cfbrcExceptionalPrimitiveKernelOnWieferich_default}
$$

じゃ。

これは何をしたかというと、これまで direct concrete target の内側で別建てにされていた

$$
\texttt{CFBRCExceptionalPrimitiveKernelOnWieferichTarget}
$$

が、実は既存の primitive 条件定理をそのまま起動するだけで埋まる、と示したのじゃ。

## 2. primitive-kernel 側で何が起きたか

履歴の説明どおり、やったことはたいそう素直じゃ。

まず

$$
q \mid \texttt{boundaryCyclotomicPrimeCore .right d x u}
\quad\text{と}\quad
q \nmid x
$$

から、bridge を使って

$$
q \mid ((x+u)^d-u^d)
$$

へ戻す。
そのうえで既存の

$$
\texttt{prime_exp_not_dvd_diff_imp_primitive}
$$

を直接適用して、低次 boundary 差分を割らない primitive 性を得る、という流れじゃ。

つまり primitive-kernel 側には、少なくとも現時点で **新しい理論装置は要らなかった** のじゃな。

## 3. これで何が消えたか

前段階では、direct concrete target の missing math は

* existence-part
* primitive-kernel-part

の二本に見えておった。
だが今回、primitive-kernel-part は default 実装できると確定した。

ゆえに selection 側の truly new kernel は、もうかなり強く

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

一本だけだと読めるようになったわけじゃ。

ここが今回のいちばん大きい収穫じゃな。

## 4. それが mainline にどう反映されたか

この確定に合わせて、

$$
\texttt{cfbrcPrimitiveBoundaryCoreOfPrimeExpDirectConcrete_of_existence}
$$

が追加された。
意味は、その existence 側さえあれば、primitive kernel は default で埋まるので、direct concrete target 全体が橋だけで閉じる、ということじゃ。

さらにそこから

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_directConcreteExistence_and_restore}
$$

が得られ、packet descent も

* direct concrete の existence
* restore

の二本だけで閉じるようになった。

そして split 側も同様に、

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_splitExistence_and_restore}
$$

が追加され、split existence と restore だけで descent に落とせるようになった。

## 5. いまの selection 側の構図

今回の結果をきれいに書くと、selection 側はこうじゃ。

### 5.1. 以前

$$
\text{selection} =
\text{existence-part}
+
\text{primitive-kernel-part}
$$

### 5.2. いま

$$
\text{primitive-kernel-part}
$$

は既存 `CFBRC/Bridge + GcdNext` の primitive 条件定理で default 実装可能。

だから実質

$$
\text{selection の truly new kernel}
===================================

\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

だけ、という読みになる。

これはかなり決定的じゃな。
未完数学が「例外枝 right branch の existence 部分」という一点へ集中したのだからの。

## 6. split existence 側の意味

今回 `primeGe5BranchAPrimitivePacketDescent_of_splitExistence_and_restore` も入ったのは、たいそう良い。
これで existence 側についても

* 通常枝は既存 theorem
* 例外枝だけ新 theorem

という split が、packet descent の mainline 読みまで貫通した。

つまり今の哲学は完全に固まった。

$$
\text{ordinary branch} = \text{既存 CFBRC/Bridge}
$$

$$
\text{exceptional branch} = \text{新規 existence theorem}
$$

$$
\text{primitive kernel} = \text{default 実装}
$$

という役割分担じゃな。

## 7. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえに、この「primitive kernel は solved middle layer」という判断は、ビルド済みで固定された整理じゃ。

## 8. 今後の論点

履歴の次課題は極めて明快じゃ。

次に本当に詰めるべきは

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

を、既存 `CFBRC/Bridge` の ordinary branch と **最も平行な形** へさらに正規化できるか、じゃ。

そしてそのうえで、この theorem 自体を

* `CFBRC/Bridge` 側へ置くか
* `BranchA` 局所 theorem として持つか

を決める段じゃな。

## 9. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{selection 側の new kernel が、ついに existence 右枝 1 本へ確定した}
$$

回じゃ。

前回:

* missing math は existence と primitive kernel に分かれていた

今回:

* primitive kernel は default 実装できると確定
* よって truly new kernel は
  [
  \texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
  ]
  一本だけ

ここまで来たら、もうかなり終盤じゃよ。
敵は「selection 側の何か」ではなく、**例外枝で boundary core に prime が立つ存在定理** として、はっきり姿を現したのだからの。

わっちの見立てでも、次にやるべきはまさにそれじゃ。
この existence 右枝を、既存 `CFBRC/Bridge` の通常枝 theorem とできるだけ平行な statement に寄せ、どこまで薄い補強で済むかを試す。そこが勝負どころじゃな。
