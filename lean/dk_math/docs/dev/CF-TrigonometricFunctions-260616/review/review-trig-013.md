# Git diff / Report / Review

## Add: docs: Why the CF2D Trigonometric Layer Is Enough

gch: 376761500144787d9b0eac5509e6d7c00b95de7f
cid: 6a342725-99e4-83e8-bb08-58a94e4b1bcc

## Report

論文化用の新規草稿を追加しました。

[CF2D-WhyThisIsEnough-PaperDraft.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md)

主題はそのまま「なぜこれだけで良いのか」です。コンパス・ピンと糸の類比、`rfl` が出る理由、Lean 実装としての相性、Mathlib の `Real.cos` / `Real.sin` を置き換えるのではなく境界モデルとして使う設計、符号感度、Phase 1 が主張しない範囲まで入れています。

`git diff --check` は通っています。docs-only なので Lean build は今回は走らせていません。

## Review

## 1. 総評

D. よ、これはかなり良い草稿じゃ。わっちの判定では、 **研究ノートではなく、短い形式化論文の骨格に到達している** 。

核心は明快じゃ。

\[
Q(x,y)=x^2+y^2
\]

を保存量として置き、

\[
(a,b)\star(x,y)=(ax-by,\;ay+bx)
\]

を定義すると、

\[
Q(r\star z)=Q(r)Q(z)
\]

が純代数で出る。ここから \(Q(r)=1\) の核が \(Q(z)\) を保存し、三角関数の加法定理・倍角・符号反転・回転作用が「解析の奇跡」ではなく、 **保存核の座標射影** として出る、という主張になっておる。資料でも、主定理 `Vec.q2_star` から `UnitKernel`、`KernelFamily`、`cfcos`、`cfsin` を定義し、通常の三角恒等式が代数的帰結として得られる、と整理されている。

これは強い。三角関数そのものを再発明したというより、 **三角関数がなぜこの形の公式を持つのか、その代数的発生源を切り出した** という成果じゃな。

## 2. いちばん重要な発見

今回わかったことは、こう言える。

> 三角関数の座標法則は、実解析より前に、二成分平方質量を保存する積構造から生まれる。

つまり、\(\cos\) と \(\sin\) の本質を最初から「円周」「角度」「弧長」「極限」で定義しなくてもよい。まず

\[
x^2+y^2
\]

を壊さない二成分核を作る。すると、その核の第一座標と第二座標が、三角関数らしい振る舞いをする。

ここがとても DkMath らしい。お主が言っていた「どこから見ても原点に向いている」「膨らみ方に法則がある」という直観が、Lean では

```lean
Vec.q2_star :
  Vec.q2 (Vec.star r z) = Vec.q2 r * Vec.q2 z
```

という一点に凝縮されている。賢狼としても、これは見事な捕獲じゃ。

## 3. `rfl` の意味づけはとても良い

草稿の中で特に良いのは、`realTrigKernelFamily_cfcos` と `realTrigKernelFamily_cfsin` が `rfl` で落ちる理由を、過大主張せず説明している点じゃ。資料では、実数モデルでは `cfcos` と `cfsin` が定義上それぞれ `Real.cos` と `Real.sin` の座標射影になるだけであり、「実三角関数の全解析事実が `rfl` で証明された」わけではない、と明確に区別している。

これは外部読者にとって非常に大事じゃ。

悪い書き方をすると、

> Lean が `rfl` で認めたので三角関数は自明だった

みたいに誤解される。

良い書き方は、今の草稿の通り、

> 実解析は、\((\cos t,\sin t)\) が有効な単位核族であることを保証する。CF2D は、有効な単位核族なら座標公式が一括で従うことを保証する。

じゃな。ここはそのまま大切にしてよい。

## 4. 符号感度の章は論文価値が高い

`badStarPlus` や `badStarMinus` の残差を出している章は、とても良い。単に「この積ならうまくいく」ではなく、「近い別積ではどこが壊れるか」を Lean に記録しているからじゃ。資料でも、符号を変えると

\[
4\,r.core\,r.beam\,z.core\,z.beam
\]

型の残差が現れ、残る保存パターンは共役によって説明できる、と整理されている。

これは研究発表ではかなり効く。

なぜなら、読者は必ずこう思うからじゃ。

> なぜこの符号配置なのか？
> ただ複素数の掛け算を写しただけではないのか？

そこに対して、

\[
(ax-by,\;ay+bx)
\]

だけが交差項を消し、別符号では残差が出る、と見せられる。これは「選んだ」のではなく、 **保存則が符号を選別した** という説明になる。

## 5. 注意すべき過大主張

草稿はすでに自制できているが、タイトルや abstract では少しだけ言い方を絞ると、さらに堅くなる。

今の “recover the usual trigonometric laws” は魅力的じゃが、外部向けには少し強く聞こえる可能性がある。Phase 1 が証明しているのは、資料自身も述べている通り、任意の square-mass-one additive kernel family の座標が三角関数的な代数法則を満たす、ということじゃ。一方で、連続性、微分可能性、周期性、角速度正規化、\(2\pi\) 閉包、点から角度を復元する大域理論はまだ主張していない。

なので外向けには、こう言うのが安全じゃ。

> CF2D recovers the algebraic coordinate laws of trigonometry from square-mass-preserving kernel composition.

日本語なら、

> CF2D は、三角関数の解析的構成ではなく、三角関数型の座標恒等式が生まれる代数的理由を形式化する。

これなら強く、かつ誤解されにくい。

## 6. 論文構成への提案

草稿の章立て案はかなり良い。わっちなら、少しだけ順序を調整する。

まず読者に「これは複素数の再包装ではなく、保存則インターフェイスの抽出である」と伝えるために、導入直後に次の対比を置くとよい。

```text
Classical view:
  sin and cos are analytic functions, then rotation laws are proved.

CF2D view:
  square-mass-preserving kernel composition is defined first,
  then trigonometric coordinate laws are projected from it.
```

その後で、

1. `Vec` と `q2`
2. `star`
3. `q2_star`
4. `UnitKernel`
5. `KernelFamily`
6. `cfcos`, `cfsin`
7. real model
8. sign sensitivity
9. limitations

という流れが美しい。

特に `KernelFamily` の説明は早めに置くべきじゃ。資料でも `kernel : T -> UnitKernel R`, `map_zero`, `map_add` が明示され、Phase 1 の三角公式はこの interface の下流にある、と述べられている。 ここが読者の理解の橋になる。

## 7. DkMath 的な解釈

DkMath の語彙で言えば、今回の CF2D はこうじゃ。

```text
Vec.q2
  = 二成分平方質量

UnitKernel
  = q2 = 1 の単位核

star
  = 質量を乗法的に運ぶ合成則

KernelFamily
  = 加法パラメータから単位核への保存写像

cfcos / cfsin
  = 単位核族の Core / Beam 座標
```

つまり、三角関数とは、

\[
\text{保存核族の Core/Beam 観測}
\]

じゃ。

これはかなり大きい。なぜなら、今後の宇宙式、PowerSwap、積分宇宙式、量子位相の話へ接続するとき、\(\cos\)、\(\sin\) を「既成の解析関数」としてだけでなく、 **保存量を壊さない核の座標** として扱えるからじゃ。

## 8. 次に足すと良いもの

今の Phase 1 は十分に発表可能じゃ。ただし、次の一手としては、次の三つが効く。

第一に、 **可換環上でできること** と **実数上でしか言えないこと** の表を入れるとよい。

| 層 | 必要構造 | 得られるもの |
|---|---|---|
| 代数層 | commutative ring | `q2_star`, 加法定理型公式 |
| 単位核層 | \(Q(r)=1\) | 平方質量保存 |
| additive family 層 | parameter addition | `cfcos`, `cfsin` の加法公式 |
| 実数モデル層 | Mathlib の `Real.cos`, `Real.sin` | 標準三角関数との同定 |
| 解析層 | 連続性・微分・周期性 | 将来課題 |

第二に、 **これは複素数の乗法と同型である** ことを隠さず、しかし主張の焦点をずらさぬことじゃ。

> もちろん構造は複素数乗法の実二成分表示と同型である。しかし CF2D の貢献は、その構造を Lean 上で square-mass preserving kernel interface として切り出し、任意モデルへ一括適用できる形にした点にある。

この一文があると、数学者の「それ複素数では？」という反応を先回りできる。

第三に、将来章として **angle reconstruction** を置くとよい。今は角度を前提にしていないので、次は

\[
Q(x,y)=1
\]

上の点から、どの条件で \(t\) を復元できるか、という問題になる。ここが \(2\pi\) 閉包、周期性、atan2、位相、実解析へつながる道じゃな。

## 9. 最終評価

わっちのレビュー結論はこうじゃ。

**CF2D Phase 1 は、三角関数の「解析的構成」ではなく、「座標恒等式の代数的発生源」を Lean で切り出した成果である。**
そして、その切り出しは十分に意味がある。なぜなら、いったん `KernelFamily` という保存インターフェイスを得れば、三角恒等式は実数三角関数に閉じず、任意の square-mass-preserving additive unit-kernel family に対して再利用できるからじゃ。

これは小さい実装に見えて、実は良い抽象化じゃ。
小麦の粒は小さくとも、畑を満たすのは粒の法則じゃからの。今回ぬしが掴んだのは、三角関数という畑を実らせる **保存核の種** じゃ。

## Diff

※差分省略、全文は以下より

[CF2D-WhyThisIsEnough-PaperDraft](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-WhyThisIsEnough-PaperDraft.md)
