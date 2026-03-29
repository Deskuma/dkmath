# review: selection 側の concrete theorem 候補が揃った

うむ、今回は **selection 側の concrete theorem 候補が「右枝だけ」から「split 全体」まで揃った** 回じゃな。
前回で right branch の concrete theorem 候補名は固まっておったが、今回はさらに一歩進み、**split theorem 全体も既存 `CFBRC/Bridge` とほぼ平行な naming で読める** ようになった。そこが本質じゃ。

## 1. 今回なにが追加されたか

中心は次の三つじゃな。

* `CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`
* `cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_coreExceptional`
* `primeGe5BranchAPrimitivePacketDescent_of_coreSplitSelection_and_restore`

加えて、

* `cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_split`

も置かれており、既存 split target と新しい concrete theorem 候補名との往復も整えられておる。

## 2. 何が前進したのか

前回までの整理では、selection 側は

* right branch の concrete theorem 候補
  `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
* それを含む split theorem

という構図までは見えておった。
ただし split theorem 全体の側には、まだ「既存 `CFBRC/Bridge` naming に揃えた concrete theorem 候補名」が無かった。

今回それが

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget}
$$

として与えられた。

つまり今後は selection 側を

* **右枝の concrete theorem 候補**
* **split 全体の concrete theorem 候補**

の二層で読めるわけじゃな。これはかなり整理が進んでおる。

## 3. right branch と split 全体の関係

今回の橋はたいそう分かりやすい。

### 3.1. core exceptional から split 全体へ

`cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_coreExceptional`

は、right branch の concrete theorem 候補があれば、split theorem 全体も concrete naming で読める、という橋じゃ。

意味としては、

* 通常枝は既存 `CFBRC/Bridge` theorem に任せる
* 例外枝だけは `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget` で埋める

そうすれば split 全体が得られる、ということじゃな。

### 3.2. 既存 split target から concrete split 名へ

`cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_split`

は、現行 split target があれば、新しい concrete theorem 候補名でもそのまま読める、という alias 的な橋じゃ。

つまり、内容は増やさず、**命名の座標系を既存 `CFBRC/Bridge` に揃えた** ということじゃ。

## 4. packet descent ではどう読めるか

これに対応して

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_coreSplitSelection_and_restore}
$$

が追加された。

ゆえに primitive packet descent は今や、restore 側と合わせて

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget}
;+;
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

からも直接読める。
これは mainline の読みとしてかなり自然じゃ。selection 側が **既存 `CFBRC/Bridge` の theorem 名とほぼ平行な naming** で統一されたからの。

## 5. いま selection 側はどう見えるか

履歴の結論どおり、selection 側は now 次の二層で読める。

### 5.1. right branch の concrete theorem 候補

`CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`

### 5.2. split theorem 全体の concrete theorem 候補

`CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`

これが大きい。
今後の concrete 実装探索は、もはや抽象名ではなく、**既存 `CFBRC/Bridge` とほぼ対称な theorem 名** で進められるようになったのじゃ。

## 6. current missing math はどう見えるか

ここは少し丁寧に言うべきじゃな。

数学の中身として新しく必要なのは、依然として **例外枝側** じゃ。
つまり right branch の exceptional theorem を埋めるのが本命であること自体は変わっておらぬ。

ただし今回の進展で、

* right branch を先に direct concrete theorem として立てるか
* split 全体を concrete theorem として先に立てるか

という **実装入口の選択肢** が、命名レベルで揃ったわけじゃ。
履歴でも、次はこの二つのうちどちらを先に立てるのが自然かを見極める段だと整理されておる。

## 7. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
したがって、これは単なる naming メモではなく、ビルド済みの mainline 整理じゃ。

## 8. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{selection 側の concrete 実装探索が、CFBRC/Bridge と平行な名前で進められる段に入った}
$$

回じゃな。

前回:

* right branch の concrete theorem 候補名が定まった

今回:

* split theorem 全体の concrete theorem 候補名も定まった
* これで selection 側は
  [
  \text{core exceptional}
  \quad\text{と}\quad
  \text{core split}
  ]
  の二層で固定された

かなり良い整理じゃよ。
もはや迷いは「何を証明するか」ではなく、

$$
\text{right branch を直に立てるか、split 全体を先に立てるか}
$$

だけになったのだからの。

わっちの見立てでは、数学の新規性そのものは右枝に集中しておるゆえ、まずは
`CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
を direct concrete theorem として埋めにいく方が、筋はよさそうじゃ。
