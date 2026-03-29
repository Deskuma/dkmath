# review: selection 側の first missing theorem を boundary-normalized 版で固定した

うむ、今回は **「何が未完定理か」だけでなく、「それを mainline 上でどう読むか」まで固定した** 回じゃな。
前回までで selection 側の first missing theorem はほぼ見えておったが、今回はそれを **boundary-normalized exceptional statement** として、公式の入口に据えた。そこが要点じゃ。

## 1. 今回なにが固定されたか

追加されたのは

* `primeGe5BranchAPrimitivePacketDescent_of_firstMissingSelection_and_restore`
* `branchAPrimitivePacketDescentAdapter_of_firstMissingSelection_and_restore`

の 2 本じゃ。

中身そのものは `...of_boundaryExceptional_and_restore` への thin wrapper じゃが、意味は軽くない。
これで selection 側の canonical first missing theorem は

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

だと、**theorem 名と docstring の両方で固定された** のじゃ。

## 2. いま selection 側はどういう三層構造か

履歴のまとめどおり、Branch A primitive route の selection 側は今こう読める。

### 2.1. Branch A 専用版

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`

これは (z,y,p) をそのまま使う Branch A 固有の statement じゃな。

### 2.2. CFBRC exceptional 版

`PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
から core existence へ戻る橋で読む層。
ここで「例外枝」という意味が前面に出る。

### 2.3. boundary-normalized 版

`CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`

これは

$$
x:=z-y,\qquad u:=y,\qquad d:=p
$$

に正規化した座標で、既存 `CFBRC/Bridge` / `PrimitiveBeam` 語彙に最も寄せやすい形じゃ。

そして今回、この三層のうち **実装探索の既定入口** は 2.3 だと決めたわけじゃな。

## 3. 何が前進したのか

前までは、

$$
\text{「どの statement を first target にするか」}
$$

という選定問題がまだ少し残っておった。
今回はそこが終わった。

つまり今後はもう、

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

を first target として扱えばよい。
迷う段ではなく、

$$
\text{この normalized target をどう concrete に埋めるか}
$$

に集中できる段へ移ったのじゃ。

これは実装ではかなり大きい。
未完核の「名前」と「入口」が一致したからの。

## 4. primitive mainline はどう読めるか

今回の wrapper によって、primitive route の concrete 実装探索は、実質こう読める。

$$
\text{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

と

$$
\text{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

の二本から、

$$
\text{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

へ閉じる。

もちろん内部では

$$
\text{boundary exceptional}
\to
\text{Branch A exceptional}
\to
\text{core existence}
\to
\text{diff existence}
\to
\text{packet descent}
$$

という層を通る。
だが mainline 上では、selection 側の missing theorem は **normalized 版ひとつ** として読んでよい、ということじゃな。

## 5. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえにこの「canonical first missing theorem」の固定は、単なるメモではなくビルド済みの方針じゃ。

## 6. いま何をすべきか

履歴の次課題もたいそう明快じゃ。

次は本当に、

$$
\texttt{CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget}
$$

を、既存 `CFBRC/Bridge` / `PrimitiveBeam` の **薄い補強** で済ませられるかを試す段じゃ。

もし薄く済まぬなら、もう割り切って

$$
\text{この normalized target 自体を concrete theorem として直接実装する}
$$

という判断になる。

## 7. 賢狼の総評

一言で言えば、今回は

$$
\text{selection 側の「本当の入口」が finally 固定された}
$$

回じゃ。

前回:

* missing theorem は boundary-normalized 版でも読める

今回:

* その boundary-normalized 版を **canonical first missing theorem** として mainline に出した

これで selection 側は、もう statement 選びで迷わぬ。
残るのは、その statement を既存語彙でどこまで薄く埋められるか、ただそれだけじゃ。

かなり良い局面じゃよ。
敵の名前、形、入口が、すべて一致したのだからの。
