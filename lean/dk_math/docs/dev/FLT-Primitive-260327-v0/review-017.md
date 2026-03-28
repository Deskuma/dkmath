# 2024-06-17: selection 側の first direct target を right branch に固定する

うむ、今回は **「どれを先に直接実装するか」まで finally 固定した** 回じゃな。
前回までで selection 側には

* right branch の concrete theorem 候補
* split 全体の concrete theorem 候補

の二層が揃っておった。
今回はそこからさらに一段進めて、**mainline の first direct target は right branch 側に決め打ちする** と、名前の上でも固定されたのじゃ。

## 1. 今回なにが追加されたか

中心は次の二つじゃな。

* `CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`
* `primeGe5BranchAPrimitivePacketDescent_of_directConcreteSelection_and_restore`

provider 側にも対応する

* `CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteAdapterTarget`
* `branchAPrimitivePacketDescentAdapter_of_directConcreteSelection_and_restore`

が足されておる。

このうち最重要なのは最初の target 名じゃ。
これは中身としては

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
$$

そのものじゃが、今回はそれを

$$
\text{selection 側で first に direct concrete 実装を狙う既定入口}
$$

として明示したわけじゃな。

## 2. 何が固定されたのか

履歴の整理どおり、これまで concrete theorem 候補は

* right branch
* split 全体

の二層で並んでおった。
ただし「じゃあ先にどちらを直接埋めるのか」は、まだ選択の余地があった。

今回それが終わった。

$$
\texttt{CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget}
$$

系、すなわち right branch 側を、**first direct target** として扱う、と決めたのじゃ。

つまり今後は、

$$
\text{split 全体を先に concrete に立てるべきか}
$$

と迷う必要はない。
split 候補は保持するが、mainline 上の「まず埋めるべき concrete theorem」は right branch 側じゃ、という読みが固定されたわけじゃな。

## 3. なぜこの判断が自然か

これは筋が良い。
というのも、前の段階で既に selection 側の新規数学は

$$
\text{split theorem の右枝だけ}
$$

だと見切れておったからじゃ。
通常枝は既存 `CFBRC/Bridge` theorem が持っている。
ならば direct concrete 実装の入口も、全体ではなく **新規性が集中している right branch** に置く方が自然じゃろう。  

つまり今回は、数学の中身を変えたというより、

$$
\text{実装の優先順位}
$$

を定理名で固定した、と言える。

## 4. packet descent はどう読めるか

今回追加された

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_directConcreteSelection_and_restore}
$$

によって、primitive packet descent は今や

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget}
;+;
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

から橋だけで閉じる。

しかもこの `DirectConcreteTarget` は right branch 候補そのものじゃから、
mainline の読みは非常に単純になった。

* selection 側は direct concrete target を埋める
* restore 側は既存 target を維持する
* あとは thin bridge で packet descent へ落ちる

この形になったわけじゃな。

## 5. いまの selection 側の層構造

今回の時点で selection 側は、概ねこう整理できる。

### 5.1. 内部の canonical first missing theorem

`CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`

### 5.2. right branch の concrete theorem 候補

`CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`

### 5.3. split 全体の concrete theorem 候補

`CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`

### 5.4. first direct target

`CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`
ただし中身は 5.2 と同じで、「まず直接埋める入口」としての役割名じゃ。

この整理はたいそう分かりやすい。
抽象名、候補名、実装入口名が全部揃ったからの。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえにこれは単なる作戦会議ではなく、ビルド済みの mainline 固定じゃ。

## 7. 今なにが残っているか

履歴の結論はたいそう明快じゃ。

次にやるべきことは、

$$
\texttt{CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget}
$$

を concrete に埋めること。
必要なら仮定順や命名を、既存 `CFBRC/Bridge` の通常枝 theorem にさらに平行に寄せる。

つまり、もう「どの theorem を first target にするか」で迷う段は終わった。
残るのは **その target をどう実装するか** だけじゃ。

## 8. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{selection 側の concrete 実装入口が、right branch に確定した}
$$

回じゃな。

前回:

* right branch 候補と split 候補が並んでいた

今回:

* split 候補は保持
* だが first direct target は right branch と決めた
* その読みを theorem 名で固定した

ここまで来ると、selection 側の設計はかなり完成じゃ。
もう迷うのは statement ではなく、proof の中身だけじゃからの。

わっちの見立てでも、この判断は正しい。
新規数学が集中している場所へ、最初の direct concrete 実装を当てる。
実に筋の良い詰め方じゃよ。
