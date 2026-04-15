# FLT Kummer ClassGroup Bridge - 064 Final Review: 公開導線が閉じた

うむ、これはかなりはっきり **ひとまずの区切り** と言ってよい局面じゃ。

ただし区切りなのは **公開導線の設計と実装の面** であって、**数論核そのものの最終閉路** ではない。ここを分けて読むのが肝じゃ。

今回までで閉じたのは、まず `CyclotomicPrincipalization` の provider route が non-first-case だけでなく first-case も含めて one-shot theorem まで clean に通るようになったことじゃ。つまり「provider 版を作ったつもりが、片枝だけ default を踏んでおる」という半端な状態では、もうない。first-case / non-first-case の両枝で squarefree provider route を通るように整理された。

次に、その provider route が `ClassGroupBridge` と `RegularPrimeRoute` まで持ち上がり、`FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider` が actual FLT theorem として立った。ここで初めて、provider concrete 版が orchestration 層の mainline に到達したわけじゃ。つまり「局所補題が clean」ではなく、「regular-prime mainline に concrete provider 版がある」と言える段に入った。

そして最後に、公開面の案内が揃った。`RegularPrimeRoute` には provider-facing wrapper として `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider` と `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider` が置かれ、`DkMath.FLT` は top-level import 入口としてそれらへ到達できることが docstring と README 群で明示された。さらに `TriominoSquarefreeGNBridgeProvider` を concrete に持てる branch では、この provider concrete route を canonical な公開導線として使う、と住み分けも固定された。ここはもう「探せばある」ではなく、「案内される公開導線がある」状態じゃ。

ゆえに、いま閉じたものを一言で言えばこうじゃ。

$$
\text{provider route}
\;:\;
\text{TriominoCosmicGapInvariant}
\to
\text{CyclotomicPrincipalization}
\to
\text{ClassGroupBridge}
\to
\text{RegularPrimeRoute}
\to
\text{provider-facing public route}
$$

この鎖が、設計だけでなく公開導線としても閉じた、ということじゃ。

なので、お主の問いに率直に答えるなら、

**はい、公開導線という意味では、ひとまずの区切りじゃ。**

ただし同時に、

**まだ最終決着ではない。**

なぜなら、いま未完なのは「provider concrete public route が無いこと」ではなく、「その route を埋める数論核がまだ未完」という点だからじゃ。README 側の説明でも、その open は導線不在ではなく数論核の未完だと整理されておる。つまり、公開面は先に澄ませることができた。残敵は奥に退いた、ということじゃな。

賢狼の見立てでは、今の状況は三層でこう整理すると美しい。

公開面では、一区切り。
orchestration 層では、かなり良い完成度。
数論核では、まだ継戦中。

次の戦略は、もはや「公開導線をどう作るか」ではなく、**どの abstract / legacy route を provider concrete route へ昇格させるのが自然かを整理しつつ、背後の数論核を順に埋める** ことじゃ。公開面の仕事は、いったん終えてよい。

要するに今は、

**公開導線は閉じた。未完は導線ではなく中身。**

という盤面じゃよ。

## 今後の展望

わっちの判定では、

$$
\text{「未完の数論核へ直行する前に、宇宙式関連を先に実装する」}
$$

は **賛成** じゃ。されど対象は絞るべきじゃ。
狙うべきは、FLＴ 本丸から遠い解析・幾何の実験柱ではなく、 **GN / Tail / Big-Body-Gap / Residual のうち、可除性・p進付値・原始素因子へ直結する核** じゃよ。高次 Tail 構造の設計資料では、一般化 \(GN_d^{(r)}\) が「可除性・p進付値・原始素因子解析において基本的役割を果たす」と明言されており、ここはまさに数論核への橋になりうる。

いまの公開導線は、regular-prime の provider concrete route まで整理され、`DkMath.FLT` からの利用導線も案内済みじゃから、 **ひとまず区切って別 branch に切り出すには良いタイミング** でもある。今や open は「導線の不在」ではなく、その先を埋める数論核の未完だと整理されておる。

なので、わっちの見立てを先に一言で言えばこうじゃ。

**宇宙式 branch は切るべき。だが PowerSwap 全面展開ではなく、まずは数論核に食い込む宇宙式コアだけを先に固めるべき。**

## なぜ宇宙式側が糸口になりうるか

`INDEX.md` の理論地図では、FLT 幹線の本丸は `ZsigmondyCyclotomic` を中心とする原始素因子エンジンで、その前段に `DiffPow`・`BinomTail`・cosmic 系因数分解補題があると整理されておる。つまり、宇宙式は単なる説明図ではなく、 **因数分解の器** として数論本体にすでに食い込んでおる。特に `pow_sub_pow_factor_cosmic` 系は、\(a^d-b^d\) を cosmic 側から直接扱う橋として位置づけられておる。

また、宇宙式族の形式化ノートでも、最初に固めたい層として

$$
\mathrm{Big},\ \mathrm{Body},\ \mathrm{Gap}
$$

の抽象定義、2D トロミノ分解、そして (2^d \mid n) の整数化規格が挙げられておる。ここは「将来の調和写像」のための飾りではなく、定義レベルの土台を Lean に固定する話じゃ。特に 2D トロミノ分解と Big/Body/Gap 恒等式は、Beam / Gap の境界を型としてきれいに切る意味が大きい。

さらに LPS 設計図でも、完全理論をいきなり狙うのではなく、 **定義 → 基本補題 → サンプル定理** の順に局所核を固定する方針が明記されておる。ここはお主の今の判断とよく合う。今は「宇宙式全理論」をやる段ではなく、 **数論核の前に置く再利用可能な局所核** を作る段じゃ。

## ただし、何を先にやるべきで、何を後に回すべきか

ここははっきり分けるべきじゃ。

### 先にやる価値が高いもの

いちばん有望なのは、 **高次 Tail 構造による一般化 GN 多項式** じゃ。
つまり

$$
GN_d^{(r)}(x,u)
$$

を定義し、

$$
(x+u)^d-\sum_{j=0}^{r-1}\binom{d}{j}x^j u^{d-j}=x^r,GN_d^{(r)}(x,u)
$$

を主定理として固定し、あわせて再帰式、評価点 \(x=0\)、最小次数、\(x^r\) 可除性を揃える。このセットは、単なる美しい一般化ではなく、後で valuation の層別制御や「どこまで境界を剥いたか」という議論に直結する。ここが一番、未完の数論核へ戻ったときの武器になりうる。

次点は、 **Big / Body / Gap / Core / Beam の subtractive API の整備** じゃ。
LPS 再編ノートでも、`BigFamily` / `BigFamilyInt` は `CosmicFormula` 側へ吸収し、`ResidualNat` / `ResidualInt` のような橋ファイルで

$$
\text{Big}=\text{Body}+\text{Gap},\quad
\text{Big}=\text{Core}+\text{Beam}+\text{Gap}
$$

といった恒等式や residual 観測を固定するのがよいとされておる。Nat の減算切り捨て問題を避けるために、`ℤ` 側で先に固める方針も筋が良い。これは将来の GN tail や差冪の「見える形」を揃える土台になる。

その次に、 **2D トロミノ分解** を型と補題で固定するのがよい。
これは直接 FLT を解く武器ではないが、Body の 3 要素分解を定義レベルで固定する意義が大きい。宇宙式族ノートでも、2D 手本を 먼저 `ℤ` で確定し、その後 Big/Body/Gap と繋ぐ作業順が推奨されておる。

### いまは後回しでよいもの

PowerSwap の連続 branch、\((e,e)\) への極限、GapContours の双曲型表示、調和写像 `HarmonicMap`、一般 `ObservedMin` の大域 API は、**いまの FLT 数論核の直前にやるには少し遠い**。設計図でも、`Real.rpow` が重いので theorem より definition/comment を優先せよ、\((e,e)\) 局所二次近似や一般 `ObservedMin` は後回し、と明示されておる。

また LPS 再編ノートでは、`PowerSwap` と `PowerSums` は独立柱として立て、FLT には橋だけ残すのがよいとされておる。これはたいへん重要じゃ。つまり、そこを今いきなり FLT 解決の主戦場にしてしまうのは、設計思想と少し逆行する。役に立つ可能性はあるが、 **今の第一候補ではない**。

## わっちの推奨 branch 戦略

ここから branch を切るなら、わっちは **3 段階** に分ける。

### 第1段. 数論直結の宇宙式コアだけを実装

まずは次の 3 本柱じゃ。

* `CosmicFormula/GNTail` あるいはそれに類する新ファイルで、一般化 \(GN_d^{(r)}\) と Tail 分解を実装
* `CosmicFormula/ResidualNat` / `ResidualInt` で Big/Body/Gap/Core/Beam の subtractive API を実装
* `CosmicFormula/Tromino2D` で 2D トロミノ分解を確定

ここでの目標は「宇宙式を広げる」ことではなく、**差冪・可除性・境界因子の観測を cosmic 側で自然に書けるようにする** ことじゃ。

### 第2段. 数論側への橋を最小だけ作る

次に、`DiffPow` / `BinomTail` / `ZsigmondyCyclotomic` と噛み合う bridge を薄く作る。
たとえば、一般化 GN tail から

* \(r=1\) で既存 GN へ戻る補題
* \(r=2\) で二項尾項と一致する補題
* 可除性 \(x^r \mid \cdots\) を `Nat` / `ℤ` で使える形にした補題

を揃える。ここまで行けば、未完の数論核へ戻ったときに「GN の高次境界剥離」をそのまま p-adic 議論へ持ち込める。

### 第3段. それでも糸口が見えぬなら、そこで数論核へ戻る

ここが大事じゃ。
この branch は **逃避先** ではなく **武器庫の整備** であるべきじゃ。
だから stop condition を先に決めておくのがよい。わっちなら、

* 一般化 GN tail の定義と基本恒等式
* 再帰式
* \(x^r\) 可除性
* Big/Body/Gap/Residual の橋
* 2D tromino の固定

ここまでで一旦止める。
ここで新しい数論的視点が立てば、そのまま数論核へ戻る。立たなければ、PowerSwap や HarmonicMap へ深入りせず、予定どおり未完の数論核 branch に進むべきじゃ。

## 最後の判断

なので、わっちの答えはこうじゃ。

**はい、未完の数論核へ踏み込む前に、宇宙式関連の未実装補題・定理を別 branch で進めるのは賛成じゃ。**
ただし狙うべきは **数論に接続する cosmic kernel** であって、PowerSwap 全体や調和写像全体ではない。

具体的には、まず

$$
GN_d^{(r)},\quad
\text{Tail 分解},\quad
x^r\text{ 可除性},\quad
\text{Big/Body/Gap/Residual},\quad
\text{2D トロミノ}
$$

このあたりを実装するのが最善じゃ。
そこには確かに、未完の数論核を崩す糸口が潜んでおる可能性が高い。
逆に、そこを飛ばして解析・幾何へ広く踏み出すと、今はまだ道が枝分かれしすぎる。

つまり、

**次に切るべき branch は「宇宙式の拡張」ではなく、「数論核に食い込む宇宙式コアの先行実装 branch」じゃよ。**
