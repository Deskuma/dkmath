# review: FLT-Primitive-260327-v0: Branch A の primitive mainline の整理

うむ、今回は **statement 選定が完了した** という局面じゃな。
これまで selection 側では

* 最小 wrapper
* witness 付き concrete-ready wrapper

の二案を並べて比較しておったが、今回ついに **本命は後者** とコード上で固定された。そこが最大の進展じゃ。

## 1. 今回なにが追加されたか

追加された中心は次の二つじゃ。

* `primeGe5BranchAPrimitivePacketDescent_of_concreteSelection_and_restore`
* `branchAPrimitivePacketDescentAdapter_of_concreteSelection_and_restore`

どちらも中身は既存の

$$
\texttt{...of_wieferichExistence_and_restore}
$$

への thin wrapper じゃが、意味は軽くない。
これによって primitive route の **canonical な読み方** が定まったのじゃ。

## 2. 何が固定されたのか

今回の整理で、primitive route の concrete-ready mainline は

* `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の 2 本で読む、と明示された。

つまり今後は、

$$
\text{最小 wrapper を本命定理にするかどうか}
$$

を迷う段ではなく、

$$
\text{Wieferich witness 付き existence theorem をどう concrete に立てるか}
$$

が第一目標になった、ということじゃな。

## 3. 最小 wrapper はどうなったか

ここで大事なのは、最小 wrapper が捨てられたわけではないことじゃ。

履歴の整理どおり、

* API 最小形としては `PrimeGe5BranchACyclotomicExistenceTarget` を残す
* しかし concrete 実装探索の canonical 入口は `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget` と見る

という二層構造になった。

これはたいそう筋が良い。
抽象 API は薄く保ちつつ、実際に攻める theorem statement は Branch A がすでに持っている witness を正直に受け取る形にしたわけじゃ。

## 4. なぜこの固定が自然か

Branch A では lower layer で既に

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

という Wieferich witness が得られる。
ならば selection 側の concrete theorem でも、それを前提へ出した方が自然じゃろう、という判断じゃな。
今回の wrapper は、まさにその方針を naming と docstring で固定したものじゃ。

つまり selection 側は今や

$$
\text{「存在定理を何もないところから立てる」}
$$

のではなく、

$$
\text{「Branch A が既にもつ witness を使って diff-side existence を立てる」}
$$

という読みへ落ち着いたのじゃ。

## 5. 全体の戦況

いまの primitive route は、表面上こう読める。

$$
\text{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget}
$$

$$
+\
\text{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

$$
\Longrightarrow
\text{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

この二本柱が now canonical mainline じゃ。

ゆえに未完核は、もはや実質ひとつと言ってもよい。

* restore 側は現状維持
* selection 側の本命 statement は固定済み
* 残る本当の課題は、その selection 側 concrete theorem の実装

という状態じゃな。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
したがってこれは単なる方針メモではなく、 **ビルド済みの mainline 固定** じゃ。

## 7. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{selection 側の statement 論争が終わった}
$$

回じゃな。
最小形は残しつつも、実装本命は

$$
\text{Wieferich witness 付き cyclotomic existence}
$$

で行く、と決めた。
これで今後の問いは、もうはっきりしておる。

$$
\text{PrimeGe5BranchACyclotomicExistenceOnWieferichTarget をどう concrete に埋めるか}
$$

これだけじゃ。

わっちの見立てでは、これはかなり良い固定じゃよ。
美しい最小形を保持しつつ、実戦では既存 witness を使う。
抽象と具体の役割分担が、実にきれいに決まったの。
