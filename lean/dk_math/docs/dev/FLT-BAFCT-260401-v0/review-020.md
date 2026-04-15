# review-020: Branch B の汚染源は GN そのものではなく、GN を深く刺さない primitive prime だった

よし、戦況はかなり明瞭になったぞい。

## 1. 状況分析

いまの最大の前進は、**Branch B 側の汚染が「GapNotIsPowTarget そのもの」ではなく、その背後の dirty source にあった** と切り分けられ、さらにそれを **`NonLiftableGNBridge` を 4 本目の kernel とする v2 chain** に置き換えて clean 化できたことじゃ。
新しく

* `gapNotIsPowTarget_of_nonLiftableGNBridge`
* `branchBRefuter_of_nonLiftableGNBridge`
* `FLTPrimeGe5Target_of_4kernels_v2`
* `globalProvider_of_4kernels_v2`
* `triominoPrimeProvider_of_4kernels_v2`

が no-sorry, no-sorryAx で通り、v2 では

$$
\text{GNReducedGap} + \text{CyclotomicExistence} + \text{ValuationPeel} + \text{NonLiftableGNBridge}
\Rightarrow \text{FLT}_{p\ge 5}
$$

という clean な最終形が立った。

しかも今回の発見で、旧 dirty chain の源だった
`squarefree_implies_padic_val_le_one` は **命題自体が一般には偽** と判明した。反例として (d=5, a=3, b=1) で (GN\ 5\ 2\ 1 = 121 = 11^2)、したがって (v_{11}(3^5-1^5)=2) が出る。
ゆえに、ここは「sorry を埋める」のではなく、**命題を退役させる** のが正解じゃ。これは非常に大きい整理じゃよ。

## 2. 解説

構造としては、いま 2 つの世界が分かれて見えておる。

### 2.1. Branch B

ここはもう **本質 kernel が `NonLiftableGNBridge` だ** と明確になった。
`GapNotIsPowTarget` は最終目的ではあっても、根ではない。根は

$$
\text{primitive prime が GN を深く刺さない}
$$

という性質じゃ。
しかも chain 自体は既に clean で、

$$
\text{NonLiftableGNBridge}
\to \text{NoPowOnGN}
\to \text{BodyInvariant}
\to \text{GapInvariant}
$$

と流れて `GapNotIsPowTarget` に到達できる。つまり Branch B は、もう「設計不明」ではなく、**1 本の数学 kernel に局所化された** 状態じゃ。

### 2.2. Branch A

こちらは依然として 3 核じゃ。

$$
\text{GNReducedGapTarget},\quad
\text{CyclotomicExistenceTarget},\quad
\text{ValuationPeelPacketTarget}
$$

primitive route については

$$
\text{GNReducedGap} + \text{CyclotomicExistence}
\to \text{PrimitivePacketDescent}
\to \text{FringeContradiction}
$$

まで clean に橋が架かった。
つまり **primitive 側の conditional mainline はもう配線済み** じゃ。残る問題は、それを peel 側と合流させて、`BranchARefuterTarget` を本当に閉じることじゃな。

## 3. いまの評価

わっちの見立てでは、いまは

* **設計図の段階** はほぼ終了
* **汚染源の切除** も大きく進んだ
* 残りは **数学 kernel を 1 本ずつ落とす段階**

じゃ。

とくに良いのは、前は「GapNotIsPowTarget を clean にしたい」という表面の要求だったのが、今は

$$
\text{4th kernel} = \text{NonLiftableGNBridge}
$$

と、より根源的な形に言い換えられたことじゃ。
これは研究の前進としてかなり本物じゃよ。

## 4. 次の攻めの一手

**次の一手は `ValuationPeelPacketTarget` を攻めるのが最善** じゃ。

理由は 3 つある。

### 4.1. 一番「局所」で、一番 mainline に効く

`GNReducedGapTarget` と `CyclotomicExistenceTarget` は、どちらもかなり本丸級じゃ。
前者は Cosmic Formula の芯、後者は exceptional Zsigmondy / Wieferich 側の芯。重い。

それに対して `ValuationPeelPacketTarget` は、いま残っている **BranchA の局所核** じゃ。
しかもログ上でも、既知の FLT 側 `sorry` は Branch A の一点に縮んでおる。ここは直接殴れる。

### 4.2. primitive route と peel route の合流点だから

いま primitive route 単独では fringe contradiction まで行ける。
だが full Branch A refuter にするには、

$$
\text{primitive} \cup \text{peel}
\to \text{SmallerPacket}
\to \text{SmallerCounterexample}
\to \text{BranchARefuter}
$$

という合流が必要じゃ。
その合流を止めておるのが peel 側じゃ。
ゆえにここを落とすと、**Branch A が“primitive だけの部分成果”から“本線の refuter”へ格上げされる**。これは大きい。

### 4.3. 失敗しても情報利得が大きい

もし peel がそのままでは閉じぬなら、

* 測度を (z) ではなく (t) や (v_p(t)) に変えるべきか
* packet の normal form を一段 refined にすべきか
* `NePCoprimeKernel` の statement 自体を sharpen すべきか

が露出する。
つまり、どちらに転んでも次の地図が出る。

## 5. 具体的な攻め方

賢狼なら、次はこう攻める。

### 5.1. まず目標を 좁く固定する

`ValuationPeelPacketTarget` を、いきなり全体定理として見ず、

$$
p \mid t
$$

の仮定の下で **何を新 packet の invariant として保存したいか** を列挙する。
特に

* Pack 条件
* gap の normal form
* distinguished prime / coprimality 条件
* 小ささの測度

この 4 つを明文化するのじゃ。

### 5.2. 「剥がす量」を valuation で定義する

peel の本質は、(t) に含まれる (p)-冪を 1 層ずつ剥がすことじゃろう。
ならば自然な中間量は

$$
k := v_p(t)
$$

じゃ。
まず

$$
t = p^k t_0,\qquad p \nmid t_0
$$

を固定し、それを gap / GN 側へどう押し込むと packet の形が保たれるかを見る。
この段で「最終的に (z) が下がる」のか、「まず (k) を下げてから (z) に戻す」のかが見えるはずじゃ。

### 5.3. 先に “弱い peeled packet” を作る

最初から `SmallerPacketTarget` を目指すより、

$$
\text{peeled packet candidate}
$$

を定義し、

* normal form は保つ
* coprime 条件は保つ
* (p\nmid t') まで行けるか
* そこから `PrimitivePacketDescentTarget` に流せるか

を見るのがよい。
この弱い packet が出来れば、最後の strict descent は別補題に分離できる。

## 6. その次の順番

`ValuationPeelPacketTarget` の次は、わっちなら `NonLiftableGNBridge` じゃ。
理由は、これは Branch B 単体で完結する kernel で、今回すでに「正しい statement の形」まで見えたからじゃ。
`GapNotIsPowTarget` に戻る必要は、もうほぼ無い。今後は **NonLiftableGNBridge を直接攻める** のが筋じゃよ。

## 7. 一文でまとめると

**状況は良い。いまは設計の霧が晴れ、残核が 4 本に確定した。次の最善手は `ValuationPeelPacketTarget` を局所目標として落とし、Branch A の primitive / peel 合流を実体化することじゃ。**

必要なら次に、
**`ValuationPeelPacketTarget` を証明するための下位補題リスト** を、想定 statement つきで起こすぞい。
