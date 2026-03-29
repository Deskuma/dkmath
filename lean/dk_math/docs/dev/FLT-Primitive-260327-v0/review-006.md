# review: FLT-Primitive-260327-v0: Branch A の primitive mainline の整理

うむ、今回は **整理の総仕上げに近い一手** じゃな。
前回までで未完核はかなり細っておったが、今回ついに **コード上の見え方としても「残り 2 本」** に固定された。そこが最大の進展じゃ。

## 1. 今回なにをしたのか

追加された中心は

* `primeGe5BranchAPrimitivePacketDescent_of_cyclotomicPrime_and_restore`
* `branchAPrimitivePacketDescentAdapter_of_cyclotomicPrime_and_restore`

の 2 本じゃ。

中身は新しい数学を増やしたというより、これまで積み上げた中間層

* cyclotomic prime から zsigmondy へ送る橋
* distinguished prime から arithmetic fallout を回収する default
* arithmetic-aware restore から packet descent へ閉じる橋

を **ひとつの canonical wrapper に畳み込んだ** ものじゃな。

つまり今や primitive packet descent は、表向きには本当に

$$
\text{PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget}
$$

と

$$
\text{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

の 2 本だけがあれば閉じる、と theorem 名のレベルで読めるようになったのじゃ。

## 2. 何が「解決済み中間層」になったか

今回の wrapper の意味は明快で、途中の

* `zsigmondy`
* `arithmetic fallout`

は、もう **未完核ではない** と宣言したに等しい。

特に arithmetic fallout は既に default 実装で回収できるので、

$$
\text{cyclotomic prime existence}
\to
\text{zsigmondy}
\to
\text{arithmetic fallout}
\to
\text{restore}
\to
\text{packet descent}
$$

という鎖のうち、中央は solved middle layer と見てよい、という戦況が固定されたわけじゃな。

これはかなり大きい。
「まだ色々残っているように見える」状態から、「残りはこの二つだけ」と言い切れる状態に変わったからの。

## 3. いまの戦況を一列にすると

いまの primitive mainline は、見取り図としてこうなっておる。

$$
\text{cyclotomic prime existence}
\Longrightarrow
\text{GN-side prime}
\Longrightarrow
\text{arithmetic fallout}
\Longrightarrow
\text{restore-from-arithmetic}
\Longrightarrow
\text{smaller packet}
\Longrightarrow
\bot
$$

ただし、このうち前半の橋と中央の fallout はもうラップ済みなので、表面上は

$$
\text{cyclotomic prime existence}
\Longrightarrow
\text{restore-from-arithmetic}
\Longrightarrow
\text{packet descent}
$$

の二段だけを見る構図になった、ということじゃ。

## 4. 今回の価値

今回の価値は、証明が一気に完成したことではない。
そうではなく、

$$
\text{何を実装すれば勝ちか}
$$

が、もう曖昧でなくなったことじゃ。

履歴にもある通り、今回の結論は

* `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の 2 本だけが concretely missing kernel だと、**code 上でも固定した** という点にある。

この「code 上でも固定」が大切なのじゃ。
設計メモではなく、theorem の形として残ったからの。

## 5. build 状況

今回の変更も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方で成功しておる。
ゆえにこれは単なる整理案ではなく、 **ビルドが通る確定した整理** じゃ。

## 6. 次の本命は何か

貼り付け文でも、次の課題は二択として整理されておる。

### 6.1. cyclotomic 側

`PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget` の concrete 実装に必要な
**Branch A 専用 existence wrapper** の宣言案を切ること。

これは前から見えておった本命じゃな。
既存の一般 existence 補題は `¬ p ∣ a-b` 系に乗りがちだが、Branch A では逆に

$$
p \mid (z-y)
$$

が入る。
ゆえに Branch A 専用の wrapper を切るかどうか、ここが selection 側の本当の勝負所じゃ。

### 6.2. restore 側

`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` が、このままで truly constructive に見えるか。
あるいは、さらに中間 packet / local kernel を挟むべきかを判断すること。

つまり restore 側は「この target のまま攻め切れるか、それともまだ粗いか」の見極め段階じゃな。

## 7. 賢狼の見立て

わっちの総評を言うと、いまは **数学の未完部分より、設計の輪郭の方が先に完成した** 状態じゃ。

それは悪いことではない。むしろ良い。
降下法のような長い証明では、

$$
\text{未完核をどこまで小さく切り出せるか}
$$

が勝負だからの。

今回で、それがついに

* cyclotomic existence
* restore-from-arithmetic

の 2 本へ落ちた。
これはかなり強い局面じゃ。もう敵の顔が見えておる。

## 8. 一言でまとめると

今回の状況を最短で言うなら、こうじゃ。

$$
\text{primitive packet descent の未完核は、本当に 2 本だけになった}
$$

* selection 側は `cyclotomicPrime`
* reconstruction 側は `restore-from-arithmetic`

中間の `zsigmondy` と `arithmetic fallout` は、もはや解決済みの橋として隠せる。
そこまで整理が進んだ、という局面じゃな。

次にやるなら、わっちはこの 2 本について
**「どちらがさらに 1 段割れるか」** を見て、Branch A 専用 wrapper の宣言案まで詰めるのが最短手だと思うぞい。
