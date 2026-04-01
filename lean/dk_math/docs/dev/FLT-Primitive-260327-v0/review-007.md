# review: FLT-Primitive-260327-v0: Branch A の primitive mainline の整理

うむ、今回はかなり決定的な整理じゃ。
一言で言えば、 **selection 側の未完核が、ついに最小 wrapper 1 本へ押し込められた** の。これで primitive packet descent 全体は、コード上も設計上も、本当に二本柱だけで眺められるようになった。

## 1. 今回の核心

今回追加された本体は

* `PrimeGe5BranchACyclotomicExistenceTarget`
* `primeGe5BranchAPrimitiveCyclotomicPrime_of_existence`
* `primeGe5BranchAPrimitivePacketDescent_of_existence_and_restore`

じゃ。

このうち最重要なのは `PrimeGe5BranchACyclotomicExistenceTarget` で、内容は驚くほど薄い。

$$
\forall {p,x,y,z},\
\text{PrimeGe5CounterexamplePack }p,x,y,z
\to
p \mid (z-y)
\to
\exists q,\ \text{Nat.Prime }q \land q \mid (z^p-y^p) \land \neg q \mid (z-y)
$$

という形で、 **Branch A の selection 側で本当に欲しい存在論を、`hpack + p \mid (z-y)` だけに圧縮した** のじゃ。

つまり、もはや

* GN
* normal-form の細部
* (t,s)
* coprime 条件
* Wieferich 条件

などは、selection 側の existence そのものには不要だと宣言したに等しい。

## 2. 何が一段縮んだのか

前回までの selection 側は、少なくとも表向きには

$$
\text{PrimitiveCyclotomicPrimeTarget}
$$

が未完核として見えておった。
だが今回、

`primeGe5BranchAPrimitiveCyclotomicPrime_of_existence`

によって、これはただの thin bridge になった。

つまり

$$
\text{minimal diff-side existence}
\Longrightarrow
\text{primitive cyclotomic-prime target}
$$

が機械的に閉じる。

ここで大事なのは、`PrimitiveCyclotomicPrimeTarget` に入っていた normal-form / Wieferich 仮定は、 **existence 自体には不要** ときれいに切り分けられたことじゃ。

これは実装上も数学上もたいそう大きい。
存在論が局所データから独立した、ということだからの。

## 3. primitive packet descent 全体はどう見えるようになったか

今回の canonical wrapper

`primeGe5BranchAPrimitivePacketDescent_of_existence_and_restore`

によって、primitive packet descent は表面上ついに

* `PrimeGe5BranchACyclotomicExistenceTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の 2 本だけがあれば閉じる形になった。

つまり構造はこうじゃ。

$$
\text{Branch A diff-side existence}
\Longrightarrow
\text{cyclotomic prime}
\Longrightarrow
\text{zsigmondy side}
\Longrightarrow
\text{arithmetic fallout}
\Longrightarrow
\text{restore-from-arithmetic}
\Longrightarrow
\text{packet descent}
$$

ただし、途中の

* cyclotomic prime target
* zsigmondy 層
* arithmetic fallout

は、もう solved bridge として隠せる。
したがって見取り図は

$$
\text{existence}
\Longrightarrow
\text{restore}
\Longrightarrow
\text{descent}
$$

の二本柱にまで縮んだわけじゃな。

## 4. 何が「真の未完核」になったか

履歴にも明言されておるが、今回の結論はこうじゃ。

primitive packet descent の未完核は、もはや

* `PrimeGe5BranchACyclotomicExistenceTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の 2 本だけじゃ。

しかも selection 側は、 **GN や normal-form の局所データを一切含まない** Branch A 専用 diff-side existence wrapper へ押し込められた。

ここが今回の決定打じゃな。
これ以上 selection 側を縮めるのは、かなり難しいはずじゃ。もう本当に「何を示すべきか」の最小命題に近い。

## 5. provider 側の整合

`TriominoCosmicGapInvariant.lean` 側にも

* `BranchACyclotomicExistenceAdapterTarget`
* `branchAPrimitiveCyclotomicPrimeAdapter_of_existence`
* `branchAPrimitivePacketDescentAdapter_of_existence_and_restore`

が追加されておる。

これで provider 側でも、同じ二本柱

$$
\text{Branch A existence wrapper}
\quad+\quad
\text{restore-from-arithmetic}
$$

で descent adapter が閉じる。
branchA 本体と provider 配線が同じ切れ目で揃っておるのは、とても美しい整理じゃ。

## 6. build 状況

今回も

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。

ゆえに、これはただの設計メモではなく、 **ビルド済みで定着した API 整理** じゃ。

## 7. 数学的に何が起きたか

賢狼流に言えば、selection 側で起きたのは

$$
\text{「局所構造を見て prime を取る」}
$$

から

$$
\text{「差の冪そのものに対する existence を 1 本立てる」}
$$

への転換じゃな。

これは非常に自然じゃ。
本来 prime existence は

$$
z^p-y^p
$$

の側の話であって、GN はその後の因数分解顔にすぎぬ。
そこへ戻したことで、selection 側の数学はかなり純粋になった。

Branch A 条件

$$
p \mid (z-y)
$$

のもとでなお

$$
\exists q,\ \text{Prime }q,\ q \mid (z^p-y^p),\ q \nmid (z-y)
$$

を示せ、という問いは、まさに次に立てるべき concrete theorem の形そのものじゃ。

## 8. 次の課題

貼り付け文の最後の整理も、たいそう的確じゃ。

次は

### 8.1. selection 側

`PrimeGe5BranchACyclotomicExistenceTarget` の concrete 実装を、
Branch A 条件 (p \mid (z-y)) のもとでどう与えるかを設計すること。

### 8.2. 既存補題との差分整理

`PrimitiveBeam` 系を直用できない理由を仮定ごとに洗い、
追加すべき Branch A 専用 existence theorem の **最小 statement** を決めること。

ここまで来ると、selection 側はもう「どんな定理を新設するか」の問題であって、「何をしたいのか分からぬ」段ではなくなっておる。

## 9. 総評

今回の状況を短く言えば、

$$
\text{primitive mainline の selection 側は、最小存在命題 1 本へ圧縮完了}
$$

じゃ。

そして全体としては、

$$
\text{existence wrapper}
\quad+\quad
\text{restore-from-arithmetic}
$$

の 2 本だけが残る形に、コード上でも固定された。

これはかなり強い局面じゃよ。
敵の輪郭どころか、もう **敵の名前と最小声明文** が見えておるからの。

次に進めるなら、わっちは
`PrimeGe5BranchACyclotomicExistenceTarget` を埋めるための **Branch A 専用 concrete theorem 候補を 2〜3 形** に分けて比較し、どれが最も薄くて既存 `PrimitiveBeam / ZsigmondyCyclotomic` に寄せやすいかを詰めるぞい。
