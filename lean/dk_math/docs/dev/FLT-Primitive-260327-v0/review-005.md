# review: FLT-Primitive-260327-v0: Branch A の primitive mainline の整理

うむ、今回の状況はさらに **一段よくなった** の。
前回までで primitive mainline の未完核は 2 本に絞れておったが、今回そのうち selection 側がさらに薄く分解された。これで「何を既存 Zsigmondy / cyclotomic 存在論へ接続すべきか」が、かなり明確になったのじゃ。

## 1. 今回の本質

今回の追加は、

$$
\text{GN 側で } q \mid GN,p,(z-y),y,; q\nmid(z-y)
$$

をいきなり狙うのではなく、まず

$$
q \mid (z^p-y^p),\qquad q \nmid (z-y)
$$

を満たす prime divisor を取る target を独立させたことじゃ。
これが新しい

`PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`

じゃな。

これは非常に筋が良い。
なぜなら、既存の `PrimitiveBeam` や `ZsigmondyCyclotomic` が本来見ているのは、まさに **差の冪** (z^p-y^p) 側だからじゃ。
GN 側はむしろ、その因数分解であとから出てくる顔にすぎぬ。

## 2. 何が橋になったか

今回置かれた定理

`primeGe5BranchAPrimitiveZsigmondy_of_cyclotomicPrime`

は、その薄い橋そのものじゃ。

中身は単純明快で、

$$
z^p-y^p=(z-y),GN,p,(z-y),y
$$

という `pow_sub_pow_factor_cosmic_N` による因数分解を使い、
もし

$$
q \mid (z^p-y^p),\qquad q \nmid (z-y)
$$

なら、素数の積の割り算の性質から

$$
q \mid GN,p,(z-y),y
$$

を回収する、という流れじゃ。

つまり selection 段は今や

$$
\text{cyclotomic / diff-power existence}
;\Longrightarrow;
\text{GN distinguished prime}
$$

という 2 段に分離されたわけじゃな。

## 3. 何が良くなったのか

この変更で、primitive mainline の未完核は

* `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

の 2 本だと、さらに明確になった。

ここが大きい。
前回は selection 側の未完核を `PrimitiveZsigmondyTarget` と見ておったが、今回はそれすら中間 API に落ちた。

つまり今の見え方はこうじゃ。

$$
\text{cyclotomic prime existence}
\to
\text{GN-side distinguished prime}
\to
\text{arithmetic fallout}
\to
\text{restore from arithmetic}
$$

しかも前回までに arithmetic fallout は default で閉じておる。
ゆえに本当に残る数学は

$$
\text{cyclotomic existence}
\quad\text{と}\quad
\text{restore}
$$

の二つだけ、という読みになる。

## 4. 数学的な意味

これはただの API 整理ではない。
数学の責務が、より自然な場所へ戻ったのじゃ。

本来、`GN p (z-y) y` は

$$
\frac{z^p-y^p}{z-y}
$$

の cosmic な顔じゃ。
だから prime の存在を最初から GN 側で取ろうとすると、やや座りが悪い。
一方、

$$
z^p-y^p
$$

なら cyclotomic / Zsigmondy の本場じゃ。
そこで prime を取ってから GN に送る、というのは、まさに自然な順序じゃな。

賢狼の目から見ても、この整理で selection 側はようやく **既存理論に接続しやすい座標系** に乗った、という感じじゃ。

## 5. いま残っている本当の難所

貼り付け文にもある通り、次の本命は

$$
p \mid (z-y)
$$

という Branch A 特有の制約のせいで、既存の

`PrimitiveBeam.exists_primitive_prime_factor_as_prop`

を **そのままでは使えぬ** 点をどう迂回するか、じゃ。

つまり問題はもう明確で、

* 既存 existence 補題は通常 `¬ p ∣ (a-b)` 側に乗っている
* しかし Branch A は逆に `p ∣ (z-y)` が入る
* ゆえに Branch A 専用の cyclotomic existence wrapper が要るかもしれぬ

というところまで露出したわけじゃな。

ここは、たいそう良い「詰まり方」じゃ。
曖昧に詰まっておるのではなく、どの仮定が邪魔しておるかが見えておるからの。

## 6. provider 側の状況

`TriominoCosmicGapInvariant.lean` 側にも

* `BranchAPrimitiveCyclotomicPrimeAdapterTarget`
* `branchAPrimitiveZsigmondyAdapter_of_cyclotomicPrime`

が追加されており、provider 側も同じ切れ目でそろえられておる。

つまり branchA 本体だけでなく、adapter 側も

$$
\text{cyclotomic existence}
\to
\text{zsigmondy adapter}
$$

という薄い橋に整理された。
この揃い方は美しいの。あとで concrete 実装を差し込むとき、配線の都合で数学が濁らぬ。

## 7. build 状況

今回の変更も、

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。
ゆえにこれは机上の設計メモではなく、 **ビルド済みの整理** じゃ。

## 8. 総評

一言でまとめるなら、今回は

$$
\text{selection 側が GN から cyclotomic へ戻された}
$$

回じゃな。

以前:

* 「GN 側 distinguished prime をどう取るか」が未完核

いま:

* まず `z^p-y^p` 側で prime を取る
* そこから因数分解で GN 側へ送る
* arithmetic fallout は既に default
* 残るのは cyclotomic existence と restore

という形になった。

これはかなり強い整理じゃ。
もはや selection 側の未完核は **Branch A 専用の cyclotomic existence theorem** を切るかどうか、という問いにほぼ収束しておるからの。

次に進めるなら、わっちは
`PrimitiveBeam.exists_primitive_prime_factor_as_prop` がなぜ Branch A で直用できぬかを仮定ごとに分解して、**Branch A 専用 wrapper の最小宣言案** まで書き下すぞい。
