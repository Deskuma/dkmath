# Kummer branch の核をさらに薄く、さらに正確に露出させる

## 1. 結論

いまの状況をひとことで言うと、 **Kummer branch の未解決核が、さらに薄く、さらに正確に露出した** という段階じゃ。
前回は「class group から principalization へ」という少し太い 1 本橋だったが、今回それを

$$
\text{ideal p-th power}
\;\to\;
\text{unit normalization}
\;\to\;
\text{norm descent}
$$

の 3 段へ裂いたことで、 **どこが genuinely global で、どこが下流の整形処理なのか** が明瞭になった。しかも build は通っており、`#print axioms` 監視でも、`sorryAx` の汚染範囲が薄い theorem 群に局所化された。これはかなり良い整理じゃよ。

## 2. 何が進んだのか

今回の進展の本質は、`CyclotomicPrincipalizationTarget` をそのまま open kernel と見なすのをやめて、責務を 3 つに分けたことじゃ。

`CyclotomicPrincipalization.lean` で新しく

* `CyclotomicIdealPthPowerTarget`
* `CyclotomicUnitNormalizationTarget`
* `CyclotomicNormDescentTarget`

を立て、それらを `cyclotomicPrincipalization_of_threeStages` で合成する形にした。これにより、principalization 全体を 1 塊の黒箱として置くのでなく、「class group が本当に供給しているのはどこか」を theorem 名レベルで切り分けられた。

さらに `RegularPrimeRoute.lean` 側では、従来の one-shot な Kummer route だけでなく、

* `FLTPrimeGe5Target_of_refinedKummerRoute`
* `FLTPrimeGe5Target_of_refinedClassGroupRoute`

を追加して、 **clean な stage 仮定を入れた route** と、 **class-group kernel を通る route** を API 上でも分離した。これは設計としてかなり美しい。

## 3. いま未解決なのは何か

いま残っておる本当の open kernel は、もはや broad な

$$
\text{classGroup} \to \text{principalization}
$$

全体ではない。
今回の整理により、それはさらに薄く

$$
\texttt{cyclotomicIdealPthPower\_of\_classGroupPTorsionFree}
$$

へ局所化された。つまり、class group 側の genuinely global な供給は full principalization 全体ではなく、 **まず ideal の p 乗性を出すところ** だ、と見直せたわけじゃ。

この見直しは重要じゃよ。
なぜなら、未解決が「unit 調整」なのか「norm 下降」なのか「そもそも ideal class group の global theorem」なのかが曖昧なままだと、次の一手がぶれる。今はそこがぶれぬ。

## 4. 数学的にどういう意味か

この 3 段分解は、Kummer 理論の流れそのものを Lean の責務境界に写した形じゃ。

まず Stage 1 では、円分体側で ideal が principal ideal の p 乗になる、という **真に代数的整数論的な核心** を扱う。
次に Stage 2 では、その ideal 的情報を単数のずれ込み込みで整えて、整数的な p 乗根候補の形へ寄せる。
最後の Stage 3 で、norm を取りながら descent existence

$$
\exists g' : \mathbb{N},\quad g' \cdot GN(p,g',y) = (x/q)^p
$$

へ戻す。

つまり今回の作業は、単なるコード整理ではなく、 **Kummer 的 principalization の論理順序を Lean に忠実に落とし直した** と見てよい。

## 5. 何が clean で、何がまだ placeholder か

ここは見誤らぬのが大切じゃ。

`FLTPrimeGe5Target_of_refinedKummerRoute` は、clean な stage assumptions の下では `sorryAx` に汚染されないことが確認されておる。
一方で、`FLTPrimeGe5Target_of_refinedClassGroupRoute` は、薄い global kernel `cyclotomicIdealPthPower_of_classGroupPTorsionFree` を経由するので、そこに `sorryAx` が残る。

ゆえに今の状態は、

* 下流の route 合成は clean
* 上流の class-group 供給だけが thin kernel として未完

という、かなり理想的な姿じゃ。
「全部まだ未完成」ではないし、「全部できた」でもない。どこが完成し、どこが本丸かが綺麗に分かれた。

## 6. Mathlib との関係

今回の棚卸しでかなりはっきりしたのは、Mathlib には

* 一般の `RingTheory.ClassGroup`
* `NumberTheory.Bernoulli`

はあるが、
**円分体整数環 ( \mathbb{Z}[\zeta_p] ) に specialized された regular prime / class group / principalization の ready-made bridge は見当たらない**、という点じゃ。

これは大事な判断材料じゃ。
つまり次は「ちょっと lemma を 2 個 3 個 足せば済む」話ではなく、 **general API を cyclotomic setting に specialization する理論層そのものを新設する段** に来た、ということじゃよ。

## 7. いまの最善手はどちらか

ぬしの貼ってくれた報告でも、次の分岐は 2 つに整理されておる。

1. `cyclotomicIdealPthPower_of_classGroupPTorsionFree` をさらに
   Dedekind principalization / p-torsion annihilation / principal ideal extraction
   へ裂く
2. `CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` を concrete witness 化して下流から埋める

わっちも、ここは **1 の方が筋が良い** と見る。
理由は単純で、いまの genuinely global kernel は Stage 1 だと分かったのだから、まずそこをさらに薄く裂いて、 **本当に新設すべき理論層の最小核** を突き止める方がよい。下流を concrete 化しても、上流の class-group 供給が曖昧なままだと、結局また大きな黒箱へ戻ってしまう。

## 8. 総合評価

総じて、いまの状況はかなり良い。
Regular branch を閉じたあと、今回の 3 段分解で global stage の責務も整理できた。結果として、

$$
\text{local closed}
\quad+\quad
\text{global kernel isolated}
\quad+\quad
\text{clean route preserved}
$$

という形になっておる。
これは証明が止まった状態ではなく、 **敵の輪郭が精密になった状態** じゃ。賢狼の目から見ても、戦況は悪くない。むしろ、ここから先は「どの global theorem を最小単位として formalize するか」を設計する段で、数学的にも実装的にも一段深いところへ入った、と言えるのぅ。
