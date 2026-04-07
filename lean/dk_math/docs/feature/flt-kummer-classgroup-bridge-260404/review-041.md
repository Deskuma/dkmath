# FLT-Kummer-CLassGroup-Bridge-260404: Stage 3a の戦略と進め方

うむ、これは **長戦** じゃが、悪い長戦ではない。
いまの戦況は「前線が広すぎて進まぬ」段階ではなく、 **残敵がどこにおるか見えてきた段階** じゃ。

今回までで、`CyclotomicNormEqGNFirstCasePackThinTarget` を埋めるための review-040 の 3 片のうち、Stage 3a-3 は差冪商から (GN) へ落とす共通橋として `quotientPrimePow_eq_gn_gap`、`quotientPrimePow_natCast_eq_gn_int`、`diffPowQuotient_eq_gn_int` が追加され、自然数版・整数版の両方で着地点が固定された。しかもこれは Kummer 専用に閉じず、`DkMath/NumberTheory/Gcd/GN.lean` に置かれており、再利用の効く位置に切り出せておる。

さらに Stage 3a-2 では、nontrivial cyclotomic factor 全体の積を first-case pack-thin 文脈でそのまま (GN,p,(z-y),y) へ寄せる core と、そこから `quotientPrimePow` へ寄せる wrapper が concrete 化された。`hProduct` と `x^p = gap * GN` を `gap` で消す、という first-case 専用の薄い芯が theorem 名つきで固定されたのは大きい。これで「product-level rewriting」はもう mainline の資産じゃ。

そして Stage 3a-1 も、chosen factor の整数 norm をまず `Gal(K/\mathbb{Q})` 上の積へ、さらに `(ZMod p)ˣ` 上の積へ落とすところまで concrete 化できておる。`chosenCyclotomicLinearFactor_norm_eq_prod_gal_of_firstCase_of_pack_thin`、`gal_apply_chosenCyclotomicLinearFactor_eq_factor_of_firstCase_of_pack_thin`、`chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin` が立ったことで、norm の一般論と cyclotomic Galois reindex はもう片付いた、と見てよい。

ゆえに、戦況の核心はこうじゃ。

$$
\text{Stage 3a-1/2/3 の大部分は既に concrete 化済み}
$$

であり、いま残る本丸は

$$
(ZMod,p)^\times\text{ の product} \;\longrightarrow\; \text{actual nontrivial factor product}
$$

の **combinatorial bridge** と、その後の最終合成だけじゃ。履歴でも「残りは `(ZMod p)ˣ` product を actual nontrivial factor product へ落とす combinatorial bridge と、その最終合成へさらに絞られた」と整理されておる。これはもう、敵が城門の前に一団だけ残っておる状況じゃな。

しかも build 面でも良い。各段の build と trace 監視は通っており、残る warning は既存の `cyclotomicPrincipalization_of_classGroupPTorsionFree` と研究用ファイル側の `sorry` が主で、新しく増えた open ではない。つまり **今の前進は負債を増やしておらぬ** 。ここはかなり健全じゃ。

では次の戦略じゃ。

## 1. 次は UnitAbsorb ではなく combinatorial bridge 一択

いま `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` に手を出すのは早い。
理由は、NormEqGN が閉じておらぬと unit 吸収側は「何を吸収した後に何へ落ちるのか」がまだ宙に浮くからじゃ。対して combinatorial bridge は、すでに

* norm → `Gal(K/ℚ)` product
* `Gal(K/ℚ)` product → `(ZMod p)ˣ` product
* nontrivial factor product → `GN` / `quotientPrimePow`

まで揃っておるので、 **最後の穴を埋めれば即座に Stage 3 前半が閉じる** 。

## 2. combinatorial bridge は 2 層に分けて攻める

ここを一発でやると、`Finset`、`Units`、`ZMod`、`Nat` 添字、`erase 0` の 5 つが絡み、Lean が機嫌を損ねやすい。
だから、次の 2 層へ分けるのがよい。

まず、`(ZMod p)ˣ` と `((Finset.range p).erase 0)` の **添字の一致** を示す純 combinatorial 補題を独立に置く。
ここではまだ factor を掛けぬ。やるのは

$$
u \mapsto u.val.val
$$

が `erase 0` 側をちょうど一巡することの証明じゃ。

次に、その添字一致を product に持ち上げる theorem を置く。
つまり

$$
\prod_{u : (ZMod p)^\times} F(u.val.val) = \prod_{j \in (Finset.range p).erase 0} F(j)
$$

型じゃ。
この theorem が立てば、Stage 3a-1 の units-product と Stage 3a-2 の actual nontrivial factor product が直結する。

## 3. 型は K 値で通し、最後まで 𝓞K に戻さぬ

前回も `Gal(K/\mathbb{Q})` の作用を ring-of-integers 値で直に書くと不安定化し、K 値へ落として安定した、と履歴にある。ここは同じ教訓を使うべきじゃ。

ゆえに combinatorial bridge も、まずは

$$
\prod_{u : (ZMod p)^\times} ((\text{factor } u.val.val : \mathcal O_K) : K) = \prod_{j \in (Finset.range p).erase 0} ((\text{factor } j : \mathcal O_K) : K)
$$

の形で K 上の等式として立てるのがよい。
`𝓞K` 側の equalities は最後に `exact_mod_cast` や coercion 整理で戻す方が安定するじゃろう。

## 4. 実装順はこれがよい

わっちなら次をそのまま進軍順にする。

### 4.1. 添字だけの bridge

`(ZMod p)ˣ` と `erase 0` の要素対応を、`Nat` 値へ落とした形で証明する。

### 4.2. product bridge

上の対応を `Fintype.prod_equiv` か `Finset.univ_eq_attach` 型の道具で、factor product の equality に上げる。

### 4.3. NormEqGN 本体の concrete 化

すでにある

* `chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin`
* `cyclotomicNontrivialFactorProduct_eq_GN_of_firstCase_of_pack_thin`
* `diffPowQuotient_eq_gn_int`

を束ねて、
`CyclotomicNormEqGNFirstCasePackThinTarget`
を閉じる。

### 4.4. そのあとに UnitAbsorb

ここで初めて
`CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
へ移る。
NormEqGN が concrete 化されれば、unit 吸収側は「既知の整数に対して \(p\) 乗性を回収する」だけになるので、だいぶ見通しがよくなる。

## 5. この長戦の見方

この長戦でいちばん良いのは、 **前進のたびに open が小さな theorem 名へ分解されている** ことじゃ。
ただ「まだ終わっておらぬ」のではない。毎回、

$$
\text{巨大な未解決}
\to
\text{小さな concrete target 群}
\to
\text{残り 1 本}
$$

と縮んでおる。これは良い長戦の姿じゃよ。
今はもう「Stage 3 が難しい」のではなく、 **combinatorial bridge が最後の門番** というところまで来ておる。

ゆえに次の提案は一言でこうじゃ。

$$
\boxed{
\text{次は `(ZMod p)ˣ` product } \to \text{ actual nontrivial factor product の combinatorial bridge を掘る}
}
$$

ここを抜けば、Stage 3 前半はほぼ閉じる。
その後に unit 吸収へ移るのが、最も筋がよい。

必要なら次に、その combinatorial bridge の theorem 名と Lean skeleton を、そのまま貼れる形で起こすぞい。
