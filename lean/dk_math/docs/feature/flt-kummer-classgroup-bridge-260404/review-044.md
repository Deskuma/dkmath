# FLT-Kummer-Bridge Stage 3 Review #44: Stage 3 の `hProduct` 追放戦の総括と次の一手

## 1. 総評

よくここまで掘ったの。これは単なる「進んだ」ではなく、**詰まりどころの種類が何度も再分類され、最後にかなり細く局所化された** 長戦じゃ。

流れを通して見ると、最初は first-case の Stage 3 全体が大きな open だった。そこからまず `NormEqGN` と `UnitAbsorb` に分割され、さらに norm 側は差冪商から (GN) への橋、product-level rewriting、Galois / units product などへ分解された。ついには `NormEqGN` と `UnitAbsorb` の両方が concrete 化され、first-case の Stage 3 split 自体は no-sorry で閉じた。ここはもう未解決本体ではない、と言ってよい。

その後の戦いは、**legacy route をどう新しい concrete 部品へ差し替えるか** と、**`hProduct` をどこまで interface から押し出せるか** へ移った。class-group 仮定から first-case concrete contradiction へ戻す stable bridge が `CyclotomicPrincipalization.lean` 側に固定され、さらに gap-divisible witness まで stable bridge 群だけで返せる形になった。この時点で、first-case 枝の差し替え先は理論としてではなく theorem 名として mainline に揃った、と読むべきじゃ。

さらに重要なのは、その後の切り分けじゃ。`hLinNe` は product identity から自動供給できるようになり、y-branch contradiction と pairwise coprimality は full product identity なし、つまり local factorization core だけで閉じると theorem-level に確定した。ここで `hProduct` の用途は大きく削れた。

そして決定打が、direct norm-eval route じゃ。`Norm(a-\zeta)` を cyclotomic polynomial の評価へ戻す product-free 補題が立ち、その specialized application と homogeneous evaluation から、chosen factor の整数 norm 自体が **full product identity を使わず** 直接 (GN,p,(z-y),y) に一致すると示せた。これにより `CyclotomicNormEqGNFirstCasePackThinTarget` は interface レベルでも `hProduct` から解放され、続いて `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` も concrete theorem を見直すと `hProduct` を実際には使っておらず、同様に interface から外された。今の logs を流れで読む限り、Stage 3 の中核 2 target はどちらも **hProduct-free** になった、というのが最大の地殻変動じゃ。

## 2. いま何が勝っていて、何が残っているか

勝っているのは明白じゃ。

first-case の Stage 3 本体。
これはもう concrete で、`NormEqGN` も `UnitAbsorb` も、さらには `GN = s^p` 回収と contradiction bridge まで stable theorem 群として mainline に乗っておる。よって「first-case の Stage 3 を埋められるようになったか」と問われれば、答えは **はい** じゃ。しかも一時しのぎではなく、部品分解と再配線を経たうえで埋まっておる。

残っているのは、`cyclotomicPrincipalization_of_classGroupPTorsionFree` などの **legacy one-shot 設計** と、その downstream routing じゃ。しかも最近のログを通して見ると、ここでの本当の blocker は「理論が足りない」ではなく、**global pack から何を canonical に供給できるか** と、**旧 wrapper がどこでまだ old architecture にしがみついているか** の 2 点に縮んでおる。とくに `CyclotomicPureFactorizationIdentityTarget` から `CyclotomicIdealEquationTarget` までが `True` placeholder のままなので、そこから `hProduct` を canonical に引く筋は現状ない、と自分で確認できておる。ここは大きい。つまり「掘れば出る金脈」ではなく、「上流がまだ仮設」なのじゃ。

## 3. 流れから見た真のボトルネック

ここが肝じゃ。

途中までは「残る本丸は `hProduct` 供給定理だ」と読めた。実際、productEq-only bridge が出来た段階ではそうじゃった。だが、その後の direct route により、Stage 3 の `norm = GN` と `UnitAbsorb` から `hProduct` は消えた。y-branch contradiction と pairwise coprimality も product-free になった。すると、今 `hProduct` が残るのは主に **unit-normalization chain**、より具体的には `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` 周辺だと自分で整理しておる。ここがいまの真ボトルネックじゃ。

つまり、戦況はこう変化したのじゃ。

以前の見立て：
「legacy one-shot を裂く最後の concrete blocker は `hProduct` 供給定理」

現在の見立て：
「`hProduct` は Stage 3 からほぼ退き、unit-normalization chain に局在した」

この変化は大きい。ここを読み違えると、不要な full product theorem を掘り続けてしまう。

## 4. 次の戦略

わっちの推論では、次の筋はもうかなり明確じゃ。

### 4.1. 推奨主戦略

**`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の依存を再分解し、`hProduct` が本当に必要な最小核を特定する。**

いまや Stage 3 本体は product-free に近づいた。y-branch も product-free。なら、次に狙うべきは normalization chain のどこで `hProduct` が indispensable なのか、その一点を pinpoint することじゃ。
ここでは theorem をいきなり潰そうとせず、まず dependency graph を明文化するのがよい。どの補題が

* ideal の (p) 乗化
* chosen factor の element-level normalization
* tail ideal との coprimality
* pairwise factor coprimality

のどこに効いているかを列挙し、`hProduct` 依存と `local factorization` 依存を分離する。
この作業は数学というより設計じゃが、いまの局面ではこれが最も効く。

### 4.2. 非推奨だが代替の筋

**global pack から `CyclotomicLinearFactorProductEqInRingOfIntegers` を canonical に供給する direct theorem を掘る。**

これは以前は本命候補だった。だが、上流 target が placeholder のままという自己観測が出ておる以上、今ここへ深く潜るのは危うい。もちろん完全に捨てる必要はないが、優先度は下がった。product identity 自体が必要な箇所が局所化された以上、先に normalization 側を薄くする方が勝率が高い。

## 5. 具体的な提案指示

次の号令は、わっちならこう出す。

### A. まず dependency の棚卸し

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の proof で `hProduct` が使われている箇所を、**行単位ではなく責務単位** で 3 つか 4 つに分ける。

推奨分類は

1. chosen factor の ideal-level (p) 乗化
2. chosen factor と tail / other factors の coprimality
3. principality から element-level equality `u * β^p` への降下
4. first-case 条件 `¬ p ∣ gap` の使用点

じゃ。
この分類で `hProduct` が実は 1 と 2 のどちらにしか効いていないなら、次の一手が見える。

### B. local factorization ベースの normalization 代替核を試す

`chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack` が既にある以上、chosen factor と tail-sum の一因子版 factorization は mainline にある。これを使って

$$
\text{chosen factor} \cdot \text{tail-sum} = x^p
$$

から ideal-level の (p) 乗性あるいは principality に近いものが取れぬかを試す。
少なくとも pairwise / y-branch 側は already product-free なのだから、ここに新しい local normalization lemma を差し込めれば、`hProduct` の最後の島が崩れる可能性が高い。

### C. 旧 route への直結は、そのあと

`FLTPrimeGe5Target_of_kummerRoute` の case split 化や `cyclotomicPrincipalization_of_classGroupPTorsionFree` の縮約は、いまでもやれるが、真に効くのは normalization 依存の再分解が済んでからじゃ。
いま無理に旧 route の proof を触ると、hProduct 依存の黒箱を抱えたまま配線だけいじることになる。これは長戦を長引かせる。

## 6. 「sorry 埋められるようになったのか」への、今回ログ込みの答え

うむ。より正確に言うと、

* first-case Stage 3 を concrete に閉じる力は、もう確立した。
* その後の解析で、`hProduct` 依存も Stage 3 からかなり追い出せた。
* したがって、今残る `sorry` は「未踏の理論」より「旧設計の縮約」と「normalization chain の局所依存」の問題に近い。

なので答えは、

**はい、埋められる領域は増えた。しかも今は “どこを埋めれば全体が縮むか” までかなり見えておる。**

じゃよ。

## 7. 最終判断

わっちの総括はこれじゃ。

この長いログの流れは、
**Stage 3 concrete 化 → first-case branch の stable bridge 化 → y-branch / coprimality の product-free 化 → direct norm-eval route による `hProduct` 追放**
という一直線の改善になっておる。途中の試行錯誤は多いが、方向はぶれておらぬ。むしろ後半ほど、敵の正体がはっきりしておる。

だから次の一手は、

$$
\boxed{
\text{`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の依存を責務ごとに解体し、
local factorization ベースの normalization 代替核を探れ}
}
$$

これが最も筋がよい。
global full product theorem を先に掘るより、こちらの方が早く本丸を細らせる可能性が高い。

必要なら次に、`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の dependency 分解用 checklist を、そのまま作業メモとして起こすぞい。

---

うむ、起こしたぞい。
これは **`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` 依存分解メモ** として、そのまま作業に使える形で書く。

## 1. 目的

目的は 1 つじゃ。

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` に残っている `hProduct` 依存が、

$$
\text{本当に本質なのか}
$$

それとも

$$
\text{old route の名残なのか}
$$

を、責務ごとに切り分けることじゃ。

いまの戦況では、first-case の Stage 3 中核 2 target

* `CyclotomicNormEqGNFirstCasePackThinTarget`
* `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`

はどちらも `hProduct` から外れた。
さらに y-branch contradiction と pairwise coprimality も product-free 版が立っておる。
ゆえに、残る `hProduct` は **ほぼ unit-normalization chain に局在** している、という見立てでよい。
このメモは、その局在を証明レベルで確認するためのものじゃ。

---

## 2. 先に確定していること

作業開始前に、もう掘らなくてよい箇所を固定する。

### 2.1. もう `hProduct` 不要と見なしてよい層

* `Norm = GN` 直結
* `UnitAbsorb`
* y-branch contradiction
* chosen factor と他因子の coprimality のうち、first-case / local factorization だけで閉じる部分

つまり、以下は **再調査対象にしない** 。

* `chosenCyclotomicLinearFactor_norm_eq_gn_direct`
* `cyclotomicNormEqGN_concrete_firstCase_packThin`
* `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`
* `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct`
* `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_counterexamplePack`

ここをもう一度掘り返すのは、長戦を無駄に伸ばすだけじゃ。

### 2.2. いま未確定の層

再調査対象は、ほぼこれだけじゃ。

* `cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
* それへ流れ込む ideal-level principalization chain
* その chain の中で `hProduct` を要求する補題群
* その周辺の tail ideal / chosen factor packaging

---

## 3. 責務分解テンプレ

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` を、proof script の順でなく **責務の順** に 4 分割して見る。

### 3.1. 責務 A. ideal-level の `p` 乗化

ここで見たいものは

$$
\langle z - \zeta y \rangle = I^p
$$

あるいはそれに類する ideal equality が、どの補題から来ているかじゃ。

ここで確認する問いは 3 つ。

* `hProduct` は **ideal equality の構成** に直接要るか
* 要るなら、それは full product identity そのものか
* それとも local factorization から取れる weaker な equality で足りるか

### 3.2. 責務 B. chosen factor と tail / other factor の coprime 化

ここはかなり怪しい。
というのも、first-case の pairwise / y-branch は product-free に落ちておるから、old chain が惰性で `hProduct` を渡しているだけの可能性が高い。

ここで見る問いはこうじゃ。

* その coprime 証明は本当に full product identity を使っているか
* 実際には `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct` へ差し替えられぬか
* tail 側の ideal についても local factorization だけで十分でないか

### 3.3. 責務 C. principal ideal から element equality への降下

ここは

$$
z - \zeta y = u \cdot \beta^p
$$

を返す最後の段じゃ。
この段は普通、`span = I^p` と principality から出るので、`hProduct` が要るなら多くは A に起因する。
C 自体が `hProduct` を本質使用していることは少ないはずじゃ。

よって確認する問いは 1 つ。

* C は A の結果を受けるだけか、それとも C 自身でも `hProduct` を参照しているか

### 3.4. 責務 D. first-case 条件 `¬ p ∣ gap` の使用

これは `hProduct` と別軸じゃが、依存分解の時に一緒に見ておくとよい。
理由は、`hProduct` が必要に見える箇所の一部が、実は本当に欲しいのは `¬ p ∣ gap` から出る prime-over-(p) contradiction である場合があるからじゃ。

---

## 4. 実作業チェックリスト

ここから先は、そのまま TODO として使ってよい。

### 4.1. Step A. 依存表を作る

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の proof に出る直接依存 theorem を全部列挙する。
列はこの 5 本でよい。

* theorem 名
* 役割
* `hProduct` 使用の有無
* `hLinNe` 使用の有無
* local factorization 代替の可能性

この表を作るだけで、かなり霧が晴れる。

### 4.2. Step B. `hProduct` 使用箇所に印を付ける

proof script の各 `have` / `obtain` / `exact` について、

* `hProduct` を **直接** 使う
* `hProduct` 依存 theorem を **間接** に呼ぶ
* `hProduct` 不要

の 3 色で分類する。

目的は「どこで使っているか」ではなく、

$$
\text{どの責務に属する use か}
$$

を確定することじゃ。

### 4.3. Step C. B のうち coprime 系を product-free 版へ置換できるか試す

ここが最優先の差し替え候補じゃ。

もし old theorem が

* y-branch contradiction
* chosen factor と他因子の common-prime 排除
* pairwise coprimality

のどれかを `hProduct` 付きで出しているなら、まず product-free 版へ置換して build を見る。

この段で build が通るなら、`hProduct` 使用箇所はさらに減る。

### 4.4. Step D. ideal-level `p` 乗化の入口を isolated theorem 化する

A が残るなら、その核だけを新 theorem 名で切り出す。
たとえば思想としては

```lean
theorem chosenFactorSpanEqPow_of_firstCase_<route>
```

のような形じゃ。

ここで重要なのは、**まだ証明できなくても theorem 境界を切ること** じゃ。
境界が切れれば、その先は C と分離される。

### 4.5. Step E. local factorization ベースの代替核を試す

すでにある

`chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack`

を使って、ideal-level に何が言えるかを試す。
狙いは full product identity の完全代替でなくてよい。

たとえば、

$$
\langle z - \zeta y \rangle \cdot J = \langle x \rangle^p
$$

型の weaker な packaging でも、principalization の入口として十分なことがある。
ここは exploratory でよいが、**試す価値が最も高い場所** じゃ。

---

## 5. 判定基準

作業が進んだかどうかは、次の 3 段で判定する。

### 5.1. 小勝利

`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の依存表で、`hProduct` が 1 箇所か 2 箇所に局所化されたと確認できる。

### 5.2. 中勝利

coprime 系依存を product-free 版へ差し替えた結果、`hProduct` が ideal-level `p` 乗化の入口にしか残らなくなる。

### 5.3. 大勝利

local factorization ベースの代替核が立ち、

$$
\text{unit-normalization chain 全体}
$$

からも `hProduct` を押し出せる見通しが立つ。

---

## 6. 今やってはいけないこと

長戦では、やらぬことも大事じゃ。

### 6.1. full product identity の global canonical supply を先に掘りに行く

これは以前は本命に見えたが、いまは優先度が下がっておる。
理由は、Stage 3 本体と y-branch がすでに product-free 化しておるからじゃ。
先に normalization 側を薄くする方が早い。

### 6.2. legacy route 本体をいきなり書き換える

`FLTPrimeGe5Target_of_kummerRoute` や
`cyclotomicPrincipalization_of_classGroupPTorsionFree`
を先に大改造すると、黒箱 dependency を抱えたまま proof が崩れる危険がある。

### 6.3. `hLinNe` をもう一度 blocker 扱いする

これはもう product identity から自動供給できると立っておる。
再び「`hLinNe` が足りない」と見るのは誤読じゃ。

---

## 7. 次の号令

わっちなら、作業指示はこう出す。

1. `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` の proof を責務 A/B/C/D に分けた依存表を作れ。
2. `hProduct` を使う箇所を direct / indirect / unnecessary に色分けせよ。
3. coprime / y-branch / pairwise reasoning に属するものは、product-free theorem 群へ差し替え可能かを順に試せ。
4. 残った `hProduct` 使用箇所についてのみ、ideal-level `p` 乗化の isolated theorem を切り出せ。
5. その isolated core が local factorization equality で代替できるか、`chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack` を起点に探索せよ。

---

## 8. ひとことで言うと

いまの本丸は

$$
\text{full product theorem を取ること}
$$

ではなく、

$$
\text{unit-normalization chain の中で `hProduct` が残る最小核を剥き出しにすること}
$$

じゃ。

そこまでできれば、次の一手は自然に見える。
必要なら次に、この checklist をそのまま Lean ファイル横に置ける Markdown の作業ログ形式へ整えてやるぞい。
