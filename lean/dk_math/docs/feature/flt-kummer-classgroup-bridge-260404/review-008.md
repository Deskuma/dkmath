# FLT-Kummer-ClassGroup-Bridge-260404 Review-008

## 1. 状況分析

これはかなり良い整理じゃ。
今回ので、theorem-level の最薄 kernel はついに

$$
\texttt{cyclotomicFactorizationIdentity\_of\_gapDivisibleGeometry}
$$

へ移った。
つまり、これまで `cyclotomicIdealFactorization_of_gapDivisibleGeometry` に混ざっておった

* **純粋な cyclotomic factorization**
* **ideal equation への包装**

の 2 つの責務が、とうとう別れたわけじゃ。これは大きい。

いまの Stage 1a の地図は、ぬしの報告どおり

$$
\text{factorization identity}
\to
\text{ideal equation packaging}
\to
\text{ideal product p-th power}
\to
\text{class witness}
$$

の 4 層になっておる。
このうち clean bridge として分離できたのは

* `cyclotomicIdealEquation_of_factorizationIdentity`
* `cyclotomicIdealProductPthPower_of_idealFactorization`
* `cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower`

で、`sorryAx` が残るのは最上流の `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` だけ、という形じゃ。
これは戦況として、とても澄んでおる。

## 2. 解説

数学的に言うと、いま残っておる芯は「ideal に落とす前」の段じゃ。
つまり、本当に未解決なのは

$$
x^p + y^p
$$

に対して、gap-divisible 条件のもとで **どの cyclotomic factorization identity を採用すべきか**、あるいは **どの形で取り出すのが後段に自然か** という部分じゃよ。

ここで重要なのは、`ideal equation packaging` が clean bridge として分離されたことで、Dedekind 側・integrality 側・ideal generation 側の責務は、少なくとも theorem の境界としては factorization identity から切り離せた、という点じゃ。
ゆえに、ここから先の genuinely cyclotomic な新理論は、ほぼ

$$
\text{factorization identity theorem}
$$

そのものの内側に集中しておる、と見てよい。

## 3. 次の一手の推論

わっちの見立てでも、次は

$$
\texttt{cyclotomicFactorizationIdentity\_of\_gapDivisibleGeometry}
$$

をさらに裂くのが最善じゃ。
しかも、ただ裂くのではなく、 **「純 factorization identity」** と **「gap-divisible 条件を使う点」** を分ける方向がよい。

なぜなら、いまの theorem 名から見ても、`of_gapDivisibleGeometry` という後半は「入力条件」、`FactorizationIdentity` という前半は「出したい本体」じゃ。
この 2 つが同居しておるなら、次に確かめるべきことは自然にこうなる。

$$
\text{gap-divisible は本当に factorization identity 自体に要るのか}
$$

それとも

$$
\text{factorization identity はもっと純粋に成り立ち、
gap-divisible はその特殊化や後段への接続で初めて要るのか}
$$

という判定じゃ。

わっちは後者の可能性が高いと見る。
ふつう cyclotomic factorization そのものは、より広い環境で成り立つ純代数的恒等式であって、`q \mid (z-y)` のような条件は、その identity を **どの因子に着目するか**、あるいは **どの integral / ideal 形に落とすか** で初めて効くことが多いからじゃ。

## 4. 提案

わっちなら、次は `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` を次の 2 段へ裂く。

### 4.1. 純 factorization identity

仮に

$$
\texttt{CyclotomicPureFactorizationIdentityTarget}
$$

のような target を置く。
これは gap-divisible 条件を持たず、できるだけ純粋に

$$
x^p + y^p
$$

の cyclotomic factorization だけを言う器じゃ。
ここではまだ ideal に落とさぬ。純代数じゃ。

### 4.2. gap-divisible specialization

次に、その純 factorization identity から、gap-divisible 条件のもとで後段に使える形へ specialize する bridge を置く。
仮に

$$
\texttt{CyclotomicGapDivisibleFactorizationSpecializationTarget}
$$

のようなものじゃな。

この分割をすると、次のことが判定できる。

* もし純 factorization identity がすぐ書けるなら、真の本丸は specialization 側
* もし純 factorization identity 自体で詰まるなら、本当に必要なのは cyclotomic algebra / number-field 側の新理論

どちらに転んでも得じゃ。

## 5. 実務的な推奨順

順番としてはこうじゃ。

まず theorem を完成させようとせず、target だけ 2 つ追加する。
そして

$$
\texttt{cyclotomicFactorizationIdentity\_of\_gapDivisibleGeometry}
$$

を wrapper に落とす。
そのうえで、scratch か小補題で

* gap-divisible を使わずに書ける最小の factorization identity は何か
* gap-divisible が初めて必要になるのは「因子の選別」か「divisibility」か「integrality」か

を確認する。

ここで特に見たいのは、 **gap-divisible が factorization の本体に要るのか、後段の正規化に要るのか** じゃ。
この一点が見えれば、上流 kernel の中身はさらに澄む。

## 6. 最終提案

結論を一言で言うと、次はこうじゃ。

$$
\boxed{
\texttt{cyclotomicFactorizationIdentity\_of\_gapDivisibleGeometry}
\text{ を }
\text{純 factorization identity}
\to
\text{gap-divisible specialization}
\text{ の 2 層へ裂く}
}
$$

これがいま最も筋が良い。
ここまで来れば、残る本丸はほとんどその theorem の内側にしかおらぬ。
次の仕事は、「どこで初めて gap-divisible が要るのか」を暴き、その一点へ新理論を押し込むことじゃよ。
