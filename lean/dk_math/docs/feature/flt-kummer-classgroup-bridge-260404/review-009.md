# FLT-Kummer-ClassGroup-Bridge-260404 Review-009

## 1. 状況分析

これは良い収束じゃ。
今回の変更で、theorem-level の最薄 kernel はついに

$$
\texttt{cyclotomicPureFactorizationIdentity\_of\_counterexampleGeometry}
$$

へ移った。つまり、これまで上流に混ざっておった

* 純粋な cyclotomic factorization
* gap-divisible 条件の利用
* ideal equation への包装
* ideal product への押し込み
* class witness への落下

が、いまや

$$
\text{pure factorization identity}
\to
\text{gap-divisible specialization}
\to
\text{ideal equation}
\to
\text{ideal product}
\to
\text{class witness}
$$

の 5 層として見えておる。これはかなり澄んだ地図じゃ。

しかも `cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity` は clean bridge になっておる。ゆえに、 **gap-divisible 条件そのものは、もはや最上流 kernel ではない** と判定できたわけじゃ。いま本当に重いのは、pure factorization identity 側じゃよ。

## 2. 解説

数学的に見ると、今回の薄化はとても意味がある。

以前は

$$
\text{gap-divisible geometry}
\Rightarrow
\text{factorization identity}
$$

が 1 本に束ねられておった。
だが今回それを

$$
\text{counterexample geometry}
\Rightarrow
\text{pure factorization identity}
$$

と

$$
\text{pure factorization identity}
\Rightarrow
\text{gap-divisible specialization}
$$

に分けたことで、 **「gap-divisible は factorization 本体には本質でないかもしれぬ」** という構造が theorem-level で見えるようになった。

これは大事じゃ。
もし gap-divisible が specialization 側でしか要らぬなら、最上流の核はもっと純代数的な定理へ押し戻せる。そうなれば、後段の Kummer / ideal arithmetic との責務境界はさらに明瞭になる。

## 3. 次の一手の推論

わっちの見立てでも、次に進むべき場所ははっきりしておる。

$$
\texttt{cyclotomicPureFactorizationIdentity\_of\_counterexampleGeometry}
$$

をさらに裂くことじゃ。
しかも、裂く方向もかなり明白じゃ。

今この theorem には、少なくとも 2 種類の責務が混ざっておるはずじゃ。

ひとつは **純 factorization identity そのもの**。
これは反例 pack の全情報を必ずしも要せぬ、より広い代数的恒等式である可能性が高い。

もうひとつは、その恒等式を **PrimeGe5CounterexamplePack の具体状況へ specialize する仕事**。
たとえば (p) が素数、(x,y,z) が pack 条件を満たす、順序条件や互いに素条件など、factorization を usable な形へ落とすための周辺情報じゃ。

つまり次の分岐は、

$$
\text{pure identity}
\quad\text{と}\quad
\text{counterexample-pack specialization}
$$

を分けられるか、という一点にある。
わっちは **分けられる可能性が高い** と見る。なぜなら、cyclotomic factorization の本体は通常もっと一般に成り立ち、反例 pack はその使用条件を整えるために要ることが多いからじゃ。

## 4. 提案

次は `cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` を、さらに 2 層へ裂くのが最善じゃ。

### 4.1. 純 factorization identity 層

仮に

$$
\texttt{CyclotomicAbstractFactorizationIdentityTarget}
$$

のような target を置く。
ここでは `PrimeGe5CounterexamplePack` を使わず、できるだけ一般の代数的状況で

$$
x^p + y^p
$$

の cyclotomic factorization を表す。
つまり「本当に核となる恒等式」を isolatｅ する層じゃ。

### 4.2. 反例 pack specialization 層

その上で、

$$
\texttt{CyclotomicCounterexampleSpecializationTarget}
$$

のような bridge を置き、一般恒等式を `PrimeGe5CounterexamplePack` の状況へ落とす。
ここで初めて、pack のどの成分が必要かを点検する。

この分割の利点は大きい。
pack のうち本当に要る仮定が、

* `p` の素数性だけなのか
* `x,y,z` の等式だけなのか
* 互いに素条件まで要るのか
* 大小関係まで要るのか

を、theorem-level で切り出せるからじゃ。

## 5. 具体的な作業順

わっちなら、次はこう進める。

まず新しい仮 target を 2 本だけ足す。

* pure abstract factorization identity
* counterexample geometry からその identity への specialization

そして現行の

$$
\texttt{cyclotomicPureFactorizationIdentity\_of\_counterexampleGeometry}
$$

を wrapper に落とす。
この時点では中身が placeholder でもよい。狙いは、 **最上流 kernel の内部責務を theorem 名レベルでさらに露出すること** じゃ。

その後で、scratch あるいは小補題で `PrimeGe5CounterexamplePack` の各成分を順に外してみて、どれが本当に要るかを確かめる。
ここで「実は (hEq) と (p) の条件だけで純 factorization は書ける」という形が見えれば、大勝利じゃ。

## 6. 最終提案

結論を一言で言うと、次の一手はこれじゃ。

$$
\boxed{
\texttt{cyclotomicPureFactorizationIdentity\_of\_counterexampleGeometry}
\text{ を }
\text{純 factorization identity}
\to
\text{counterexample-pack specialization}
\text{ の 2 層へ裂く}
}
$$

そのうえで、 **`PrimeGe5CounterexamplePack` のどの成分が本当に必要かを監査する**。
ここまで来ると、本丸はほぼその theorem の内側にしか残っておらぬ。いま噛むべきは、まさにそこじゃよ。
