# FLT-Kummer-ClassGroup-Bridge 260404 Review 007

要約: Stage 1a-1 をさらに 2 層へ割る提案。

## 1. 状況分析

これは良い薄化じゃ。
今回の変更で、Stage 1a はついに

$$
\text{ideal factorization}
\;\to\;
\text{ideal product p-th power}
\;\to\;
\text{class p-torsion witness}
$$

の 3 層へ割れ、theorem-level の最薄 kernel が

$$
\texttt{cyclotomicIdealFactorization\_of\_gapDivisibleGeometry}
$$

にまで局所化された。
この一点が、いま本当に噛むべき場所じゃ。

前回までの流れで、Stage 1b は generic ClassGroup API 側、Stage 1c は principal ideal extraction 側へかなり整理されておった。今回さらに Stage 1a-2 と Stage 1a-3 が clean bridge として分離されたので、 **「どこが genuinely cyclotomic で、どこが下流整理か」** が、かなり明瞭になったのぅ。

## 2. 数学的な解説

いまの図式を数学の意味で言い直すと、こうじゃ。

まず Stage 1a-1 では、gap-divisible 条件から円分体整数環の中で扱うべき ideal の factorization を作る。
次に Stage 1a-2 で、その factorization を ideal equation に押し込み、

$$
I_0 I_1 \cdots I_{p-1} = J^p
$$

のような「ideal product が p 乗になる」形へ寄せる。
最後に Stage 1a-3 で、それを class group へ落として

$$
[I]^p = 1
$$

型の p-torsion witness を得る。

この分解は筋が良い。
なぜなら、Stage 1a-2 と 1a-3 は少なくとも抽象責務としては **Dedekind / ideal arithmetic / class-group 演算** の側へ押しやすいが、Stage 1a-1 だけは

$$
x^p + y^p
$$

の cyclotomic factorization と gap-divisible 条件そのものに根を持つからじゃ。
つまり、今回の変更で「本当に新理論が要る場所」が Stage 1a-1 に集中した、と読める。

## 3. 今の戦況の意味

ここで大事なのは、 **open kernel が 1 個に見える** ということと、 **その kernel の中身の地図ができた** ということは別だ、という点じゃ。

いま見えておるのは後者じゃ。
`cyclotomicIdealFactorization_of_gapDivisibleGeometry` に `sorryAx` が残っておるが、その内側ももう無色透明な黒箱ではない。少なくとも、

* factorization identity
* ideal equation への変換
* class への落とし込み

という責務境界が見えておる。これは大きい。
証明が進んだというより、 **証明すべきものの輪郭が sharpen された** のじゃ。

## 4. 次の一手の推論

ぬしの報告にもある通り、次の分岐は実質ひとつじゃ。

$$
\texttt{cyclotomicIdealFactorization\_of\_gapDivisibleGeometry}
$$

を、さらに Dedekind ideal arithmetic と cyclotomic factorization の境界で裂くべきかどうか。
わっちの見立てでは、 **裂くべき** じゃ。

理由ははっきりしておる。

今の `cyclotomicIdealFactorization_of_gapDivisibleGeometry` には、少なくとも 2 種類の仕事が混ざっておるはずじゃ。

ひとつは、円分体側での **代数的因数分解そのもの**。
つまり

$$
x^p + y^p
$$

が cyclotomic factor にどう分かれるか、という ring / polynomial / number field 側の話じゃ。

もうひとつは、その因数分解を **整数環の ideal statement** に変換する仕事。
こちらは factorization identity そのものではなく、integrality、ideal 生成、積、場合によっては互いに素性や divisibility を扱う、Dedekind 的整理の仕事じゃ。

この 2 つは同じではない。
だから、いまの kernel をさらに

$$
\text{factorization identity}
\quad\text{と}\quad
\text{ideal equation packaging}
$$

に分ける価値が高い。

## 5. 提案

わっちなら、次は Stage 1a-1 をさらに 2 層へ割る。

### 5.1. 第一層

**cyclotomic factorization identity** を独立 target 化する。
ここではまだ ideal へ降ろさず、円分体あるいはその分数体で

$$
x^p + y^p
$$

の分解がどう書けるか、という **純代数的・純 factorization 的主張** を扱う。

たとえば役割としては、

$$
\text{gap-divisible geometry}
\to
\text{cyclotomic factorization identity}
$$

じゃ。

### 5.2. 第二層

その factorization identity を、整数環の **ideal equation** へ変換する target を立てる。
ここで初めて Dedekind ideal arithmetic を使う。

つまり

$$
\text{cyclotomic factorization identity}
\to
\text{ideal factorization / ideal equation}
$$

を分離するわけじゃ。
これで `CyclotomicIdealFactorizationTarget` 自体も、さらに

* factorization identity side
* ideal packaging side

へ薄くなる。

## 6. なぜこの順が良いか

この順が良いのは、次の判定ができるからじゃ。

もし factorization identity 側がすぐ書けるなら、残る重さはほぼ ideal packaging 側にある。
逆に factorization identity の時点で詰まるなら、本当に必要なのは cyclotomic algebra / number-field 側の新理論だと分かる。

どちらに転んでも、次の工程が明瞭になる。
いまの kernel をそのまま抱えておるより、ずっと良い。

## 7. 実務的な次手

実務としては、まず 2 つだけ新 target を置くのがよい。

ひとつは仮に

`CyclotomicFactorizationIdentityTarget`

のようなもの。
もうひとつは

`CyclotomicIdealEquationTarget`

のようなものじゃ。

そして

$$
\texttt{cyclotomicIdealFactorization\_of\_gapDivisibleGeometry}
$$

を、この 2 段の composition theorem に組み替える。
すると、現在の theorem-level kernel はさらにどちらか一方へ押し込める。そこまで行けば、本当に書くべき新補題の種類がもっとはっきりする。

## 8. 最終提案

結論を一言で言うと、次はこうじゃ。

$$
\boxed{
\text{Stage 1a-1 を }
\text{factorization identity}
\to
\text{ideal equation packaging}
\text{ の 2 層へさらに裂く}
}
$$

これが最も筋が良い。
Stage 1b 側はもう十分整理された。Stage 1a-2, 1a-3 も責務が見えた。
ならば次に噛むべきは、 **truly cyclotomic な最上流 factorization kernel** そのものじゃ。そこを薄く割れば、いよいよ本丸の正体が露わになるはずじゃよ。
