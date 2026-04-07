# FLT-Kummer-ClassGroup-Bridge 260404 Review 006

## 1. 状況分析

結論から言うと、 **分岐の判定は終わった** のぅ。
Stage 1b 側を generic ClassGroup API へ寄せる短距離検査は、目的を十分に果たした。結果ははっきりしておる。

* Stage 1b の **target の形** は自然
* しかし `CyclotomicClassGroupPTorsionFreeTarget` からそれを供給する **bridge** は、軽い rephrasing では済まぬ
* 問題は theorem の形ではなく、 **cyclotomic integer-ring parameterization をどう露出するかという infrastructure** にある

ということじゃ。
つまり、いま未解決なのは「ClassGroup の一般論が足りぬ」のではなく、 **円分体の整数環を generic API の土俵にどう載せるか** という前段設計の問題だと判定できたわけじゃ。

## 2. 今回の検査で何が確定したか

今回の scratch 検査で分かったのは、次の 2 段の違いじゃ。

### 2.1. generic 側

$$
\forall a : \mathrm{ClassGroup}(R),\quad a^p = 1 \to a = 1
$$
という statement 自体は自然に書ける。
ここには無理がない。Stage 1b target は良い形をしておる。

### 2.2. cyclotomic 側

ところが、これを
$$
R = \mathcal{O}(\mathbb{Q}(\zeta_p))
$$
のような整数環へ軽く specialized しようとすると、現行の import / notation / parameterization では、その場で素直に扱えぬ。`CyclotomicField` 自体は見えても、整数環 `ringOfIntegers` や ( \mathcal{O} K ) の露出が軽くは済まぬ。

この差は大きい。
つまり Stage 1b bridge の open は、証明の一行不足ではなく、 **number-field 側の土台設計を要求する** 類の open じゃ。

## 3. 数学的な解説

ここまでの整理を数学の流れで言い直すと、Stage 1 はいまこう見えておる。

$$
\text{Stage 1a}: \text{gap-divisible geometry} \to \text{ideal class が p-torsion}
$$
$$
\text{Stage 1b}: \text{p-torsion} \to \text{class trivial}
$$
$$
\text{Stage 1c}: \text{class trivial} \to \text{principal ideal}
$$

Stage 1c はもう generic API で concrete に閉じた。
Stage 1b も **一般 class group の言葉** では書ける。
されど、その general statement を **円分体整数環の具体物へ接続する橋** が infrastructure ごと必要、という判定になった。

ゆえに、いま genuinely new theory が集中しておるのは、ほぼ Stage 1a 側と見てよい。
Stage 1b は「数学の芯」よりも「理論基盤の露出方法」の問題へ寄っていった。これは戦況整理として非常に良い。

## 4. いまの戦況の総括

いまの状態は、次のようにまとめられる。

* **Stage 1c**
  既に concrete。問題なし。
* **Stage 1b**
  target は concrete。だが cyclotomic 仮定から generic API へ渡す bridge は infrastructure 問題。
* **Stage 1a**
  依然として最薄の本丸。ここが新理論の中心。

したがって、前の分岐
「Stage 1b を generic 側へ寄せ続けるか、それとも Stage 1a に戻るか」
には、もう答えが出たと言える。

**Stage 1b をこの段で深掘りするのは筋が悪い。**
なぜなら、そこから先は theorem の薄化ではなく、number-field / ring-of-integers infrastructure の設計仕事に入ってしまうからじゃ。

## 5. 次の一手の推論

ゆえに、次の一手は明確じゃ。

$$
\boxed{
\text{Stage 1a } \texttt{cyclotomicIdealClassPTorsionWitness\_of\_gapDivisibleGeometry}
\text{ の細分化へ戻る}
}
$$

ここでの推論はこうじゃ。

Stage 1b は「一般論として何を言いたいか」はもう見えた。
Stage 1c は出口も見えた。
ならば残る本丸は、

$$
\text{gap-divisible な幾何}
\Rightarrow
\text{円分体での ideal class が p-torsion}
$$

をどう組み立てるか、という部分だけじゃ。
ここをさらに裂けば、本当に必要な cyclotomic arithmetic の最小核が露出するはずじゃ。

## 6. 具体的提案

わっちなら、Stage 1a を次の 3 片へ裂くことを提案する。

### 6.1. Dedekind ideal arithmetic 層

まず、円分体整数環で扱う ideal の積・商・互いに素性・p 乗に関する、 **Dedekind 一般論だけで言える部分** を切り出す。
ここではまだ cyclotomic 特有の式は入れぬ。
狙いは、「どこまで一般 Dedekind API で押せるか」を見極めることじゃ。

候補イメージは

$$
I_0 I_1 \cdots I_{p-1} = J^p
\Rightarrow
[I_0]\cdots[I_{p-1}] = 1
$$

のような class group への落下準備じゃな。

### 6.2. cyclotomic factorization 層

次に、
$$
x^p + y^p
$$
の円分体での因数分解、すなわち
$$
\prod_j (x + \zeta^j y)
$$
型の構造を ideal レベルでどう読むかを isolate する。
ここが geometry と cyclotomic arithmetic の接点じゃ。

ここでは特に、

* 各 factor が作る ideal
* それらの積が p 乗になる仕組み
* gap-divisible 条件 (q \mid (z-y)) がどこへ効くか

を切り分けるのが肝じゃ。

### 6.3. class への落とし込み層

最後に、上の factorization から

$$
[I]^p = 1
$$

型の class statement へ落とす補題を独立化する。
すると Stage 1a の核は、

$$
\text{factorization の幾何}
\to
\text{ideal equation}
\to
\text{class equation}
$$

という 3 段に薄まる。
これで初めて「本当に新しく書くべき定理」が theorem 名レベルで見えるようになる。

## 7. 実務的な次手

実務上は、いきなり大定理を書かずに、次の順がよい。

まず設計上の仮 target を 2〜3 本だけ追加する。
たとえば名前の方向としては、

* `CyclotomicIdealFactorizationTarget`
* `CyclotomicIdealProductIsPthPowerTarget`
* `CyclotomicClassPTorsionWitness_of_idealProductPthPower`

のように、Stage 1a の中身を **factorization / ideal product / class witness** の 3 層へ分けるのが良い。
そのうえで `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` を、それらの composition theorem に置き換える。
そうすれば、今の「最薄 kernel」をさらに 1 段薄くできる。

## 8. 最終提案

提案を一言でまとめると、こうじゃ。

$$
\boxed{
\text{Stage 1b の generic 化追撃はここで止め、Stage 1a を }
\text{Dedekind / factorization / class witness}
\text{ の 3 層へ裂く}
}
$$

これが最も筋が良い。
理由は、Stage 1b 側はもう「何が問題か」が分かったからじゃ。そこに長居しても infrastructure 整備へ流れてしまう。
対して Stage 1a は、まだ数学の芯そのものが残っておる。いま噛むべき本丸はそこじゃよ。
