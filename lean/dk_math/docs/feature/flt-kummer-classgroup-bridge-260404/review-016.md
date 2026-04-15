# FLT Kummer-classgroup bridge: review-016: Stage 2 の generic core が no-sorry で入った！次は pack-specialization へ直接刺す段へ

## 1. 状況分析

いまの景色は、かなり明瞭じゃ。
今回ので Stage 2 の **generic core**、すなわち

$$
(a) = (b)^n \;\Longrightarrow\; a = u,b^n \quad (\text{(u) は unit})
$$

に相当する一般補題群が no-sorry で入った。具体的には

* `principalGeneratorsUnitMulOfSpanEq`
* `unitMulPowOfSpanEqPowSpan`
* `unitMulPowOfSpanEqPowIdeal`
* `unitMulPowOfSpanEqPowPrincipal`

の 4 本じゃ。
ゆえに、「ideal-level の p 乗性から generator-level の \(u \cdot \beta^p\) 形へ戻す一般核」は、もう証明済みと見てよい。

しかも direct `sorry` は、引き続き

$$
\texttt{cyclotomicPrincipalization_of_classGroupPTorsionFree}
$$

の 1 本だけじゃ。
つまり、もはや class-group 側でも Stage 1 でもなく、残る honest open は

$$
\texttt{CyclotomicUnitNormalizationTarget}
\quad\text{と}\quad
\texttt{CyclotomicNormDescentTarget}
$$

の concrete 化に集中した、と見てよい。

## 2. 解説

これは証明の論理順で言えば、かなり本質的な前進じゃ。

いま既に手元にあるのは、

1. 局所因数分解
2. ideal の積の式
3. pairwise-coprime ideal arithmetic
4. 各因子が p 乗 ideal であること
5. class-group p-torsion witness
6. p-torsion annihilation
7. principal root ideal の抽出

までじゃ。
そこから次に必要なのは、ideal の statement

$$
(z-\zeta y) = (\beta)^p
$$

を元の statement

$$
z-\zeta y = u,\beta^p
$$

へ戻す段じゃ。
今回追加された generic core は、まさにこの橋のためのものじゃから、ここで道がかなり短くなったのぅ。

要するに、いま残っておるのは「Stage 2 を generic に証明すること」ではなく、**その generic core を Kummer の pack-specialized theorem に落とすだけ** の段へ縮んだのじゃ。
これが今回の数学的な面白さじゃよ。

## 3. 次の一手の推論

閉じる方向での最短経路なら、次ははっきりしておる。

$$
\boxed{
\texttt{CyclotomicUnitNormalizationTarget}
\text{ 自体を concrete 化する}
}
$$

これじゃ。
Stage 3 へ先に行くのは遠回りじゃ。理由は、norm descent の statement 自体が、Stage 2 で得る

$$
z-\zeta y = u,\beta^p
$$

型の element-level 正規化形に依存するからじゃ。
つまり Stage 2 が concrete にならぬと、Stage 3 もまだ honest に書けぬ。

## 4. 最短で刺すべき theorem

わっちなら、次に立てる theorem はほぼこれ一択じゃ。

### 4.1. 目標形

pack-specialized に

$$
\exists \beta,\ \exists u,\ \mathrm{IsUnit}(u)
\quad\text{such that}\quad
z-\zeta y = u,\beta^p
$$

を言う theorem を直接立てる。
つまり、`CyclotomicUnitNormalizationTarget` の中身を **その形そのもの** に置き換えるのじゃ。

generic core はもうあるので、ここでさらに abstraction を増やす必要はない。
閉じる最短経路なら、**target をそのまま concrete statement へ変える** のが最も速い。

### 4.2. 使う材料

この theorem を出すのに必要なのは、すでに揃っておる。

* Stage 1 で得た ideal p 乗性
* principal root ideal extraction
* `unitMulPowOfSpanEqPowPrincipal`

つまり論理的には

$$
(z-\zeta y) = K^p,\quad K \text{ principal}
$$

から

$$
z-\zeta y = u,(\mathrm{generator}(K))^p
$$

を出せばよい。
これは、いまの generic core をまっすぐ適用するだけでかなり近い。

## 5. 提案

最短手順としては、こうじゃ。

## 5.1. まず legacy one-shot は触らぬ

`cyclotomicPrincipalization_of_classGroupPTorsionFree` はいま legacy wrapper じゃ。
ここを直接埋めようとすると、Stage 2 と Stage 3 がまた混ざる。
いまは触らぬ方がよい。

## 5.2. `CyclotomicUnitNormalizationTarget` を concrete statement に置換

今の abstract target を、pack-specialized な存在命題へ変える。

たとえば意味としては、

$$
\forall \text{pack},\ \forall q,\ \exists \beta,\exists u,\
\mathrm{IsUnit}(u)\land
(z-\zeta y)=u,\beta^p
$$

のような形じゃ。
もちろん実際には ring と \(\zeta\) の文脈をもう少し丁寧に持たせる必要があるが、要は **unit と p 乗根候補の存在** をそのまま target にするのじゃ。

## 5.3. その target を、既存 generic core で埋める

ここでは新しい数学はほとんど要らぬ。
必要なのは、Stage 1 で作った principal ideal p 乗性と、principal generator をつなぐ specialization の整理だけじゃ。

## 5.4. その後に Stage 3 を切り出す

Stage 2 が concrete になったら、次は norm descent target を honest に書ける。
この時点で初めて

$$
z-\zeta y = u,\beta^p
$$

から norm を取って整数 witness を作る theorem を立てる。
ここで Stage 3 に入る。

## 6. 最終判断

結論を一言で言うぞい。

$$
\boxed{
\text{次の最短経路は、}
\texttt{CyclotomicUnitNormalizationTarget}
\text{ を pack-specialized な存在命題へ concrete 化し、}
\texttt{unitMulPowOfSpanEqPowPrincipal}
\text{ で埋めること}
}
$$

いまの generic core の証明は、まさにそのためにある。
ここを刺せば、残る honest open は本当に Stage 3 の norm descent だけになる。
つまり次に噛むべき本丸は、もうはっきり **Stage 2 の pack-specialization** じゃよ。
