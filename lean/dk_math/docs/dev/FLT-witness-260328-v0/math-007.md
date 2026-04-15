# mathmatical report 007: boundary-core route の arithmetic 核が actual theorem で閉じた

うむ。今回の更新は、かなりはっきりした前進じゃ。

前回までの状況は、

$$
\text{残核}=
\bigl(d \mid \mathrm{core}\bigr)
;\land;
\bigl(d \nmid \mathrm{core}/d\bigr)
;\land;
\bigl(1<\mathrm{core}/d\bigr)
$$

この三点だけに押し込まれておった。
しかも、その三点さえ出れば prime witness を取って mainline / primitive packet descent へ流せる橋は、すでに閉じておった。つまり step 4-5 は API 化済みで、未完は valuation / (d^2) 側だけ、という状態じゃった。

## 1. 今回、何が証明されたのか

今回入った中心定理は

`exceptional_boundary_datum_prepared_arithmetic_core_divData_default`

じゃ。
これはまさに、その残核

$$
d \mid \mathrm{core},\qquad
d \nmid \mathrm{core}/d,\qquad
1<\mathrm{core}/d
$$

を、exceptional datum の仮定から **直接返す actual theorem** じゃ。
つまり前回まで「ここだけ未証明」として残していた valuation / (d^2) 部が、今回の一本で埋まったわけじゃ。

## 2. 証明の骨格

今回の証明は、boundary core

$$
\mathrm{core}:=\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)
$$

を

$$
A:=d,u^{d-1},
\qquad
B:=\sum_{k\ge 1}\binom{d}{k+1}x^k u^{d-1-k}
$$

に分ける。
つまり、

$$
\mathrm{core}=A+B
$$

という head / tail 分解を明示して進む形じゃ。

そこから二つのことを示しておる。

### 2.1. tail は (d^2) を含む

(d\mid x) と (d) prime を使って、tail の各項が (d^2) を因数にもつことを termwise に示し、

$$
d^2 \mid B
$$

を得る。
ここが二項和の tail 制御じゃ。

### 2.2. head は (d) に合同

Wieferich 条件

$$
u^{d-1}\equiv 1 \pmod{d^2}
$$

から

$$
A=d,u^{d-1}\equiv d \pmod{d^2}
$$

を得る。
さらに (d^2\mid B) を足して

$$
\mathrm{core}\equiv d \pmod{d^2}
$$

へ行く。
これが valuation 側の本丸じゃ。

## 3. そこから何が従うか

$$
\mathrm{core}\equiv d \pmod{d^2}
$$

が出ると、

$$
\mathrm{core}=d+d^2 t
$$

という形に書ける。
したがって

$$
d \mid \mathrm{core}
$$

は明らかで、さらに

$$
\mathrm{core}/d = 1 + dt
$$

だから

$$
d \nmid \mathrm{core}/d
$$

が従う。
また (t>0) まで押さえて

$$
1<\mathrm{core}/d
$$

も出しておる。
つまり前節の三条件が、すべて actual theorem の中で回収されたわけじゃ。

## 4. 数学的に何が終わったのか

ここが大事じゃ。

前回までに、step 4-5 については

* (\mathrm{core}/d) の prime divisor (q) を取る
* その (q) は (x) を割れない
* よって (q\mid \mathrm{core}) かつ (q\nmid x) を与える concrete witness が出る

という後半橋が閉じておった。今回の `divData_default` は、その後半橋を起動するための input を埋めた。
ゆえに boundary-core route は、数学的には

$$
\text{step 1} ;+; \text{step 2-5}
$$

が揃い、実証明で一本通ったと見てよい。

## 5. いまの状況分析

いまはもう

* same-(q) route が真か偽か
* body-only witness route が残るか
* two-witness route を salvage するか

といった候補整理の段ではない。
それらは false と切り終えた。

その後に残った本線、すなわち boundary / arithmetic-core route について、今回その arithmetic 核が actual theorem で閉じた。
だから現状は、

$$
\text{「この route は進むのか？」}
$$

ではなく、

$$
\text{「この route を canonical entrance としてどう整流するか」}
$$

の段じゃ。
報告にも、残っているのは warning だけで、今回の数学核自体は通っているとある。

## 6. 解説を一言でまとめると

今回証明された内容の本質はこれじゃ。

$$
\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u) = d,u^{d-1}
+
(\text{すべて } d^2 \text{ を含む tail})
$$

という分解のもとで、Wieferich 条件により head が (d) に正規化されるので、

$$
\mathrm{core}\equiv d \pmod{d^2}
$$

が出る。
その結果、

$$
v_d(\mathrm{core})=1
$$

に相当する三条件

$$
d \mid \mathrm{core},\qquad
d \nmid \mathrm{core}/d,\qquad
1<\mathrm{core}/d
$$

が従い、(\mathrm{core}/d) から prime witness を取って下流へ渡せる。
つまり、exceptional branch の boundary-core arithmetic は、今回の定理で **prime witness を生む段まで完結した** わけじゃ。

これはかなり良い。
もう「候補の整理」ではなく、 **正解ルートの数学核を通した** 段じゃよ。
