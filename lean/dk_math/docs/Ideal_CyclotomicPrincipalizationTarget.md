# Cyclotomic Principalization Target におけるイデアル部分のまとめ

## 1. 目的

本稿は、`CyclotomicPrincipalizationTarget` のうち、特に Stage 1 に属する「局所因数分解からイデアル演算へ至る部分」を整理してまとめるものである。

ここで扱う主題は、円分的な線型因子
\[
z - \alpha y
\]
および
\[
z - \beta y
\]
に対応する principal ideals が、どのように差冪
\[
z^p - y^p
\]
の構造と結びつき、さらに互いに素性・交叉・積の関係へ進むか、という点にある。

狙いは、Kummer 的 principalization の Stage 1 を、単なる元の因数分解ではなく、ideal arithmetic の concrete core として固定することである。

---

## 2. 背景

Kummer 的 principalization は、大きく次の 3 段に分かれる。

### 2.1. Stage 1. ideal の \(p\) 乗性

円分環上で、線型因子 ideal の積が \(p\) 乗 ideal に一致することを示す段階である。

### 2.2. Stage 2. 単数の調整

Kummer 単数や cyclotomic unit を吸収し、principalization に必要な単数補正を行う段階である。

### 2.3. Stage 3. norm を通じた整数 descent existence への帰還

円分環で得た ideal-level の構造を、整数 world へ戻す橋を与える段階である。

本稿で扱うのは、このうち Stage 1 に属するイデアル部分である。

---

## 3. 局所文脈

最小の局所文脈として、可換環 \(R\) 上で
\[
\zeta^p = 1
\]
を満たす元 \(\zeta \in R\) を固定する。

このとき、`CyclotomicLocalFactorizationContext` は、将来の一般化に耐えるために、あえて最小限の条件だけを保持するよう設計されている。すなわち、現段階では primality、class group、unit group の詳細までは仮定せず、局所因数分解の核だけを抽出している。

---

## 4. 局所因数分解

まず、幾何級数型の和
\[
\sum_{i=0}^{p-1} x^i (\zeta y)^{p-1-i}
\]
を考えると、これに対して次が成り立つ。
\[
\left(\sum_{i=0}^{p-1} x^i (\zeta y)^{p-1-i}\right)(x - \zeta y) = x^p - y^p
\]

これは `geom_sum₂_mul` による標準的な差冪因数分解であるが、本実装ではこれを DkMath-native な局所 kernel として固定している。

この和は、通常の
\[
(x+u)^d - u^d = x \, GN_d(x,u)
\]
における quotient kernel に対応する、円分 twist 版の GN と見なすことができる。

---

## 5. FLT 方程式への specialization

さらに
\[
x^p + y^p = z^p
\]
の状況を仮定すると、上の局所因数分解は
\[
\left(\sum_{i=0}^{p-1} z^i (\zeta y)^{p-1-i}\right)(z - \zeta y) = x^p
\]
へ specialize される。

これは、線型因子
\[
z - \zeta y
\]
が単に \(z^p - y^p\) を割るだけでなく、FLT 反例方程式のもとで
\[
x^p
\]
を生成する局所因子として現れることを意味する。

---

## 6. principal ideal への持ち上げ

元の等式をそのまま `Ideal.span` に持ち上げることで、principal ideals の積等式
\[
\operatorname{span}(\text{kernel}) \cdot \operatorname{span}(z - \zeta y) = \operatorname{span}(x^p)
\]
が得られる。

さらに `Ideal.span_singleton_pow` を用いて
\[
\operatorname{span}(x^p) = \operatorname{span}(x)^p
\]
と書き換えることで、
\[
\operatorname{span}(\text{kernel}) \cdot \operatorname{span}(z - \zeta y) = \operatorname{span}(x)^p
\]
を得る。

これは、Kummer 第一場合において必要となる
「線型因子 ideal の積が \(p\) 乗 ideal に一致する」
という concrete ideal identity の最小核である。

---

## 7. 線型因子 ideals の comaximal 性

次に、2 つの線型因子
\[
z - \alpha y,\qquad z - \beta y
\]
を考える。

それらの差は
\[
(z - \alpha y) - (z - \beta y) = \beta y - \alpha y
\]
であるから、もし
\[
\beta y - \alpha y
\]
が unit なら、対応する principal ideals は comaximal になる。

すなわち、
\[
\operatorname{span}(z - \alpha y) \,\vee\, \operatorname{span}(z - \beta y) = \top
\]
が成立する。

これは Kummer 的には、異なる線型因子 ideal が pairwise coprime になるための最小 concrete 補題である。

---

## 8. generator レベルと ideal レベルでの互いに素性

上記の comaximal 性から、元そのものについても
\[
\operatorname{IsCoprime}(z - \alpha y,\; z - \beta y)
\]
が従う。

さらに ideals 自体についても
\[
\operatorname{IsCoprime}\bigl(\operatorname{span}(z - \alpha y),\; \operatorname{span}(z - \beta y)\bigr)
\]
が成り立つ。

この 2 つは、後で pairwise-coprime family を扱うときに重要になる。すなわち、

- 元レベルの互いに素性
- ideal レベルの互いに素性
- `sup = top`

が互いに整合する形で整理されている。

---

## 9. 交叉と積の一致

さらに、互いに素な ideals に対しては
\[
I \cap J = IJ
\]
が成り立つ。

本件では具体的に
\[
\operatorname{span}(z - \alpha y) \cap \operatorname{span}(z - \beta y) = \operatorname{span}(z - \alpha y)\operatorname{span}(z - \beta y)
\]
を得た。

これは Dedekind ideal arithmetic に入る前の最小 concrete 補題として自然であり、pairwise-coprime な線型因子 ideals の交叉が、そのまま積で表されることを意味する。

---

## 10. 数学的到達点

ここまでで得られた内容は、次の 4 段で整理できる。

### 10.1. 局所因数分解

\[
\mathrm{kernel}(x,y,\zeta)\,(x-\zeta y)=x^p-y^p
\]

### 10.2. FLT 方程式への specialization

\[
\mathrm{kernel}(z,y,\zeta)\,(z-\zeta y)=x^p
\]

### 10.3. principal ideal identity

\[
(\mathrm{kernel})\,(z-\zeta y)=(x)^p
\]

### 10.4. 異なる線型因子 ideals の pairwise-coprime 性

\[
I_\alpha \vee I_\beta=\top
\]
および
\[
I_\alpha \cap I_\beta = I_\alpha I_\beta
\]

この意味で、Stage 1 はすでに単なる元の因数分解ではなく、pairwise-coprime ideal family の arithmetic に入っている。

---

## 11. GN との関係

通常の GN は
\[
(x+u)^d - u^d = x \, GN_d(x,u)
\]
という差冪 kernel として現れる。

今回の幾何級数型和
\[
\sum_{i=0}^{p-1} z^i (\zeta y)^{p-1-i}
\]
も、本質的には
\[
\frac{z^p-y^p}{z-\zeta y}
\]
を表す quotient kernel であり、通常の GN の円分 twist 版とみなせる。

したがって、今回のイデアル部分の成果は、

「GN 的 kernel が element-level から ideal-level に昇格した」

と理解できる。

これは DkMath の宇宙式・GN 系の研究の流れにおいて、非常に自然な拡張である。

---

## 12. 今後の展望

ここから先は、主に次の 3 方向が見えている。

### 12.1. finite family 版への拡張

2 個の ideals について得られた
\[
I \cap J = IJ
\]
を、有限族
\[
\{I_j\}_{j \in S}
\]
に対して
\[
\bigcap_{j \in S} I_j = \prod_{j \in S} I_j
\]
へ拡張する。

### 12.2. \(\alpha = \zeta^i\)、\(\beta = \zeta^j\) への specialization

本命の円分因子族に対して
\[
\beta y - \alpha y = y(\zeta^j - \zeta^i)
\]
の unit 性をどう処理するかが、Stage 2 の単数調整に直結する。

### 12.3. norm を通じた descent existence への接続

Stage 1 で得た pairwise-coprime ideal family の情報を用いて、各因子の \(p\) 乗性や principalization を individual に読み、最終的に整数 descent existence へ戻す。

---

## 13. 総括

今回固定されたイデアル部分は、

- 局所因数分解
- principal ideal identity
- pairwise-comaximality
- `inf = mul`

までを連続的に押さえたものである。

ひとことで言えば、

「線型因子が差冪を割る」
という元の事実を、
「線型因子 ideals が互いに素に分離し、その交叉が積になる」
という ideal arithmetic の concrete core へ持ち上げた部分

である。

これにより、Kummer 的 principalization の Stage 1 は、局所 kernel の実装段階から、pairwise-coprime ideal family の構造段階へ進んだと評価できる。
