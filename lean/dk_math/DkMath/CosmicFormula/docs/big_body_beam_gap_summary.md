# Big / Body / Beam / Core / Gap 構造まとめ

## 1. 基本定義

\[
W := (x+u)^d
\]

\[
\text{Core} := x^d
\]

\[
\text{Gap} := u^d
\]

\[
\text{Big} := W = (x+u)^d
\]

Big は次の三層構造として分解できる。

\[
\text{Big} = \text{Core} + \text{Beam} + \text{Gap}
\]

## 2. Beam（パスカル三角形の胴体）

Beam は純冪の両端を除いた中間項の総和として定義する。

\[
\text{Beam}_d(x,u) := (x+u)^d - x^d - u^d
\]

二項定理より

\[
(x+u)^d = \sum_{k=0}^{d} \binom{d}{k} x^k u^{d-k}
\]

したがって

\[
\text{Beam}_d(x,u) = \sum_{k=1}^{d-1} \binom{d}{k} x^k u^{d-k}
\]

これはパスカル三角形の外壁

\[
1,\;1
\]

を取り除いた **内部（Body）** に対応する。

## 3. Body（片側 Gap を除いた構造）

Body は Gap を取り除いた構造として定義する。

\[
\text{Body}_u^{(d)} := (x+u)^d - u^d
\]

よって

\[
\text{Body}_u^{(d)} = x^d + \text{Beam}_d(x,u)
\]

すなわち

\[
\text{Body} = \text{Core} + \text{Beam}
\]

## 4. d = 3 の具体形

展開すると

\[
(x+u)^3 = x^3 + 3x^2u + 3xu^2 + u^3
\]

したがって

\[
\text{Beam}_3(x,u) = 3x^2u + 3xu^2
\]

さらに因数分解すると

\[
\text{Beam}_3(x,u) = 3xu(x+u)
\]

また

\[
\text{Body}_u^{(3)} = x^3 + 3x^2u + 3xu^2
\]

## 5. Beam の意味（構造解釈）

Beam は

\[
(x+u)^d - (x^d + u^d)
\]

として定義され、純冪 \(x^d\) と \(u^d\) の **結合項** に対応する。

- Core : 左端の純冪
- Gap : 右端の純冪
- Beam : 両者を結ぶ中間結合構造

建築的比喩では

- Core, Gap = 柱
- Beam = 梁
- Big = 柱 + 梁 の全体構造

## 6. Body − Core の差

\[
\text{Body}^3 - x^3 = (x+u)^3 - (x^3 + u^3)
\]

よって

\[
\text{Body}^3 - x^3 = 3x^2u + 3xu^2
\]

すなわち Core を取り除くと **純粋な Beam 構造** が現れる。

## 7. d = 2 の場合

\[
(x+u)^2 = x^2 + 2xu + u^2
\]

\[
\text{Beam}_2(x,u) = 2xu
\]

\[
\text{Body}_u^{(2)} = x^2 + 2xu = x(x+2u)
\]

この場合は

\[
x(x+2u)
\]

が平方数になる解が存在する。

例：

\[
x=1,\;u=4
\]

\[
1(1+8) = 9 = 3^2
\]

## 8. d = 3 との対比

\[
\text{Body}_u^{(3)} = x^3 + 3x^2u + 3xu^2
\]

Beam が

\[
3xu(x+u)
\]

となり三重結合構造になる。

## 9. Pascal 構造としての解釈

\[
(x+u)^d
\]

は

\[
\text{Core} + \text{Beam} + \text{Gap}
\]

の三層分解を持つ。

Beam は

\[
\sum_{k=1}^{d-1} \binom{d}{k} x^k u^{d-k}
\]

であり、これは **Pascal's Triangle Body**（外壁を除いた内部）に対応する。
