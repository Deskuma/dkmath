# 一般 \(d\) 次半宇宙式と円分的拡張

cid: 69bd3505-2580-83a7-9ec0-e1c4c6d58a0c

## 1. 概要

本メモは、2 次の半宇宙式

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

を出発点として、これを一般の \(d\) 乗へ拡張する枠組みを整理するものである。

2 次の場合には

- Body が 2 因子積 \(z(z+u)\) に落ちる
- Gap が \(\left(\frac{u}{2}\right)^2\) となる
- Big が中点平方 \(\left(z+\frac{u}{2}\right)^2\) となる
- 複素数 \(i\) による直交ノルム表示が成立する

という特別な美しさがある。

一方、一般の \(d\) に対しては、同じ 2 因子積のままでは閉じない。その代わり、

- 中点閉包型
- 差分核型
- 円分的分解型

という 3 つの顔を持つ一般化が得られる。

---

## 2. 2 次半宇宙式の再確認

原型宇宙式

\[
P(P+2u)+u^2=(P+u)^2
\]

に対し、\(P=2z\) とおくと

\[
(2z)(2z+2u)+u^2=(2z+u)^2
\]

である。両辺を \(4\) で割って

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

を得る。

これを **半宇宙式** と呼ぶ。

### 2.1. 構造対応

\[
\text{Body}=z(z+u),\qquad
\text{Gap}=\left(\frac{u}{2}\right)^2,\qquad
\text{Big}=\left(z+\frac{u}{2}\right)^2
\]

したがって

\[
\text{Body}+\text{Gap}=\text{Big}
\]

という宇宙式の基本骨格は保存される。

---

## 3. 中点座標による書き換え

\[
m:=z+\frac{u}{2},\qquad a:=\frac{u}{2}
\]

とおくと、2 次半宇宙式は

\[
(m-a)(m+a)+a^2=m^2
\]

となる。

これは

\[
m^2-a^2+a^2=m^2
\]

であり、差の平方の完全な実装になっている。

この形が一般 \(d\) 次への自然な入口となる。

---

## 4. 一般 \(d\) 次半宇宙式：中点閉包型

一般の \(d\in\mathbb{N}\) に対して、まず

\[
m^d-a^d
\]

を Body と見なす。

すると

\[
\left(m^d-a^d\right)+a^d=m^d
\]

は恒等的に成り立つ。

ここで \(m=z+\frac{u}{2}\), \(a=\frac{u}{2}\) を代入すると

\[
\boxed{
\left[\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d\right]
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
}
\]

を得る。

これを **一般 \(d\) 次半宇宙式（中点閉包型）** と呼ぶ。

### 4.1. 定義

\[
\boxed{
\mathrm{Body}_d^{(1/2)}(z,u)
:=
\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d
}
\]

と定めると

\[
\boxed{
\mathrm{Body}_d^{(1/2)}(z,u)
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
}
\]

である。

---

## 5. 2 次への還元

\(d=2\) のとき

\[
\mathrm{Body}_2^{(1/2)}(z,u)=
\left(z+\frac{u}{2}\right)^2-\left(\frac{u}{2}\right)^2
\]

であるから

\[
\mathrm{Body}_2^{(1/2)}(z,u)=z(z+u)
\]

となる。

ゆえに

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

が回収される。

したがって、2 次半宇宙式は一般式の特殊化に他ならない。

---

## 6. Body の展開形

二項定理により

\[
\left(z+\frac{u}{2}\right)^d=
\sum_{k=0}^{d}\binom{d}{k}z^k\left(\frac{u}{2}\right)^{d-k}
\]

であるから

\[
\mathrm{Body}_d^{(1/2)}(z,u)=
\sum_{k=1}^{d}\binom{d}{k}z^k\left(\frac{u}{2}\right)^{d-k}
\]

となる。

したがって \(z\) を因数として

\[
\mathrm{Body}_d^{(1/2)}(z,u)=
z\sum_{k=1}^{d}\binom{d}{k}z^{k-1}\left(\frac{u}{2}\right)^{d-k}
\]

と書ける。

また差の冪の因数分解より

\[
m^d-a^d=(m-a)\sum_{j=0}^{d-1}m^{\,d-1-j}a^j
\]

なので、\(m=z+\frac{u}{2}\), \(a=\frac{u}{2}\) を代入して

\[
\boxed{
\mathrm{Body}_d^{(1/2)}(z,u)=
z\sum_{j=0}^{d-1}
\left(z+\frac{u}{2}\right)^{d-1-j}
\left(\frac{u}{2}\right)^j
}
\]

を得る。

---

## 7. \(d=3\) の例

\(d=3\) では

\[
\mathrm{Body}_3^{(1/2)}(z,u)=
\left(z+\frac{u}{2}\right)^3-\left(\frac{u}{2}\right)^3
\]

であり、展開すると

\[
\mathrm{Body}_3^{(1/2)}(z,u)=
z^3+\frac{3}{2}uz^2+\frac{3}{4}u^2z
\]

となる。

したがって

\[
z\left(z^2+\frac{3}{2}uz+\frac{3}{4}u^2\right)
+
\left(\frac{u}{2}\right)^3=
\left(z+\frac{u}{2}\right)^3
\]

である。

ここでは Body はもはや 2 因子積ではなく、高次多項式になる。  
これが 2 次と一般 \(d\) 次の本質的差異である。

---

## 8. 差分核型との関係

一般宇宙式の重要な骨格は

\[
(x+u)^d-x^d=u\,G_{d-1}(x,u)
\]

である。ここで

\[
G_{d-1}(x,u)=
\sum_{j=0}^{d-1}(x+u)^{d-1-j}x^j
\]

とおく。

これを半スケールへ落とすと

\[
\left(z+\frac{u}{2}\right)^d-z^d=
\frac{u}{2}\,
G_{d-1}\!\left(z,\frac{u}{2}\right)
\]

を得る。

これを **半スケール差分核型** と呼ぶ。

### 8.1. 意味

中点閉包型

\[
\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
\]

は **中心・Gap・完成形** を観測する。

差分核型

\[
\left(z+\frac{u}{2}\right)^d-z^d=
\frac{u}{2}\,
G_{d-1}\!\left(z,\frac{u}{2}\right)
\]

は **成長・差分・Beam/GN** を観測する。

両者は役割が異なるが、どちらも一般 \(d\) 次宇宙式の半スケール表現として重要である。

---

## 9. 円分的分解型

一般 \(d\) では 2 次のような単純な直交ノルム表示は失われる。その代わり、円分的な根配置による分解が現れる。

\[
\zeta_d:=e^{2\pi i/d}
\]

を \(d\) 次の 1 の原始根とすると

\[
m^d-a^d=
\prod_{k=0}^{d-1}(m-\zeta_d^k a)
\]

である。

したがって \(m=z+\frac{u}{2}\), \(a=\frac{u}{2}\) を代入して

\[
\boxed{
\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d=
\prod_{k=0}^{d-1}
\left(
z+\frac{u}{2}-\zeta_d^k\frac{u}{2}
\right)
}
\]

を得る。

よって中点閉包型は

\[
\boxed{
\prod_{k=0}^{d-1}
\left(
z+\frac{u}{2}-\zeta_d^k\frac{u}{2}
\right)
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
}
\]

とも書ける。

これを **円分的半宇宙式** と呼ぶ。

---

## 10. 2 次では複素直交ノルムになる

\(d=2\) では

\[
\zeta_2=-1
\]

であるから

\[
m^2-a^2=(m-a)(m+a)
\]

となる。

さらに

\[
R^2+a^2=
(R+ai)(R-ai)=
|R+ai|^2
\]

が成り立つ。

したがって 2 次では

- 差の平方
- 直交ノルム
- 複素共役積

が一致する。

しかし一般 \(d>2\) では、これは複素平面上の単純なノルムではなく、**複数の根方向への円分的分解** に置き換わる。

この意味で、

\[
\boxed{
\text{2 次では直交ノルム、一般 \(d\) では円分配置}
}
\]

という対比が成立する。

---

## 11. 負の量の \(d\) 乗根による表示

\[
\omega_{d,k}:=e^{(2k+1)\pi i/d}
\qquad (k=0,\dots,d-1)
\]

とおくと、\(\omega_{d,k}^d=-1\) である。

したがって

\[
R^d+\left(\frac{u}{2}\right)^d=
\prod_{k=0}^{d-1}
\left(
R-\omega_{d,k}\frac{u}{2}
\right)
\]

が成立する。

これは 2 次での

\[
R^2+\left(\frac{u}{2}\right)^2=
\left(R+\frac{u}{2}i\right)\left(R-\frac{u}{2}i\right)
\]

の一般化である。

ただし、2 次のときのような「直交ノルムの 1 本化」は一般 \(d\) では失われ、代わりに **多方向根配置の積構造** が現れる。

---

## 12. 定義案

### 定義 12.1. 一般 \(d\) 次半宇宙式（中点閉包型）

\[
\mathrm{Body}_d^{(1/2)}(z,u)
:=
\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d
\]

とおき、

\[
\mathrm{Body}_d^{(1/2)}(z,u)
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
\]

を一般 \(d\) 次半宇宙式という。

### 定義 12.2. 半スケール差分核型

\[
\left(z+\frac{u}{2}\right)^d-z^d=
\frac{u}{2}\,
G_{d-1}\!\left(z,\frac{u}{2}\right)
\]

を半スケール差分核型という。

### 定義 12.3. 円分的半宇宙式

\[
\prod_{k=0}^{d-1}
\left(
z+\frac{u}{2}-\zeta_d^k\frac{u}{2}
\right)
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
\]

を円分的半宇宙式という。

---

## 13. 命題

### 命題 13.1

一般 \(d\) 次半宇宙式は恒等的に成り立つ。

#### 証明

\[
\left[\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d\right]
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
\]

は明らかである。 \(\square\)

### 命題 13.2

\(d=2\) のとき、一般 \(d\) 次半宇宙式は通常の半宇宙式に一致する。

#### 証明

\[
\left(z+\frac{u}{2}\right)^2-\left(\frac{u}{2}\right)^2=
z(z+u)
\]

であるから

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

を得る。 \(\square\)

### 命題 13.3

一般 \(d\) 次半宇宙式の Body は \(z\) を因子に持つ。

#### 証明

差の冪の因数分解

\[
m^d-a^d=(m-a)\sum_{j=0}^{d-1}m^{d-1-j}a^j
\]

に \(m=z+\frac{u}{2}\), \(a=\frac{u}{2}\) を代入すると \(m-a=z\) である。ゆえに Body は \(z\) を因子に持つ。 \(\square\)

---

## 14. 解釈上の要点

### 14.1. 2 次は特別である

2 次だけが

\[
\text{Body}=z(z+u)
\]

という 2 因子積に落ち、さらに複素直交ノルムに対応する。

### 14.2. 一般 \(d\) では Body は高次化する

一般 \(d\) では Body は

\[
\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d
\]

という高次多項式になり、2 因子積では表しきれない。

### 14.3. しかし骨格は不変である

それでも

\[
\text{Body}+\text{Gap}=\text{Big}
\]

という閉包構造そのものは変わらない。

### 14.4. 一般 \(d\) では円分構造が現れる

2 次の複素共役対の代わりに、一般 \(d\) では \(\zeta_d^k\) による複数方向の根配置が現れる。

---

## 15. 展望

### 15.1. GN 系との統合

差分核型

\[
\left(z+\frac{u}{2}\right)^d-z^d=
\frac{u}{2}\,G_{d-1}\!\left(z,\frac{u}{2}\right)
\]

は GN 系の半スケール版として自然であり、既存の一般宇宙式理論との統合が見込まれる。

### 15.2. 円分多項式との接続

円分的半宇宙式

\[
\prod_{k=0}^{d-1}
\left(
z+\frac{u}{2}-\zeta_d^k\frac{u}{2}
\right)
\]

は円分多項式、原始根、Zsigmondy 型議論との接点を持つ。

### 15.3. CFBRC・複素解析への橋

2 次で現れる直交ノルム像は、一般 \(d\) では円分的位相配置へ一般化され、複素解析的観測器としての拡張可能性がある。

---

## 16. まとめ

本メモの中心式は次の 3 つである。

### 16.1. 中点閉包型

\[
\boxed{
\left[\left(z+\frac{u}{2}\right)^d-\left(\frac{u}{2}\right)^d\right]
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
}
\]

### 16.2. 差分核型

\[
\boxed{
\left(z+\frac{u}{2}\right)^d-z^d=
\frac{u}{2}\,G_{d-1}\!\left(z,\frac{u}{2}\right)
}
\]

### 16.3. 円分的分解型

\[
\boxed{
\prod_{k=0}^{d-1}
\left(
z+\frac{u}{2}-\zeta_d^k\frac{u}{2}
\right)
+
\left(\frac{u}{2}\right)^d=
\left(z+\frac{u}{2}\right)^d
}
\]

したがって、一般 \(d\) 次においては、

- 2 次では直交ノルムとして見えていたものが
- 一般 \(d\) では円分配置と高次 Body 多項式へ姿を変え
- それでもなお Body + Gap = Big という閉包骨格を保つ

と結論できる。

ゆえに **一般 \(d\) 次半宇宙式は、2 次半宇宙式の単なる形式的拡張ではなく、円分的・差分核的・中点閉包的な三層構造を持つ一般化である**。
