# 複素半宇宙式と直交 Gap 表現

cid: 69bd3505-2580-83a7-9ec0-e1c4c6d58a0c

## 1. 概要

本メモは、半宇宙式

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

を、複素数のノルム

\[
a^2+b^2=(a+bi)(a-bi)=|a+bi|^2
\]

の観点から再解釈し、**Gap 項 \(\left(\frac{u}{2}\right)^2\) を虚軸方向の直交成分として表す一般化** を与えるものである。

この見方では、半宇宙式は単なる平方完成ではなく、

- 実数側では completed square
- 複素側では completed norm
- 宇宙式側では Body + Gap = Big

という三重対応を持つ。

---

## 2. 原型：半宇宙式

宇宙式

\[
P(P+2u)+u^2=(P+u)^2
\]

に対して、\(P=2z\) とおくと

\[
(2z)(2z+2u)+u^2=(2z+u)^2
\]

となる。両辺を \(4\) で割れば

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

という宇宙式の基本骨格は、そのまま保存される。

---

## 3. 複素直交化

複素数では

\[
i^2=-1
\]

であるから

\[
\left(\frac{u}{2}i\right)^2=-\left(\frac{u}{2}\right)^2
\]

である。

よって

\[
R^2+\left(\frac{u}{2}\right)^2 =
R^2-\left(\frac{u}{2}i\right)^2
\]

となり、差の平方公式

\[
a^2-b^2=(a+b)(a-b)
\]

より

\[
R^2+\left(\frac{u}{2}\right)^2 =
\left(R+\frac{u}{2}i\right)\left(R-\frac{u}{2}i\right)
\]

を得る。

さらにこれは複素ノルムの形

\[
R^2+\left(\frac{u}{2}\right)^2 =
\left|R+\frac{u}{2}i\right|^2
\]

とも書ける。

---

## 4. 複素半宇宙式

半宇宙式

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

において

\[
R^2:=z(z+u)
\]

とおくと、

\[
R^2+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

である。

したがって複素ノルム表示として

\[
\left|\,\sqrt{z(z+u)}+\frac{u}{2}i\,\right|^2 =
\left(z+\frac{u}{2}\right)^2
\]

を得る。

これを **複素半宇宙式** と呼ぶ。

### 4.1. 同値な積表示

同じ式は

\[
\left(\sqrt{z(z+u)}+\frac{u}{2}i\right)
\left(\sqrt{z(z+u)}-\frac{u}{2}i\right) =
\left(z+\frac{u}{2}\right)^2
\]

とも書ける。

---

## 5. 意味づけ

この式の意味は明確である。

### 5.1. 実数側

\[
z(z+u)+\left(\frac{u}{2}\right)^2
\]

は、隣接積 \(z(z+u)\) に半 Gap を補うことで平方へ閉じる completed square である。

### 5.2. 複素側

\[
\left|\,\sqrt{z(z+u)}+\frac{u}{2}i\,\right|^2
\]

は、Body を実軸方向、Gap を虚軸方向に置いた completed norm である。

### 5.3. 宇宙式側

\[
\text{Body}+\text{Gap}=\text{Big}
\]

の Gap は、「不足量」ではなく **直交方向へ立ち上がった構造単位** と読める。

---

## 6. \(u=1\) の基本例

\(u=1\) とすると

\[
z(z+1)+\frac14=\left(z+\frac12\right)^2
\]

である。

複素表示では

\[
\left|\sqrt{z(z+1)}+\frac12 i\right|^2 =
\left(z+\frac12\right)^2
\]

となる。

したがって \(\frac14\) は

- 平方完成の補正量
- 半単位 \(\frac12\) の二乗
- 虚軸方向の直交ノルム成分

の三つを同時に担う。

---

## 7. 円との接続

円

\[
x^2+y^2=R^2
\]

を考えると、

\[
x^2=R^2-y^2
\]

である。

一方、複素半宇宙式では

\[
R^2+\left(\frac{u}{2}\right)^2 =
\left|R+\frac{u}{2}i\right|^2
\]

であるから、\(R\) は実軸方向の長さ、\(\frac{u}{2}\) は虚軸方向の長さであり、両者は直交してノルム平方を作る。

したがって半宇宙式は、円の半径構造に対し **補正 Gap を直交方向へ持ち上げたノルム幾何** と見なせる。

---

## 8. 一般スケール版

さらに宇宙式

\[
P(P+2u)+u^2=(P+u)^2
\]

に対し \(P=sz\) とおくと

\[
z\left(z+\frac{2u}{s}\right)+\left(\frac{u}{s}\right)^2 =
\left(z+\frac{u}{s}\right)^2
\]

を得る。

これを **スケール宇宙式** と呼ぶ。

その複素版は

\[
\left|\sqrt{z\left(z+\frac{2u}{s}\right)}+\frac{u}{s}i\right|^2 =
\left(z+\frac{u}{s}\right)^2
\]

である。

### 8.1. 特別な場合

- \(s=1\)：原型宇宙式
- \(s=2\)：半宇宙式
- \(s=4\)：四分宇宙式

ここで Gap は

\[
\left(\frac{u}{s}\right)^2
\]

へ縮尺変換される。

---

## 9. 定義案

### 定義 9.1. 半宇宙式

任意の実数 \(z,u\) に対し

\[
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
\]

を半宇宙式という。

### 定義 9.2. 複素半宇宙式

半宇宙式を複素ノルムで書いた

\[
\left|\,\sqrt{z(z+u)}+\frac{u}{2}i\,\right|^2 =
\left(z+\frac{u}{2}\right)^2
\]

を複素半宇宙式という。

### 定義 9.3. 直交 Gap 表現

Gap 項を虚軸方向に持ち上げて

\[
R^2+\left(\frac{u}{2}\right)^2 =
\left|R+\frac{u}{2}i\right|^2
\]

と表す操作を直交 Gap 表現という。

---

## 10. 命題

### 命題 10.1

半宇宙式は completed square であると同時に completed norm である。

#### 証明

\[
z(z+u)+\left(\frac{u}{2}\right)^2 =
z^2+uz+\frac{u^2}{4} =
\left(z+\frac{u}{2}\right)^2
\]

である。

また \(R^2:=z(z+u)\) とおけば

\[
R^2+\left(\frac{u}{2}\right)^2 =
\left|R+\frac{u}{2}i\right|^2
\]

であるから completed norm でもある。 \(\square\)

### 命題 10.2

半宇宙式は宇宙式の \(P=2z\) による半スケール表示である。

#### 証明

\[
P(P+2u)+u^2=(P+u)^2
\]

に \(P=2z\) を代入して \(4\) で割ればよい。 \(\square\)

---

## 11. 解釈上の要点

### 11.1. \(\frac{u}{2}\) は不足量ではない

\[
\frac{u}{2}
\]

は単なる「足りない半分」ではなく、左右の状態 \(z\) と \(z+u\) の **中点補正** である。

### 11.2. Gap は虚軸方向へ持ち上がる

\[
\left(\frac{u}{2}\right)^2
\]

は、実軸上では補正平方、複素平面では虚軸成分のノルム平方である。

### 11.3. 宇宙式は completed norm として再読できる

この観点では

\[
\text{Body}+\text{Gap}=\text{Big}
\]

は、直交成分を含むノルム閉包の原理として読める。

---

## 12. 今後の展望

本構造から、次の方向が見える。

### 12.1. 高次元ノルム化

複素数に限らず

\[
R^2+\lambda_1^2+\cdots+\lambda_m^2 =
\|(R,\lambda_1,\dots,\lambda_m)\|^2
\]

とすることで、多次元 Gap 宇宙式へ拡張できる。

### 12.2. CFBRC・複素解析への接続

複素半宇宙式は、Gap の直交化という観点から CFBRC や偏角保存、ノルム保存型の設計と親和的である。

### 12.3. 実数宇宙式と複素宇宙式の橋

実数側では平方完成、複素側ではノルム完成であり、両者を統一する「複素宇宙式」概念の整備が期待される。

---

## 13. まとめ

本メモの中心式は次である。

\[
\boxed{
z(z+u)+\left(\frac{u}{2}\right)^2=\left(z+\frac{u}{2}\right)^2
}
\]

および、その複素ノルム版

\[
\boxed{
\left|\,\sqrt{z(z+u)}+\frac{u}{2}i\,\right|^2 =
\left(z+\frac{u}{2}\right)^2
}
\]

である。

これは

- 宇宙式の半スケール表示
- Gap の直交化
- completed square と completed norm の同一化

を一つの式に圧縮したものである。

ゆえに、**半宇宙式は複素平面上で直交 Gap を持つ completed norm 構造として一般化できる**。
