# Body 正規化極限

## 1. 概要

宇宙式構造

$$
\mathrm{Big} = \mathrm{Core} + \mathrm{Beam} + \mathrm{Gap}
$$

において、微分は

- まず **Core を差分で除去** し
- 残った **Body** から共通の **Gap** を 1 枚はがし
- 最後に \( \mathrm{Gap} \to 0 \) の極限で **Beam 骨格** を露出する

操作として理解できる。

この操作を定式化したものを **Body 正規化極限** と呼ぶ。

---

## 2. 基本設定

自然数 \( d \ge 1 \)、実数 \( x \in \mathbb{R} \)、微小変位 \( u \in \mathbb{R} \setminus \{0\} \) を取る。

### 2.1. Big

$$
\mathrm{Big}(x,u;d) := (x+u)^d
$$

### 2.2. Core

$$
\mathrm{Core}(x;d) := x^d
$$

### 2.3. Body

$$
\mathrm{Body}(x,u;d)
:=
\mathrm{Big}(x,u;d)-\mathrm{Core}(x;d)=
(x+u)^d-x^d
$$

この Body は、Big から純粋な Core を抜いた残差である。

---

## 3. Body の基本構造

二項展開より

$$
(x+u)^d=
x^d+\sum_{k=1}^{d}\binom{d}{k}x^{d-k}u^k
$$

したがって

$$
\mathrm{Body}(x,u;d)=
\sum_{k=1}^{d}\binom{d}{k}x^{d-k}u^k
$$

である。

右辺の各項はすべて \(u\) を 1 個以上含む。  
よって Body は必ず \(u\) を共通因子にもつ。

$$
\mathrm{Body}(x,u;d)=u \cdot \Gamma_{d-1}(x,u)
$$

ただし

$$
\Gamma_{d-1}(x,u)
:=
\sum_{k=1}^{d}\binom{d}{k}x^{d-k}u^{k-1}
$$

である。添字をずらせば

$$
\Gamma_{d-1}(x,u)=
\sum_{j=0}^{d-1}\binom{d}{j+1}x^{d-1-j}u^j
$$

と書ける。

---

## 4. Body 正規化

Body に含まれる共通 Gap \(u\) を 1 枚はがす操作として、**Body 正規化** を次で定義する。

$$
\mathcal{N}_d(x,u)
:=
\frac{\mathrm{Body}(x,u;d)}{u}=
\frac{(x+u)^d-x^d}{u}
$$

したがって

$$
\mathcal{N}_d(x,u)=\Gamma_{d-1}(x,u)
$$

である。

これは

- Big から Core を引いて Body を作り
- Body の外側に付いている Gap を 1 つはがした

後の内部骨格を表している。

---

## 5. Body 正規化極限の定義

### 5.1. 定義

$$
\mathcal{B}_d(x)
:=
\lim_{u\to 0}\mathcal{N}_d(x,u)=
\lim_{u\to 0}\frac{(x+u)^d-x^d}{u}
$$

を **Body 正規化極限** と呼ぶ。

---

## 6. 基本定理

### 6.1. 定理

$$
\mathcal{B}_d(x)=dx^{d-1}
$$

### 6.2. 証明

$$
\mathcal{N}_d(x,u)=
\sum_{j=0}^{d-1}\binom{d}{j+1}x^{d-1-j}u^j
$$

であるから、\(u\to 0\) において \(j\ge 1\) の項はすべて消える。  
ゆえに \(j=0\) の項だけが残り、

$$
\mathcal{B}_d(x)=
\binom{d}{1}x^{d-1}=
dx^{d-1}
$$

を得る。

---

## 7. 宇宙式的解釈

Body 正規化極限は、通常の微分係数

$$
\frac{d}{dx}x^d
$$

に一致する。  
しかし宇宙式構造では、これは単なる微分ではなく、次の 3 段階の構造抽出になっている。

### 7.1. 第1段階. Core の除去

$$
\mathrm{Big}-\mathrm{Core}=
(x+u)^d-x^d=
\mathrm{Body}
$$

純粋な \(x^d\) 世界を抜き、混合側だけを残す。

### 7.2. 第2段階. Gap の正規化

$$
\frac{\mathrm{Body}}{u}=
\Gamma_{d-1}(x,u)
$$

Body に共通する最小 Gap \(u\) を 1 枚はがす。

### 7.3. 第3段階. 極限による骨格抽出

$$
\lim_{u\to 0}\Gamma_{d-1}(x,u)=dx^{d-1}
$$

余分な \(u\)-揺らぎを消し、内部骨格の先頭成分を露出する。

---

## 8. Beam との関係

宇宙式構造では Beam は混合項の集合である。  
Body は Core を除いた残差であり、そこにはすでに Beam 的構造が埋め込まれている。

正規化後の

$$
\Gamma_{d-1}(x,u)
$$

は、Gap を 1 個はがした後の **Beam 骨格列** と見なせる。

その極限

$$
dx^{d-1}
$$

は、この Beam 骨格の **最前線**、あるいは **先頭骨格** である。

したがって Body 正規化極限とは、

$$
\boxed{
\text{Body から Gap を正規化除去して抽出される Beam 骨格の極限核}
}
$$

である。

---

## 9. 低次の例

## 9.1. \(d=2\)

$$
\mathrm{Body}(x,u;2)=(x+u)^2-x^2=2xu+u^2
$$

したがって

$$
\mathcal{N}_2(x,u)=\frac{2xu+u^2}{u}=2x+u
$$

ゆえに

$$
\mathcal{B}_2(x)=\lim_{u\to 0}(2x+u)=2x
$$

---

## 9.2. \(d=3\)

$$
\mathrm{Body}(x,u;3)=(x+u)^3-x^3=3x^2u+3xu^2+u^3
$$

したがって

$$
\mathcal{N}_3(x,u)=3x^2+3xu+u^2
$$

ゆえに

$$
\mathcal{B}_3(x)=\lim_{u\to 0}(3x^2+3xu+u^2)=3x^2
$$

---

## 10. 定義の要点

Body 正規化極限の定義において、正規化に使うのは \(u\) である。  
これは Body のすべての項に共通する **最小一次因子** が \(u\) だからである。

一般に \(u^2\) 以上で割ると、

- 共通因子としては過剰であり
- 本来の一次骨格を壊し
- 微分的極限の自然性を失う

したがって標準形は

$$
\mathcal{B}_d(x)=
\lim_{u\to 0}\frac{(x+u)^d-x^d}{u}
$$

である。

---

## 11. まとめ

Body 正規化極限は、宇宙式構造における微分の本質を表す。

$$
\mathrm{Big}=(x+u)^d,\qquad
\mathrm{Core}=x^d,\qquad
\mathrm{Body}=(x+u)^d-x^d
$$

とすると、

$$
\mathrm{Body}=u\cdot\Gamma_{d-1}(x,u)
$$

であり、さらに

$$
\mathcal{B}_d(x)=
\lim_{u\to 0}\frac{\mathrm{Body}(x,u;d)}{u}=
dx^{d-1}
$$

となる。

したがって微分とは、

$$
\boxed{
\text{差分で Core を抜き、Gap を正規化除去し、Beam 骨格の極限核を得る操作}
}
$$

として解釈できる。

---

## 12. 短い定義文

**Body 正規化極限** とは、Big から Core を除いた Body を共通 Gap で正規化し、その Gap を 0 に近づけた極限である。  
数式では

$$
\mathcal{B}_d(x)
:=
\lim_{u\to 0}\frac{(x+u)^d-x^d}{u}=
dx^{d-1}
$$

で与えられる。  
これは Body の内部に潜む Beam 骨格の先頭成分を抽出する極限操作である。
