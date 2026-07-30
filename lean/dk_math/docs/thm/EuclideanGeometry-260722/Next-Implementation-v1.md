# Next Implementation

## 「中央橋」と「意味論橋」

## 今後は「中央橋」と「意味論橋」の二本立てになる

現在の状態を一行で書けば、こうじゃ。

$$
\text{Fermat form}\longrightarrow\varphi(n)=2^e\qquad\Box\qquad\text{constructible kernel}\longrightarrow\text{constructible orbit}
$$

中央の $\Box$ に入るのが Level C、

$$
\operatorname{IsGaussWantzelIndex}(n)\longrightarrow
\operatorname{QuadraticallyConstructibleUnitKernel}(\operatorname{regularKernel}(n))
$$

じゃ。

その後に別案件として、

$$
\text{QuadraticExpr による構成可能性}
\longleftrightarrow
\text{定規とコンパスによる幾何的作図可能性}
$$

を証明する。

したがって、今後は大きく二期に分かれる。

## 第一期：Level C ― Fermat form から one-step kernel を作る

今回の成果により、Gauss–Wantzel の前向き方向で本当に残ったものは、次の一点へ圧縮された。

> $2\pi/n$ 回転を表す一つの `regularKernel n` が、四則演算と平方根の有限式で表現できること。

全頂点を個別に構成する必要はない。

一つの kernel が構成可能なら、EUC-009 がすでに、

```text
one-step kernel
  → kernel powers
  → action on (1, 0)
  → every regular vertex
```

を証明しておる。

つまり Level C の主定理が通れば、直後に次が得られる。

```lean
theorem gaussWantzel_constructibleRegularOrbit
    {n : ℕ}
    (hn : IsGaussWantzelIndex n) :
    QuadraticallyConstructibleRegularOrbit n
```

## Level C-1：複素数との橋

まず `UnitKernel ℝ` と単位複素数を接続する。

CF2D の核、

$$
(x,y)
$$

を複素数、

$$
x+yi
$$

として読む写像じゃ。

Lean 上では概念的に、

```lean
def UnitKernel.toComplex (r : UnitKernel ℝ) : ℂ :=
  r.val.1 + r.val.2 * Complex.I
```

のようなものになる。

必要な性質は、

```text
star      → complex multiplication
one       → 1
conj      → complex conjugation
pow       → complex power
regularKernel n → exp(2πi/n)
```

じゃ。

ここで `regularKernel n` が primitive $n$ 乗根と一致することを固定する。

EUC-005 の exact order があるので、原始性を円分多項式側から再証明する必要はない。

$$
\operatorname{orderOf}(\operatorname{regularKernel}(n))=n
$$

を複素数側へ輸送すればよい。

## Level C-2：円分体の入口

次に primitive $n$ 乗根 $\zeta_n$ を含む体、

$$
\mathbb{Q}(\zeta_n)
$$

を扱う。

ここで必要なのは、単に「次数が二冪」というだけではない。

一般の代数的数について、

$$
[\mathbb{Q}(\alpha):\mathbb{Q}]=2^e
$$

だから $\alpha$ が平方根だけで構成できる、とは限らぬ。

円分体では拡大が Galois であり、その自己同型群の位数が、

$$
\varphi(n)
$$

になるという固有の構造を使う。

EUC-008 から、

$$
\varphi(n)=2^e
$$

が得られているため、円分体の Galois 群は有限 $2$ 群となる。

ここが中央橋の心臓じゃ。

## Level C-3：指数 $2$ の塔を取り出す

有限 $2$ 群には、位数を一段ずつ半分にする部分群列を構成できる。

概念的には、

$$
G=G_0\supset G_1\supset\cdots\supset G_e={1}
$$

かつ、

$$
[G_j:G_{j+1}]=2
$$

となる列じゃ。

Galois 対応によって、向きが逆転した中間体の塔、

$$
\mathbb{Q}=K_0\subset K_1\subset\cdots\subset K_e=\mathbb{Q}(\zeta_n)
$$

が得られ、各段階は、

$$
[K_{j+1}:K_j]=2
$$

となる。

これによって primitive root は有限回の二次拡大の中にある、と示せる。

ただし、この段階ではまだ `QuadraticExpr` へ入っていない。

得られるのは **体論的構成可能性** じゃ。

## Level C-4：二次拡大塔から `QuadraticExpr` へ

ここには専用 bridge が必要になる。

新しい中間 predicate を置くのがよい。

```lean
def LiesInQuadraticTower (x : ℝ) : Prop := ...
```

その上で二段階に分ける。

```text
IsGaussWantzelIndex n
  → regularKernel n の座標が quadratic tower に属する

quadratic tower に属する実数
  → QuadraticallyConstructibleScalar
```

後者では、各二次拡大の元が基礎体上、

$$
a+b\sqrt{d}
$$

の形に書けることを逐次使う。

ここで注意が必要なのは、円分体自体は複素体であることじゃ。

最終的に必要なのは、

$$
\cos\frac{2\pi}{n}
$$

と、

$$
\sin\frac{2\pi}{n}
$$

という二つの実座標なので、複素拡大塔から実部分へ降ろす必要がある。

## Level C-5：実座標への降下

one-step kernel は、

$$
\left(\cos\frac{2\pi}{n},\sin\frac{2\pi}{n}\right)
$$

である。

複素根 $\zeta_n$ から、

$$
\cos\frac{2\pi}{n}=\frac{\zeta_n+\zeta_n^{-1}}{2}
$$

が得られる。

また、

$$
\sin\frac{2\pi}{n}
$$

は、例えば、

$$
\sin^2\frac{2\pi}{n}=1-\cos^2\frac{2\pi}{n}
$$

から非負平方根として得られる。ただし $n$ の範囲や角度に応じて符号を管理する必要がある。

正 $n$ 角形を対象とする $3\leq n$ では、one-step angle は、

$$
0<\frac{2\pi}{n}<\pi
$$

なので $\sin(2\pi/n)>0$ を使える。

すると EUC-009 の閉包 APIへ、

```text
constructible cos
constructible 1 - cos²
nonnegative square root
```

を流し込める。

最終的に、

```lean
theorem gaussWantzel_constructibleRegularKernel
    {n : ℕ}
    (hn : IsGaussWantzelIndex n)
    (hpolygon : 3 ≤ n) :
    QuadraticallyConstructibleUnitKernel (regularKernel n)
```

へ到達する。

その直後は既存定理一つじゃ。

```lean
exact constructibleRegularOrbit_of_constructibleRegularKernel
  (gaussWantzel_constructibleRegularKernel hn hpolygon)
```

## Level C には二つの攻略路がある

### 抽象 Galois 路線

```text
totient is 2-power
  → cyclotomic Galois group is a 2-group
  → index-two subgroup tower
  → quadratic field tower
  → QuadraticExpr
```

長所は一般性が高く、Gauss–Wantzel の本質をそのまま形式化できること。

短所は Mathlib の円分体、Galois 対応、中間体次数、有限 $2$ 群 APIを広く扱う必要があることじゃ。

### Gaussian period 路線

Fermat prime ごとに Gaussian period を明示的に作り、平方根を反復して $\zeta_n$ の座標を構成する。

```text
Fermat prime structure
  → residue classes を二分
  → period sums
  → 二次方程式
  → nested square roots
```

こちらは `QuadraticExpr` へ直接落としやすい。

ただし、組合せ論・有限群・和の恒等式が大きくなりやすい。

## 推奨は抽象路線を先に進めること

現在の DkMath の設計には、抽象路線の方が合う。

理由は、今回すでに、

```text
orbit existence
exact order
Euclidean interpretation
constructibility closure
```

を全て抽象 API として分離したからじゃ。

Level C も、

```text
cyclotomic membership
quadratic tower
expression realization
```

と分層した方が、証明のどこに Gap があるか明確になる。

Gaussian period の明示式は、後に「実際の作図手順を取り出す」第二実装として追加できる。

## 第二期：幾何的作図との完全な同値

Level C が完成しても、まだ証明されるのは、

> `QuadraticExpr` で座標を生成できる。

という代数的作図可能性じゃ。

古典的な「無目盛り定規とコンパス」の操作との同値には、別の意味論が必要になる。

## 幾何側の primitive operations

まず作図操作を有限構文として定義する。

```lean
inductive StraightedgeCompassStep
  | givenPoint
  | lineThrough
  | circle
  | lineLineIntersection
  | lineCircleIntersection
  | circleCircleIntersection
```

そして、各手順が以前に構成した点だけを参照する有限作図列を定義する。

```lean
def GeometricallyConstructiblePoint (p : EuclideanSpace ℝ (Fin 2)) : Prop := ...
```

## 幾何作図から二次式へ

定規とコンパスの交点計算は、座標で書けば高々二次方程式を解くことになる。

```text
直線 × 直線
  → 四則演算

直線 × 円
  → 二次方程式
  → 平方根

円 × 円
  → 根軸と二次方程式
  → 平方根
```

したがって、

$$
\text{幾何的に構成可能}
\longrightarrow
\text{QuadraticallyConstructibleVec}
$$

を帰納法で証明できる。

## 二次式から幾何作図へ

逆方向では、`QuadraticExpr` の各 constructor に対応する古典作図を与える。

```text
rational
  → 単位線分と比例作図

add / sub
  → 平行移動・線分演算

mul / inv
  → 相似三角形

sqrt
  → 半円または平均比例
```

これにより、

$$
\text{QuadraticallyConstructibleVec}
\longrightarrow
\text{幾何的に構成可能}
$$

を式構文の帰納法で示す。

最終的に、

```lean
theorem quadraticallyConstructibleVec_iff_geometricallyConstructible
    (p : Vec ℝ) :
    QuadraticallyConstructibleVec p ↔
      GeometricallyConstructiblePoint p
```

が目標になる。

## 最後の Wantzel 側

完全同値には逆向きも必要じゃ。

$$
\text{正 }n\text{ 角形が作図可能}
\longrightarrow
\operatorname{IsGaussWantzelIndex}(n)
$$

これは次の流れになる。

```text
regular polygon constructible
  → primitive n-th root constructible
  → cyclotomic extension degree is a power of two
  → φ(n) is a power of two
  → prime-factor classification
  → Gauss–Wantzel Fermat form
```

EUC-008 では意図的に未証明とした、

$$
\varphi(n)=2^e\longrightarrow\operatorname{IsGaussWantzelIndex}(n)
$$

が、ここで必要になる。

奇素因数 $p$ について $p-1$ が二冪となり、

$$
p=2^{2^m}+1
$$

でなければならないこと、さらに奇素因数が重複しないことを証明する数論層じゃ。

したがって Wantzel 側は、

```text
constructibility necessity
totient necessity
Fermat-factor classification
```

の三段になる。

## 最終的な完成形

すべて閉じると、最終定理は概念的にこうなる。

```lean
theorem constructible_regularPolygon_iff_gaussWantzel
    {n : ℕ} (hn : 3 ≤ n) :
    GeometricallyConstructibleRegularPolygon n ↔
      IsGaussWantzelIndex n
```

その内部構造は、

```text
Gauss direction
  Fermat form
  → totient 2-power
  → cyclotomic quadratic tower
  → constructible one-step kernel
  → constructible regular orbit
  → geometric construction

Wantzel direction
  geometric construction
  → quadratic tower
  → cyclotomic degree 2-power
  → totient 2-power
  → Fermat form
```

となる。

## 次期案件の現実的な分割

いきなり完全同値を狙わず、次の順がよいじゃろう。

### Level C0：API 監査

Mathlib の、

```text
Cyclotomic
IsPrimitiveRoot
IntermediateField
IsGalois
finrank
subgroup towers
roots of unity
```

を調査し、利用可能な実在 API を固定する。

### Level C1：CF2D–cyclotomic bridge

`regularKernel n` と primitive complex $n$-th root の対応を証明する。

### Level C2：Quadratic tower predicate

`QuadraticExpr` と独立した体論的な二次拡大塔を定義する。

### Level C3：Gauss forward theorem

`IsGaussWantzelIndex n` から one-step kernel の tower constructibility を証明する。

### Level C4：tower から expression へ

体論的存在証明を `QuadraticExpr` の有限証人へ変換する。

### Level C5：constructible orbit theorem

既存 EUC-009 と結合して、Gauss 前向きを閉じる。

### Geometry G1〜G3

定規・コンパス構文、両方向の意味論、正多角形 predicate を実装する。

### Wantzel W1〜W3

構成可能性から次数、totient、Fermat form への逆向きを閉じる。

## 一番面白い点

今回の EUC-001〜010 によって、今後の難所はもう「正多角形全体」ではない。

難所は、一つの点に凝縮された。

$$
\left(\cos\frac{2\pi}{n},\sin\frac{2\pi}{n}\right)
$$

この **一歩分の核** を、平方根の有限反復で取り出せるか。

一歩さえ手に入れば、群作用が残りの頂点をすべて生成し、exact order が重複しないことを保証し、Euclidean bridge が正多角形として読み取ってくれる。

つまり次章は、

> **正多角形を作る話ではなく、最初の一歩を作る話**

になるのじゃ。🧙‍♀️✨️
