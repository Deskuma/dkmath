# canonical order

## D

次の課題の詳細をまとめたんだけど、

> ## 2. canonical order の検証
>
> canonical order は、順序を「差分の存在」で特徴づける性質じゃ。
>
> $$
> x\le y\ \leftrightarrow\ \exists z,\ y=x+z
> $$

これって宇宙式の $(x+u)^d$ の $x+u$ 成分だよねぇ。$u := z \to 0$
非負差分宇宙
差を取らなくても Big 内部の出来事として解釈するような事、できないのかな？

$y = x + z \iff Big = Body + Gap$

なわけだし。

ここで $x \le y$ だとしても引き算なく $x = y$ で $Big = Body + 0$

$x < y$ なら $Big + Body + Gap$

$Gap := z$

って、事ではないのかな？

## Codex

その解釈で合っています。

canonical order の本質は「差を計算すること」ではなく、

\[
x \le y \iff \exists z \ge 0,\quad y=x+z
\]

という **非負 Gap 宇宙の存在**です。

DkMath 的には、

```text
Core = x
Gap  = z
Big  = x + z = y
```

と読めます。したがって減算は定義に不要です。

- `x = y` なら `z = 0`
- `x < y` なら正の Gap 宇宙 `z`
- `x ≤ y` なら零を含む非負 Gap 宇宙 `z`

宇宙式へ冪を通せば、

\[
y^d=(x+z)^d
   =x^d+z\operatorname{gapGN}(d,x,z)
\]

となります。これは既存の subtraction-free theorem

```lean
pow_add_eq_pow_add_delta_mul_gapGN
```

そのものです。

ただし、`Big = Body + Gap` と `y = x + z` は層が異なります。

- `y = x + z`: 一次座標での Gap 充填
- `y^d = x^d + z * gapGN d x z`: 冪観測後の Body/Gap 分解

canonical order の難所は、`x ≤ y` からこの `z` を **DkNNRealQ 内部で構成すること**です。候補区間は資料どおり、

\[
Z_n=
\left[
\max(0,y_n^- - x_n^+),
\max(0,y_n^+ - x_n^-)
\right].
\]

これは減算を外部演算として導入するのではなく、Big 内部から安全な非負 Gap 区間を抽出する有限有理計算です。

したがって次の実装テーマは、

> canonical order = subtraction ではなく、非負 Gap 宇宙の抽出可能性

と置けます。`y = x + z ↔ Big = Body + Gap` という直感は正しく、Lean ではまず `diffNonnegApprox` の入れ子性・幅収束・`x + z ∼ y` に落とすのが具体的な実装経路です。

## 🐺賢狼

うむ。この解釈でかなり合っている。
そして「平方構造を辺にしてしまってよいか？」については、**順序・canonical order の文脈では、ほぼその理解でよい** じゃ。

ただし、注意点が一つある。
「辺」として扱うのは **一次元の Gap 充填方向** であって、ユークリッド幾何の対角線や斜辺ではない。ここを分ければ問題ない。

## 1. canonical order は「引き算」ではない

通常の数学では、

$$
x\le y\quad\Longleftrightarrow\quad \exists z,\ y=x+z
$$

を見ると、つい \(z=y-x\) と考える。

しかし DkMath 的には、これは引き算ではなく、

```text id="canonical-gap"
Body = x
Gap  = z
Big  = y
Big  = Body + Gap
```

という **非負 Gap 宇宙の存在定理** と読む方がよい。

つまり canonical order は、

$$
\boxed{x\le y\ \text{とは、}x\text{ から }y\text{ へ届く非負 Gap が存在すること}}
$$

じゃ。

これは subtraction-free にできる。
`DkNNRealQ` の内部で「差」を演算として入れる必要はない。有限有理区間のレベルで、Big の中から Gap 区間を抽出すればよい。

## 2. `x = y` と `x < y` の読み分け

あなたの整理は正しい。

```text id="eq-lt-gap"
x = y:
  Big = Body + 0

x < y:
  Big = Body + Gap
  Gap は非零の正 Gap 宇宙

x ≤ y:
  Big = Body + Gap
  Gap は 0 を含んでよい非負 Gap 宇宙
```

厳密には、`x < y` のときは quotient 上で \(z\neq0\) が欲しい。
さらに、今回 totality が有限分離で読めるので、`x < y` ならある段階で

$$
x.hi_n<y.lo_n
$$

が起きるはずじゃ。すると Gap の下端がその段階以降で正になる。
つまり strict order は「正 Gap が有限段階で観測された状態」と読める。

これはかなり美しい。

## 3. 平方構造を「辺」にすることについて

ここは大事じゃ。

`canonical order` の段階では、比較は一次元じゃ。

$$
y=x+z
$$

これは一本の線上で、

```text id="one-dimensional"
x から z だけ伸びて y に届く
```

という構造。

だから、ここで参照するのは斜辺ではない。
直交する二軸のノルムでもない。
単に同じ Big の中で、Body に Gap が足される。

したがって、

```text id="side-ok"
平方構造を辺として扱う
```

というのは、次の意味なら正しい。

```text id="side-meaning"
x + z という一次元の伸長を、
冪観測後の新しい辺・新しい値として見る
```

しかし、次の意味なら違う。

```text id="hypotenuse-not"
x と z を直交成分として、
斜辺 sqrt(x^2 + z^2) を見る
```

DkMath の canonical order では斜辺はいらない。
対角線ではなく、**Body から Big への同一直線上の Gap 充填** じゃ。

## 4. 冪を通すと GN が出る

一次元の Gap 充填

$$
y=x+z
$$

に冪観測を通すと、

$$
y^d=(x+z)^d
$$

となる。

ここで DkMath の既存核が出る。

$$
(x+z)^d=x^d+z,gapGN(d,x,z)
$$

つまり、

```text id="power-layer"
一次座標:
  Big = Body + Gap
  y = x + z

冪観測:
  Big^d = Body^d + Gap * GN
  y^d = x^d + z * gapGN d x z
```

ここで大事なのは、冪観測後の Gap は単なる \(z^d\) ではないことじゃ。
たとえば \(d=2\) なら、

$$
(x+z)^2=x^2+z(2x+z)
$$

となる。

だから「平方構造を辺にする」はよいが、「平方した Gap がただ \(z^2\) になる」と読んではいけない。
平方後の Gap は GN によって補正される。

## 5. 実装上は `diffNonnegApprox` が本丸

canonical order の難所は、

$$
x\le y
$$

から、

$$
\exists z,\ y=x+z
$$

の \(z\) を作ることじゃ。

ここで作る \(z\) は、DkNNRealQ の引き算ではない。
代表元の有限区間から抽出する **安全な非負 Gap 区間** じゃ。

候補は前に出したこれでよい。

$$
Z_n=\left[\max(0,y.lo_n-x.hi_n),\max(0,y.hi_n-x.lo_n)\right]
$$

DkMath 的に読むと、

```text id="gap-extract"
Z_n.lo:
  y が x の上端を確実に超えている部分

Z_n.hi:
  y が x の下端から見て届きうる最大 Gap

Z_n:
  Big 内部から抽出した安全な非負 Gap 観測
```

これは「引き算を導入した」のではない。
有限有理端点の差を使って、非負 Gap の観測区間を作っているだけじゃ。

## 6. この \(Z_n\) はかなり良い候補

この候補には、実装上の良い性質がある。

まず非負。

$$
0\le Z_n.lo
$$

かつ

$$
0\le Z_n.hi
$$

じゃ。`max 0` で切っているから当然。

次に入れ子性が期待できる。

```text id="z-nested"
y.lo は増える
x.hi は減る
したがって y.lo - x.hi は増える

y.hi は減る
x.lo は増える
したがって y.hi - x.lo は減る
```

ゆえに、`Z_n.lo` は単調増加、`Z_n.hi` は単調減少になりやすい。

さらに幅は、

$$
width(Z_n)\le width(X_n)+width(Y_n)
$$

で押さえられるはずじゃ。
両方の幅は 0 に収束するので、\(Z_n\) も DkReal になる。

## 7. `x + z ∼ y` はどう出るか

構成した \(Z\) について、最終的に必要なのは、

$$
x+z\sim y
$$

じゃ。
quotient ではこれが、

$$
x+z=y
$$

になる。

直感的には、\(Z_n\) は「\(y\) が \(x\) から見て取りうる Gap」を全部覆う区間なので、\(X_n+Z_n\) は \(Y_n\) を覆う、または少なくとも separation が 0 に潰れる。

ただし \(x\le y\) は asymptotic order なので、各段階で完全に overlap するとは限らない。
その場合でも、はみ出しは `orderDefect x y` と幅で押さえられる。

つまり証明の形は、

$$
separation(X_n+Z_n,Y_n)\le orderDefect(X,Y)_n
$$

または、

$$
separation(X_n+Z_n,Y_n)\le orderDefect(X,Y)_n+width(X_n)+width(Y_n)
$$

のような評価になるはずじゃ。

右辺は 0 に収束する。
だから `Equiv (x + z) y` が出る。

ここが canonical order の Lean 実装本丸じゃな。

## 8. DkMath 的な言い換え

この canonical order は、次のように書ける。

```text id="canonical-dkmath"
x ≤ y:
  x の Core が y の Big 内部に収まる

∃ z, y = x + z:
  y の Big から、x の Body を基準にした非負 Gap 宇宙 z を抽出できる

x = y:
  抽出される Gap は 0

x < y:
  抽出される Gap は非零、かつ有限段階で正に観測される
```

つまり、

$$
\boxed{\text{canonical order は、減算ではなく、Big 内部の非負 Gap 抽出可能性である。}}
$$

この方が DkMath らしい。

## 9. 「平方構造を辺にする」はどこで効くか

平方構造を辺にする発想は、canonical order の次に効く。

まず一次で、

$$
y=x+z
$$

を得る。

次に冪観測で、

$$
y^2=(x+z)^2
$$

を見る。

ここで、

$$
y^2=x^2+z(2x+z)
$$

となる。

これは、`x` から `y` への一次 Gap \(z\) が、平方観測では

$$
z(2x+z)
$$

という補正 Gap に変わる、ということじゃ。

だから平方構造を「辺」として見るなら、

```text id="square-side"
一次辺:
  y = x + z

平方辺:
  y^2 = x^2 + z(2x+z)
```

であり、斜辺ではない。
同一直線上の観測レベルが変わっただけじゃ。

## 10. 実装テーマ名としてはこれが良い

次の実装テーマは、こう名付けると分かりやすい。

```text id="theme-name"
canonical order = nonnegative Gap extraction
```

Lean ファイルとしては、既存 `Order.lean` が膨らみすぎるなら分けてもよい。

```lean id="possible-file"
DkMath.Analysis.DkReal.CanonicalOrder
```

または、

```lean id="possible-file-gap"
DkMath.Analysis.DkReal.GapExtract
```

補題名はこう。

```lean id="lemma-plan"
def diffNonnegApprox
theorem diffNonnegApprox_nested
theorem diffNonnegApprox_width_tends_zero
def gapOfLe
theorem add_gapOfLe_equiv
theorem exists_add_of_le
theorem le_iff_exists_add
```

ただし「diff」という名前は引き算に見えるので、DkMath 的には、

```lean id="better-name"
gapApproxOfLe
gapOfLe
add_gapOfLe_equiv
```

の方がよいかもしれぬ。

## 11. 結論

あなたの直感は合っている。

```text id="conclusion"
canonical order は subtraction ではない
非負 Gap 宇宙の存在である
Big = Body + Gap と読める
x = y なら Gap = 0
x < y なら正 Gap が有限段階で観測される
平方構造は斜辺ではなく、同一直線上の冪観測として扱えばよい
```

最も大事な一文はこれじゃ。

$$
\boxed{x\le y\ \text{とは、}y\text{ という Big の内部から }x\text{ を Body とする非負 Gap を抽出できることである。}}
$$

この解釈なら、DkMath の宇宙式スタイルと canonical order がかなり綺麗につながる。
