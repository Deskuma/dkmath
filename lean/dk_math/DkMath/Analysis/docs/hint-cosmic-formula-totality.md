# Hint: Cosmic Formula Totality Implements Design

## Hint

ふむ。大小比較か。
DkMath っぽく宇宙式スタイルで、この totality は記述したい部分だな。

２つの宇宙式を１つにして、その Core $\le$ Gap の比較だろうな。
単一の宇宙式でも Core = $x^2$ と Gap = $u^2$ が同じとなる時、$x = u$ となる。

２つの宇宙式を結合する。
それを取り囲む Big が生まれる。その内部構造の Core $\le$ Gap を見る。

直感的にはこれで上手く行きそうだが。

一般化すると単位 Gap の底の変換を伴う。または、そのまま合算して両方デカくする。減算の必要が無くなる。
それで、２つの宇宙を伸縮して、まず Gap を合わせる。
その Gap を重ねて２つの宇宙を合わせる。
そこから Gap → 0 で Core を 2つ にする。
片方を Gap に読み替える。
で、比較する。 $x \le u$

この操作を $\R$ に頼らずに行う。

## 検証

うむ。その方向はかなり **DkMath らしい totality の記述** になり得る。
いまの `orderDefect` は、すでにその原型になっておる。

要点を先に言うと、totality は DkMath 風にはこう書ける。

$$
\boxed{\text{二つの宇宙を同じ Big の中へ入れ、Gap を潰したとき、Core の向きが必ず片側へ閉じる。}}
$$

Lean 的には、

```lean id="totality-target"
theorem le_total (x y : DkNNRealQ) :
    x ≤ y ∨ y ≤ x
```

だが、DkMath 的にはこれは「大小比較」ではなく、**二宇宙合成後の Core-Gap 配置の向き決定** と見た方が合う。

## 1. 二つの宇宙式を一つの Big に入れる

今の `DkReal` では、各値は入れ子区間列として表されている。

$$
X_n=[x_n^-,x_n^+]
$$

$$
Y_n=[y_n^-,y_n^+]
$$

ここで \(x_n^-\) は lower endpoint、\(x_n^+\) は upper endpoint じゃ。

二つを一つにまとめる Big は、たとえば各段で

$$
Big_n(X,Y)=[\min(x_n^-,y_n^-),\max(x_n^+,y_n^+)]
$$

のように見られる。

この Big の内部で、二つの宇宙の Core がどちら側にあるかを見る。
ただし、まだ Gap があるので、いきなり点比較はできない。

## 2. Core 差と Gap 幅

二つの宇宙の比較 Core を、現在の実装に合わせるなら、

$$
Core_{X,Y}(n)=x_n^- - y_n^-
$$

と置ける。

そして、比較の不確定幅を

$$
Gap_{X,Y}(n)=width(X_n)+width(Y_n)
$$

と見る。

ここで、`DkReal` の定義から両方の width は 0 に収束するので、

$$
Gap_{X,Y}(n)\to0
$$

じゃ。

つまり、二つの宇宙を Big に入れたとき、内部の比較 Gap は精度を上げるほど潰れていく。

## 3. 現在の orderDefect は「正の Core 超過」

今の順序定義は、

$$
orderDefect(X,Y)(n)=\max(0,x_n^- - y_n^-)
$$

じゃった。

これは DkMath 的には、

```text id="defect-meaning"
X の Core が Y の Core を正方向に超えてしまう量
```

を見るものじゃ。

そして、

$$
X\le Y
$$

とは、

$$
\max(0,x_n^- - y_n^-)\to0
$$

という意味。

つまり、

```text id="le-meaning"
X の Core が Y の Core より右へ出る量が、
Gap → 0 の中で消える
```

ということじゃ。

これはまさに、あなたの言う **Core ≤ Gap を見る** という発想に近い。

## 4. totality を宇宙式スタイルで書くなら

二つの宇宙を合成したとき、比較 Core は符号を持つ。

$$
C_n=x_n^- - y_n^-
$$

この \(C_n\) について、

```text id="orientation"
C_n の正の部分が消えるなら X ≤ Y
C_n の負の部分が消えるなら Y ≤ X
```

となる。

正の部分は、

$$
C_n^+=\max(0,C_n)
$$

負の部分は、向きを反転して、

$$
C_n^-=\max(0,-C_n)=\max(0,y_n^- - x_n^-)
$$

と見ればよい。

したがって totality は DkMath 風には、

$$
\boxed{C^+ \to 0\ \text{または}\ C^- \to 0}
$$

と書ける。

これは通常の大小比較

$$
X\le Y\ \text{または}\ Y\le X
$$

を、Core の向きの崩壊として書いたものじゃ。

## 5. Gap を合わせる、という直感

あなたの言う、

```text id="gap-align"
どちらかを伸縮して Gap を合わせる
Gap を重ねて 2 つの宇宙を合わせる
Gap → 0 で Core 2 つにする
```

は、実装上はかなり自然に

$$
Gap_{X,Y}(n)=width(X_n)+width(Y_n)
$$

へ落とせる。

二つの表現はそれぞれ独自の幅を持つ。
しかし比較時には、共通の不確定性として足し合わせればよい。

$$
x_n^- - y_n^-
$$

がこの共通 Gap の範囲内なら、まだ同じ位置に潰れる可能性がある。
逆に、Gap を超えて片側へ出続けるなら、向きが決まる。

## 6. 三状態比較として見るとよい

DkMath 的には、totality をいきなり二択にせず、まず三状態で書くと美しい。

```text id="three-state"
Left:
  X は Y より左に閉じる

Right:
  Y は X より左に閉じる

Merge:
  X と Y は同じ Core へ潰れる
```

Lean 風には、たとえば概念としてはこう。

```lean id="comparison-concept"
inductive CoreComparison (x y : DkReal) : Prop where
  | left  : DkReal.Le x y → CoreComparison x y
  | right : DkReal.Le y x → CoreComparison x y
  | merge : DkReal.Equiv x y → CoreComparison x y
```

ただし `merge` は実際には `left` と `right` の両方を含む。
なぜなら `Equiv x y` なら、すでに `equiv_le` により

$$
x\le y
$$

かつ

$$
y\le x
$$

が出るからじゃ。

なので、totality は最終的には二択でよいが、DkMath の説明では三状態の方が直感的じゃ。

## 7. 「片方を Gap に入れ替える」の対応

あなたの言う、

```text id="gap-swap"
片方を Gap に入れ替える。で、比較する。 x ≤ u
```

これは、現在の `orderDefect` の形でかなり表現できる。

比較対象 \(Y\) を基準 Gap 側に置き、\(X\) の Core がそこからどれだけ正方向へ飛び出すかを見る。

$$
defect(X,Y)=\max(0,Core_X-Core_Y)
$$

この defect が 0 に潰れるなら、\(X\) は \(Y\) を超えていない。
つまり \(X\le Y\)。

この意味で、`orderDefect` は「片方を基準 Gap にして、もう片方の Core 超過を見る」核になっている。

## 8. ただし totality には追加原理が要る

ここが大事じゃ。

現在の実装では、

```text id="already-proved"
Le は反射的
Le は推移的
互いに Le なら Equiv
Equiv と両立
```

までは閉じている。

しかし totality は、

$$
C^+\to0\ \text{または}\ C^-\to0
$$

のどちらかを **必ず選べる** という主張じゃ。

これは、実数的には当然だが、内部の区間列だけで証明するには一段重い。

なぜなら、二つの Core 差

$$
C_n=x_n^- - y_n^-
$$

が 0 に近づくのか、正側に残るのか、負側に残るのかを判定するには、実質的に「極限値の符号」を見る必要があるからじゃ。

これを \(\mathbb{R}\) に頼らずやるなら、DkMath 側に次のような **比較原理** を立てるのがよい。

## 9. DkMath 版 totality 原理

提案する名前は、たとえばこれじゃ。

```lean id="cosmic-totality-name"
CosmicComparisonTotal
```

または、

```lean id="big-gap-totality-name"
BigGapTotality
```

内容は概念的にはこう。

```text id="big-gap-totality"
二つの収縮宇宙 X, Y を同じ Big に埋める。
共通 Gap が 0 に潰れるとき、
Core 差は正側に潰れるか、負側に潰れるか、同一 Core に潰れる。
```

Lean で最初に置くなら、いきなり theorem ではなく predicate として置くのが安全じゃ。

```lean id="located-prop"
def LocatedPair (x y : DkReal) : Prop :=
  DkReal.Le x y ∨ DkReal.Le y x
```

ただしこれだと totality そのものなので、もう少し構造的にするなら、

```lean id="core-gap-located"
def CoreGapLocated (x y : DkReal) : Prop :=
  Filter.Tendsto
      (fun n => max 0 ((x.interval n).lo - (y.interval n).lo))
      Filter.atTop (nhds 0)
  ∨
  Filter.Tendsto
      (fun n => max 0 ((y.interval n).lo - (x.interval n).lo))
      Filter.atTop (nhds 0)
```

これは現行 `Le` を展開しただけじゃが、DkMath 的な意味は明確じゃ。

## 10. もっと宇宙式らしい三分岐

さらに宇宙式らしくするなら、

```text id="core-gap-trichotomy"
SeparatedLeft:
  X の右端が Y の左端より左へ閉じる

SeparatedRight:
  Y の右端が X の左端より左へ閉じる

Merged:
  separation(X,Y) → 0
```

という三分岐にする。

概念的には、

```lean id="trichotomy-concept"
def BigGapTrichotomy (x y : DkReal) : Prop :=
  DkReal.Le x y ∨ DkReal.Le y x ∨ DkReal.Equiv x y
```

ただし `Equiv` は両方向の `Le` を含むので、定理としては冗長。
しかし説明としては綺麗じゃ。

DkMath 的には、

```text id="trichotomy-meaning"
左へ閉じる
右へ閉じる
重なって同じ Core へ閉じる
```

の三状態で語るとよい。

## 11. 実装ルート案

\(\mathbb{R}\) に頼らず進めたいなら、まずは theorem ではなく、比較原理を API として分離するのが安全じゃ。

第一段階。

```lean id="pair-defs"
def coreDiff (x y : DkReal) (n : ℕ) : ℚ :=
  (x.interval n).lo - (y.interval n).lo

def pairGap (x y : DkReal) (n : ℕ) : ℚ :=
  (x.interval n).width + (y.interval n).width
```

第二段階。

```lean id="core-gap-defect"
def corePositiveDefect (x y : DkReal) (n : ℕ) : ℚ :=
  max 0 (coreDiff x y n)
```

これは現行 `orderDefect` と同じ。

第三段階。

```lean id="biggap-located"
def BigGapLocated (x y : DkReal) : Prop :=
  DkReal.Le x y ∨ DkReal.Le y x
```

第四段階。

```lean id="biggap-totality"
class HasBigGapTotality where
  le_total : ∀ x y : DkNNRealQ, x ≤ y ∨ y ≤ x
```

ここまでなら、\(\mathbb{R}\) に頼らずに「DkMath 的 totality の入口」を定義できる。
証明はまだ別問題として残せる。

## 12. 現時点で言えること

あなたの直感を現在の実装に翻訳すると、こうじゃ。

```text id="translation"
二つの宇宙式を結合する:
  DkReal pair X Y

それを取り囲む Big:
  共通比較空間 Big_n = hull(X_n, Y_n)

Gap を合わせる:
  pairGap_n = width(X_n) + width(Y_n)

Core を比較する:
  coreDiff_n = lo(X_n) - lo(Y_n)

Core ≤ Gap を見る:
  orderDefect(X,Y)_n = max 0 coreDiff_n

Gap → 0:
  DkReal の width_tends_zero

totality:
  coreDiff の正側または負側が必ず消える
```

この対応はかなり綺麗じゃ。

## 13. 結論

うむ。
この totality は、DkMath では単なる

$$
x\le y\ \text{or}\ y\le x
$$

ではなく、

$$
\boxed{\text{二つの宇宙を Big に合成し、Gap を 0 に潰したとき、Core の向きが片側へ閉じる}}
$$

として書くのがよい。

実装上は、今の `orderDefect` を核にして、

```text id="next-totality-api"
coreDiff
pairGap
BigGapLocated
BigGapTotality
```

のような補助概念を足すと、DkMath らしい説明と Lean の `le_total` が綺麗に接続できるはずじゃ。

ただし、\(\mathbb{R}\) に頼らず全ペアで totality を証明するには、何らかの **Core-Gap 比較原理** が必要になる。
そこを theorem として内部証明するか、将来の semantic bridge から導くか、ここが次の設計判断じゃ。
