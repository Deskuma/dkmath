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
\text{Body}_u^{(3)} - x^3 = (x+u)^3 - (x^3 + u^3)
\]

よって

\[
\text{Body}_u^{(3)} - x^3 = 3x^2u + 3xu^2
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

## 10. Lean 形式化の方針

### 10.1. 目的

二項定理そのものは mathlib の `add_pow` にあるが、

\[
(x+u)^d = x^d + \sum_{k=1}^{d-1} \binom{d}{k} x^k u^{d-k} + u^d
\]

という **Core–Beam–Gap 分解** は、そのままの命名では未整備である可能性が高い。

したがって、Lean 側では次の構造を自前で定義・補題化する価値がある。

- `Core d x := x^d`
- `Gap d u := u^d`
- `Beam d x u := \sum_{k=1}^{d-1} \binom{d}{k} x^k u^{d-k}`
- `Big d x u := (x+u)^d`

### 10.2. 基本定義案

減算を避け、まずは加法分解として定義するのが Lean 向きである。

```lean
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic

open Finset
open BigOperators

namespace DkMath

variable {R : Type*} [CommSemiring R]

/-- 左端の純冪。 -/
def Core (d : ℕ) (x : R) : R :=
  x ^ d

/-- 右端の純冪。 -/
def Gap (d : ℕ) (u : R) : R :=
  u ^ d

/-- パスカル三角形の外壁を除いた胴体部分。 -/
def Beam (d : ℕ) (x u : R) : R :=
  ∑ k in Finset.Icc 1 (d - 1), (Nat.choose d k : R) * x^k * u^(d-k)

/-- 全体構造。 -/
def Big (d : ℕ) (x u : R) : R :=
  (x + u) ^ d

end DkMath
```

### 10.3. 第一目標補題

目標は次の構造分解である。

\[
\text{Big} = \text{Core} + \text{Beam} + \text{Gap}
\]

Lean では次の形を狙う。

```lean
namespace DkMath

variable {R : Type*} [CommSemiring R]

lemma big_eq_core_beam_gap (d : ℕ) (x u : R) :
    Big d x u = Core d x + Beam d x u + Gap d u := by
  -- 土台は `add_pow`
  -- 端点 k=0, k=d を切り出し、中間和を `Beam` にまとめる
  sorry

end DkMath
```

この証明の骨格は、mathlib の `add_pow` を用いて

\[
(x+u)^d = \sum_{k=0}^{d} \binom{d}{k} x^k u^{d-k}
\]

を得てから、

- \(k=0\) 項 = \(u^d\)
- \(k=d\) 項 = \(x^d\)
- 中間項 = `Beam d x u`

へ切り分ける流れになる。

### 10.4. Body の定義と加法分解

`Nat` では減算が扱いにくいので、まずは加法分解として扱うのが安定である。

\[
\text{Body}_u^{(d)} = x^d + \text{Beam}_d(x,u)
\]

Lean では

```lean
namespace DkMath

variable {R : Type*} [CommSemiring R]

/-- Gap を除いた片側構造。 -/
def Body (d : ℕ) (x u : R) : R :=
  Core d x + Beam d x u

lemma big_eq_body_add_gap (d : ℕ) (x u : R) :
    Big d x u = Body d x u + Gap d u := by
  simp [Body, big_eq_core_beam_gap, add_assoc]

end DkMath
```

としておくと、後で `CanonicallyOrderedCommSemiring` や `LinearOrderedSemiring` 上で不等式へ発展しやすい。

### 10.5. d = 3 の特化形

\[
\text{Beam}_3(x,u)=3x^2u+3xu^2=3xu(x+u)
\]

これを専用補題として切り出すと、後続の議論が楽になる。

```lean
namespace DkMath

variable {R : Type*} [CommSemiring R]

lemma beam_three_eq (x u : R) :
    Beam 3 x u = 3 * x^2 * u + 3 * x * u^2 := by
  sorry

lemma beam_three_factor (x u : R) :
    Beam 3 x u = 3 * x * u * (x + u) := by
  sorry

lemma big_three_eq_core_beam_gap (x u : R) :
    Big 3 x u = x^3 + Beam 3 x u + u^3 := by
  simpa [Big, Core, Gap] using big_eq_core_beam_gap (R := R) 3 x u

end DkMath
```

### 10.6. d = 2 の特化形

\[
\text{Beam}_2(x,u)=2xu
\]

\[
\text{Body}_u^{(2)}=x^2+2xu=x(x+2u)
\]

Lean では

```lean
namespace DkMath

variable {R : Type*} [CommSemiring R]

lemma beam_two_eq (x u : R) :
    Beam 2 x u = 2 * x * u := by
  sorry

lemma body_two_eq_factor (x u : R) :
    Body 2 x u = x * (x + 2 * u) := by
  sorry

end DkMath
```

を整える。

ここで大事なのは、`d=2` では平方数になる **例が存在する** のであって、常に平方数になるわけではない、という整理である。

### 10.7. 「Body は純冪ではない」の書き方

言葉としての「足りない」を Lean に直接書くのではなく、次の形に翻訳する。

- 「Big から Gap が抜けた」

  \[
  \text{Big} = \text{Body} + \text{Gap}
  \]

- 「Body は Core より大きい」

  \[
  \text{Body} = \text{Core} + \text{Beam}, \qquad \text{Beam} > 0
  \]

- よって

  \[
  \text{Body} > \text{Core}
  \]

この方針で、不等式は `LinearOrderedSemiring` などに型を上げて扱う。

```lean
namespace DkMath

variable {R : Type*} [LinearOrderedSemiring R]

lemma body_gt_core_of_pos
    {d : ℕ} (hd : 2 ≤ d) {x u : R}
    (hx : 0 < x) (hu : 0 < u) :
    Core d x < Body d x u := by
  -- Beam > 0 を示してから加法で押し上げる
  sorry

end DkMath
```

### 10.8. d = 3 と FLT3 の接続

`Body 3 x u` が立方数であると仮定すると

\[
z^3 = (x+u)^3 - u^3
\]

となり、移項して

\[
z^3 + u^3 = (x+u)^3
\]

を得る。これを FLT3 の不可能性と接続する。

Lean では

```lean
namespace DkMath

lemma body_three_eq_cube_implies_flt_shape
    (x u z : ℕ)
    (hz : z^3 = x^3 + Beam 3 x u) :
    z^3 + u^3 = (x + u)^3 := by
  -- `Big = Core + Beam + Gap` を用いて式変形
  sorry

end DkMath
```

のような橋渡し補題を先に置くとよい。

### 10.9. 実装上の注意

- `Nat` 上の減算は扱いづらいので、まずは **加法分解** で進める。
- 一般定理は `CommSemiring` 上で作り、不等式や正値性は `StrictOrderedSemiring` / `LinearOrderedSemiring` に上げる。
- `Beam` の添字集合は `Finset.Icc 1 (d-1)` で定義するのが自然。
- 証明の土台は `add_pow`。専用構造定理はその上に構築する。
- `d=2`, `d=3` の特化補題は別に持つと、その後の議論が急に楽になる。

### 10.10. 研究上の位置づけ

この Core–Beam–Gap 分解は、単なる二項定理の言い換えではなく、

- 純冪の両端
- 中間結合構造
- Gap 除去後の Body

を分離して扱うための **構造言語** である。

特に

\[
\text{Beam}_d(x,u)=\sum_{k=1}^{d-1}\binom{d}{k}x^k u^{d-k}
\]

を **Pascal's Triangle Body** とみなすことで、二項定理の外壁を除いた内部構造が独立対象として現れる。

これは今後、

- `Body > Core`
- `Body` の純冪非一致
- `d=2` と `d=3` の分岐
- FLT3 への橋渡し

を整理するための基本語彙になる。

---
