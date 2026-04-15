# Lie代数と宇宙式 Lean 実装設計書

## 1. 題目

**初等恒等式**

\[
f(x) = (x+1)^2 - x(x+2) - 1 = 0
\]

から出発して、

\[
(x+u)^d - x^d
\]

の差分構造を

- 多項式の平行移動作用
- 微分作用素
- 斉次二変数多項式
- \(\mathfrak{sl}_2\) 型の作用素関係

へ接続する Lean 実装の設計を与える。

本設計では、いきなり「Lie 群の指数写像」や「既約表現の完全抽象化」を目指さず、まず Lean で堅く通る **代数的核** を先に作る。
そのうえで、最後に Lie 理論として読むための包装を与える。

---

## 2. 実装の到達目標

最小目標は次の 4 層である。

### 2.1. 層 A. 基本恒等式

\[
(x+u)^2 - x(x+2u) = u^2
\]

および

\[
(x+1)^2 - x(x+2) - 1 = 0
\]

を、可換環上で証明する。

### 2.2. 層 B. 平行移動作用素

一変数多項式に対し、平行移動

\[
T_u(p)(X) := p(X+u)
\]

を定義し、

\[
T_u(X^d) = (X+u)^d
\]

および

\[
T_u(X^d) - X^d = u\,G_{d-1}(X,u)
\]

を形式化する。

### 2.3. 層 C. 斉次二変数版

二変数多項式で

\[
(X+Y)^d - X^d = Y \, H_{d-1}(X,Y)
\]

を構成し、係数列が二項展開そのものであることを示す。

### 2.4. 層 D. \(\mathfrak{sl}_2\) 型作用素

斉次二変数多項式上の作用素

\[
E := Y\partial_X,\qquad
F := X\partial_Y,\qquad
H := X\partial_X - Y\partial_Y
\]

を導入し、基底モノミアル上で

\[
[E,F]=H,\qquad [H,E]=2E,\qquad [H,F]=-2F
\]

に対応する関係式を証明する。

---

## 3. 設計上の大方針

## 3.1. 先に「作用素」で固める

Lean では、抽象 Lie 理論を最初から押し出すより、

- `Polynomial`
- `MvPolynomial`
- `LinearMap`
- `Module.End`

の範囲でまず証明を積んだ方が堅い。

したがって第 1 段階では
「Lie 代数として宣言する」より先に
「Lie 的に読むべき作用素関係を証明する」ことを優先する。

## 3.2. 一変数から二変数へ上げる

\[
(x+u)^d - x^d
\]

をそのまま扱うと、\(u\) は係数なのか変数なのかが曖昧になりやすい。
Lean ではこれを避けるため、二変数版

\[
(X+Y)^d - X^d
\]

を先に `MvPolynomial` 上で作るのがよい。
その後、評価写像 \(Y \mapsto u\) により一変数版へ落とす。

## 3.3. \(\mathfrak{sl}_2\) 作用は「基底上の公式」から入る

最初から homogeneous submodule 全体を作ると重い。
まずはモノミアル基底

\[
e_{d,k} := X^{d-k}Y^k
\qquad (0 \le k \le d)
\]

上で

\[
E(e_{d,k}) = (d-k)e_{d,k+1},\qquad
F(e_{d,k}) = k\,e_{d,k-1},\qquad
H(e_{d,k}) = (d-2k)e_{d,k}
\]

を示し、それを後で「\(\mathrm{Sym}^d\) 表現」と読むのがよい。

---

## 4. 推奨ディレクトリ構成

既存の `DkMath.CosmicFormula` との接続を意識しつつ、命名は中立的にする。

```text
lean/dk_math/DkMath/LieBridge/
  BasicIdentity.lean
  ShiftOperator.lean
  BivariateDifference.lean
  SL2MonomialAction.lean
  InnerProductBridge.lean
  Main.lean
```

### 4.1. 各ファイルの役割

#### `BasicIdentity.lean`

- 基本恒等式
- 二次の最小核
- `ring` で落ちる事実を整理

#### `ShiftOperator.lean`

- 一変数多項式の平行移動作用
- 差分作用素
- \(X^d\) に対する公式
- 評価写像との整合

#### `BivariateDifference.lean`

- `MvPolynomial` による二変数化
- \((X+Y)^d - X^d = Y \cdot H_{d-1}(X,Y)\)
- `H_{d-1}` の明示式

#### `SL2MonomialAction.lean`

- \(E,F,H\) の導入
- モノミアル基底上の作用式
- 交換子関係
- \(\mathfrak{sl}_2\) 型の骨格

#### `InnerProductBridge.lean`

- 中点・半差による二次形式恒等式
- 内積空間版
- 二次不変量としての読み替え

#### `Main.lean`

- import 集約
- 外部公開用エントリ

---

## 5. 層 A. 基本恒等式の実装

まずは完全に初等的な核を置く。

```lean
import Mathlib

namespace DkMath
namespace LieBridge

section Basic

variable {R : Type*} [CommRing R]

theorem quadratic_shift_identity (x u : R) :
    (x + u)^2 - x * (x + 2*u) = u^2 := by
  ring

theorem quadratic_shift_identity_one (x : R) :
    (x + 1)^2 - x * (x + 2) - 1 = 0 := by
  ring

end Basic

end LieBridge
end DkMath
```

### 5.1. このファイルでやるべきこと

上の 2 本に加え、次も置いてよい。

\[
A := x,\quad C := x+2u,\quad
M := \frac{A+C}{2},\quad D := \frac{C-A}{2}
\]

に対する

\[
M^2 - AC = D^2
\]

の一次元版である。

ただし分数が入るため、これは `[Ring R] [Invertible (2 : R)]` か
`[LinearOrderedField R]` など、係数の型クラス条件を分けて書くのがよい。

---

## 6. 層 B. 平行移動作用素の実装

## 6.1. 基本方針

一変数多項式 \(p(X)\) に対して

\[
T_u(p) := p(X+u)
\]

を `Polynomial.comp` で定義する。

Lean ではだいたい次の形になる。

```lean
import Mathlib

namespace DkMath
namespace LieBridge

open Polynomial

section Shift

variable {R : Type*} [CommSemiring R]

noncomputable def shift (u : R) : Polynomial R →ₐ[R] Polynomial R :=
{ toFun := fun p => p.comp (X + C u)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intro p q; simp [Polynomial.comp]
  map_mul' := by intro p q; simp [Polynomial.comp]
  commutes' := by intro r; simp }

theorem shift_X (u : R) :
    shift u X = X + C u := by
  simp [shift]

theorem shift_X_pow (u : R) (d : ℕ) :
    shift u (X^d : Polynomial R) = (X + C u)^d := by
  simp [shift]

end Shift

end LieBridge
end DkMath
```

## 6.2. この段階の主要定理

### 定理 B.1

\[
T_u(X^d) = (X+u)^d
\]

Lean では `C u` が係数埋め込みになるので、厳密には

\[
T_u(X^d) = (X + C(u))^d
\]

で表される。

### 定理 B.2

差分作用素

\[
\Delta_u := T_u - \mathrm{id}
\]

を `LinearMap` として定義し、

\[
\Delta_u(X^d) = (X+C(u))^d - X^d
\]

を証明する。

ここで `shift u` は `AlgHom` なので、差を取るためには `toLinearMap` に落とす。

```lean
noncomputable def shiftLin (u : R) : Polynomial R →ₗ[R] Polynomial R :=
  (shift u).toLinearMap

noncomputable def delta (u : R) : Polynomial R →ₗ[R] Polynomial R :=
  shiftLin u - LinearMap.id
```

### 定理 B.3

\[
(X+C(u))^d - X^d
\]

が `C u` で割れることを証明する。

ここは最初から「商」を定義するより、

\[
(X+Y)^d - X^d = Y \cdot H_{d-1}(X,Y)
\]

を二変数で先に作ってから評価した方が楽である。

---

## 7. 層 C. 二変数版の実装

## 7.1. なぜ二変数版を先に作るか

\[
(X+u)^d - X^d
\]

では \(u\) は係数である。
Lean では「変数として因数分解する」には二変数化が自然である。

よって `MvPolynomial (Fin 2) R` を使い、

- \(X := \mathrm{X}\,0\)
- \(Y := \mathrm{X}\,1\)

を導入して

\[
(X+Y)^d - X^d
\]

を扱う。

## 7.2. 変数の導入

```lean
import Mathlib

namespace DkMath
namespace LieBridge

open MvPolynomial

section Bivariate

variable {R : Type*} [CommSemiring R]

abbrev σ := Fin 2

noncomputable abbrev Xv : MvPolynomial σ R := X 0
noncomputable abbrev Yv : MvPolynomial σ R := X 1
```

## 7.3. 差分核 \(H_{d-1}\) の定義

まず明示式で定義する。

\[
H_{d-1}(X,Y)
:=
\sum_{j=0}^{d-1}
\binom{d}{j+1} X^{d-1-j}Y^j
\]

Lean では次のような形が候補となる。

```lean
noncomputable def diffQuot (d : ℕ) : MvPolynomial σ R :=
  ∑ j in Finset.range d,
    C (Nat.choose d (j+1)) * Xv^(d-1-j) * Yv^j
```

### 定理 C.1

\[
(X+Y)^d - X^d = Y \cdot \mathrm{diffQuot}(d)
\]

これは `Finset.sum_range_succ` と二項定理で通す。
係数環は少なくとも `[CommSemiring R]` で足りる。

### 定理 C.2

評価写像 \(Y \mapsto C(u)\) により、一変数版

\[
(X+C(u))^d - X^d = C(u)\cdot G_d(X,u)
\]

が得られる。

ここは `eval₂Hom` を使う方針になる。

---

## 8. 層 D. \(\mathfrak{sl}_2\) 型作用の実装

ここがこの設計の核である。
ただし最初から完全一般の Lie module を作る必要はない。

## 8.1. 実用的な第一歩

まずモノミアル

\[
e_{d,k} := X^{d-k}Y^k
\]

上での作用式を証明する。

## 8.2. 作用素の定義方針

候補は 2 つある。

### 方針 D-A. `MvPolynomial` の偏微分 API を使う

mathlib 側の API 名は版差がありうるが、概念的には

\[
\partial_X,\quad \partial_Y
\]

を使って

\[
E := Y\partial_X,\qquad
F := X\partial_Y,\qquad
H := X\partial_X - Y\partial_Y
\]

を `LinearMap` として定義する。

### 方針 D-B. まずモノミアル上の公式だけ定義する

API が重い場合は、基底モノミアル上で

\[
E(X^aY^b)=aX^{a-1}Y^{b+1}
\]

\[
F(X^aY^b)=bX^{a+1}Y^{b-1}
\]

\[
H(X^aY^b)=(a-b)X^aY^b
\]

を直接補題として証明する。
この方が Lean では通しやすいことが多い。

## 8.3. 目標定理

### 定理 D.1

\[
E(e_{d,k}) = (d-k)e_{d,k+1}
\]

### 定理 D.2

\[
F(e_{d,k}) = k e_{d,k-1}
\]

### 定理 D.3

\[
H(e_{d,k}) = (d-2k)e_{d,k}
\]

### 定理 D.4

交換子

\[
[E,F] := EF - FE
\]

について

\[
[E,F](e_{d,k}) = H(e_{d,k})
\]

### 定理 D.5

同様に

\[
[H,E](e_{d,k}) = 2E(e_{d,k}),\qquad
[H,F](e_{d,k}) = -2F(e_{d,k})
\]

これにより、`e_{d,k}` の張る有限次元空間の上で \(\mathfrak{sl}_2\) 関係式が成り立つ。

## 8.4. ここでの数学的意味

このとき

\[
(X+uY)^d =
\sum_{k=0}^{d} \binom{d}{k} u^k X^{d-k}Y^k
\]

は、最高ウェイトベクトル \(X^d\) に対する unipotent 軌道として読める。
Lean では最初はそこまで包まずとも、

- 係数列が二項係数であること
- \(E\) の反復作用でこの鎖が生成されること

を示せば十分強い。

---

## 9. 内積空間版の橋

これは Lie 代数本体ではないが、二次形式の橋として重要である。

\[
M := \frac{A+C}{2},\qquad D := \frac{C-A}{2}
\]

とおくと、

\[
\|M\|^2 - \langle A,C\rangle = \|D\|^2
\]

が成り立つ。

Lean では `InnerProductSpace ℝ V` 上で

```lean
theorem midpoint_halfDiff_identity
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A C : V) :
    ‖(A + C) / (2 : ℝ)‖^2 - ⟪A, C⟫_ℝ = ‖(C - A) / (2 : ℝ)‖^2 := by
  ...
```

のような形が候補になる。

ただし `‖v‖^2` と `inner` の変換補題が少々煩いので、第一段階では

\[
\langle M,M\rangle - \langle A,C\rangle = \langle D,D\rangle
\]

の形で証明してから `norm_sq_eq_inner` に落とすのがよい。

---

## 10. 実装順序

Lean の通しやすさを考えると、順序は次が最適である。

### 第 1 段階

`BasicIdentity.lean`

- 二次恒等式
- \(u=1\) 特化
- `ring` による自動化

### 第 2 段階

`ShiftOperator.lean`

- `shift`
- `shiftLin`
- `delta`
- `shift_X_pow`

### 第 3 段階

`BivariateDifference.lean`

- `Xv`, `Yv`
- `diffQuot`
- \((X+Y)^d - X^d = Y \cdot diffQuot(d)\)

### 第 4 段階

`SL2MonomialAction.lean`

- 基底モノミアルの導入
- \(E,F,H\) の作用式
- 交換子関係

### 第 5 段階

`InnerProductBridge.lean`

- 二次形式恒等式
- 幾何学的読み替え

---

## 11. ここではまだやらないこと

この設計段階では、次は後回しでよい。

### 11.1. 完全一般の Lie group 指数写像

\[
e^{uE}
\]

を一般論として formalize するのは重い。
まずはモノミアル上の有限和として扱う。

### 11.2. `LieAlgebra` / `LieModule` の完全包装

最終的にはよいが、最初からそこへ行くと API 依存で重くなりがち。
まず `LinearMap` と交換子で十分。

### 11.3. `SL(2,R)` 群作用の完全形式化

行列群からの作用の一般論は Phase 2 でよい。
Phase 1 では `E,F,H` の交換子関係までで十分強い。

---

## 12. 成功判定

この設計の成功条件は次の 3 点である。

### 12.1

\[
(X+Y)^d - X^d = Y \cdot H_{d-1}(X,Y)
\]

が Lean で明示式として通ること。

### 12.2

モノミアル基底上で

\[
E,F,H
\]

の作用式がすべて通ること。

### 12.3

交換子関係

\[
[E,F]=H,\qquad [H,E]=2E,\qquad [H,F]=-2F
\]

が少なくとも基底上で証明されること。

ここまで到達すれば、

「初等的な差分恒等式が、平行移動作用素と \(\mathfrak{sl}_2\) 型作用へ接続する」

という主張は Lean 上で十分に骨格化できたと見てよい。

---

## 13. `Main.lean` の想定

```lean
import DkMath.LieBridge.BasicIdentity
import DkMath.LieBridge.ShiftOperator
import DkMath.LieBridge.BivariateDifference
import DkMath.LieBridge.SL2MonomialAction
import DkMath.LieBridge.InnerProductBridge
```

必要に応じて namespace を揃え、外部からは `DkMath.LieBridge.Main` を import すれば全体が見えるようにする。

---

## 14. 将来拡張

この設計の先には、次の拡張がある。

### 14.1. 一般次数差分の導分表示

\[
(X+u)^d =
\sum_{k=0}^{d}\frac{u^k}{k!}\partial_X^k(X^d)
\]

を有限和として証明する。

### 14.2. 斉次空間の有限次元部分空間化

\[
\mathrm{span}\{X^{d-k}Y^k \mid 0\le k\le d\}
\]

を有限次元部分空間として明示し、その上の \(\mathfrak{sl}_2\) 表現を packages する。

### 14.3. Lie module としての正式宣言

`LinearMap` で証明した交換子関係を `LieAlgebra` / `LieModule` に持ち上げる。

---

## 15. 結語

Lean 実装では、最初から「壮大な理論名」を押し出す必要はない。
むしろ

\[
(x+u)^2 - x(x+2u) = u^2
\]

という最小核から始めて、

\[
(X+Y)^d - X^d = Y \cdot H_{d-1}(X,Y)
\]

へ上げ、そこから

\[
E = Y\partial_X,\quad F = X\partial_Y,\quad H = X\partial_X - Y\partial_Y
\]

の交換子関係へ到達する、という流れが最も堅い。

この流れならば、

- 初等恒等式
- 差分構造
- 平行移動作用
- 斉次多項式
- \(\mathfrak{sl}_2\) 型作用

が一本の Lean 証明系列として繋がる。

これが Phase 1 の設計として最も現実的であり、かつ拡張性も高い。
