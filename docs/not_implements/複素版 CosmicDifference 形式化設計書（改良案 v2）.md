# 複素版 `CosmicDifference*` 形式化設計書 v2

## 1. 目的

本設計は、既存の実数版

- `DkMath.CosmicFormula.CosmicDifferenceKernel`
- `DkMath.CosmicFormula.CosmicDerivativeBasic`
- `DkMath.CosmicFormula.CosmicDerivativePower`
- `DkMath.CosmicFormula.CosmicDerivativePowerLimit`
- `DkMath.CosmicFormula.CosmicDerivativePolynomial`
- `DkMath.CosmicFormula.CosmicFormulaDerivativeBridge`

を、そのまま **複素数 \(\mathbb{C}\) 版** へ持ち上げるための実装設計である。

狙いは次の三つじゃ。

1. **複素差分核**
   \[
   K_f(z,u) := \frac{f(z+u)-f(z)}{u}
   \qquad (u \neq 0)
   \]
   を exact に定義する。

2. その差分核を通して、**複素微分係数** を
   \[
   \text{差分核} \to \text{複素微分}
   \]
   の流れで固定する。

3. 宇宙式側の
   \[
   (z+u)^d - z^d = u \cdot G_{d-1}(z,u)
   \]
   という **GC 的骨格** を、冪 kernel・多項式 kernel・平方宇宙式 bridge へ接続する。

本設計では、解析接続や D-加群をいきなり形式化しない。
まずは

\[
\text{差分核} \to \text{複素微分} \to \text{冪 kernel} \to \text{多項式 kernel} \to \text{宇宙式 bridge}
\]

を Lean 上で安全に固定することを目標とする。

---

## 2. 基本方針

## 2.1. 理論順序

複素版でも本線は変わらぬ。

\[
\boxed{
GC \to \text{複素差分核} \to \text{複素微分係数} \to \text{局所生成核} \to \text{複素特異点解析}
}
\]

つまり、先に露出すべきは D-加群そのものではなく、**微分係数側の核** じゃ。

## 2.2. GC の位置づけ

複素数 \(z,h \in \mathbb{C}\) に対し、

\[
\mathrm{Body}(z,h;d) := (z+h)^d - z^d
\]

と置くと、

\[
\mathrm{Body}(z,h;d) = h \cdot G_{d-1}(z,h)
\]

と分解できる。
このとき

\[
GC_d(z,h) := \frac{(z+h)^d - z^d}{h}
\qquad (h \neq 0)
\]

は、冪関数に対する複素 cosmic kernel の基本例である。

したがって本設計では、

- `complexCosmicKernel` は一般関数版
- `powerKernelC` は冪関数版
- `GC_d` はその数学的解釈名

として扱う。

## 2.3. 実装原則

- 先に **定義** を置く
- 次に **exact algebra** を置く
- その後で **limit / derivative** を置く
- 解析接続・可除特異点の一般定理は後段へ回す

---

## 3. 推奨ファイル構成

本設計では、次の **6 本** を推奨する。

```text
lean/dk_math/DkMath/CosmicFormula/CosmicDifferenceKernelComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicDerivativeBasicComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePowerComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePowerLimitComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePolynomialComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDerivativeBridgeComplex.lean
```

## 3.1. 命名方針

`Holomorphic*` よりも `Derivative*Complex` を推奨する。
理由は次の通り。

- 実数版との対応が一目で分かる
- 現段階では「局所微分核」の形式化が中心であり、
  `Holomorphic` という語はやや強い
- 後で `CosmicAnalyticKernel.lean` や `CosmicHolomorphicExtension.lean` を足しやすい

---

## 4. 各ファイルの役割

## 4.1. `CosmicDifferenceKernelComplex.lean`

役割:

- `cdelta`
- `complexCosmicKernel`
- 和・差・スカラー倍・積・有限和に関する exact law

ここは純代数層であり、複素解析そのものはまだ入れない。

## 4.2. `CosmicDerivativeBasicComplex.lean`

役割:

- `HasDerivAt` と punctured limit の橋
- `id`, `const` の基本例
- 複素微分係数が cosmic kernel 極限として現れることの固定

## 4.3. `CosmicDerivativePowerComplex.lean`

役割:

- `powerKernelC`
- `powerKernelC_eq_GN_swap`
- `sub_pow_eq_u_mul_powerKernelC`
- 冪関数の cosmic kernel が多項式 kernel に一致すること

## 4.4. `CosmicDerivativePowerLimitComplex.lean`

役割:

- `powerKernelC` の連続性
- `powerKernelC_zero`
- `tendsto_powerKernelC_zero`
- `hasDerivAt_pow_complexCosmic`

ここで初めて、冪関数の複素微分係数が exact に出る。

## 4.5. `CosmicDerivativePolynomialComplex.lean`

役割:

- `polynomialKernelExtC`
- 多項式評価に対する complex cosmic kernel の有限和分解
- `polynomialKernelExtC_zero`
- `hasDerivAt_polynomial_eval_complexCosmic`

ここは「中心で埋めた kernel」の最初の完成形じゃ。

## 4.6. `CosmicFormulaDerivativeBridgeComplex.lean`

役割:

- 平方宇宙式との橋
- `cdelta (fun w => w^2)` と `powerKernelC 2` の接続
- 複素平方宇宙式
  \[
  (z+u)^2 - z(z+2u) = u^2
  \]
  の再表現

---

## 5. 理論の流れ

## 5.1. 第1段. 複素差分核

まず

\[
\mathrm{cdelta}_f(z,u) := f(z+u) - f(z)
\]

\[
\mathrm{complexCosmicKernel}_f(z,u) := \frac{f(z+u)-f(z)}{u}
\qquad (u \neq 0)
\]

を定義する。

これは実数版の単なる複素化であり、和・差・スカラー倍・有限和については完全に平行移植できる。

## 5.2. 第2段. 複素微分との橋

ここで固定したい主定理はこれじゃ。

\[
\text{HasDerivAt } f \, L \, z
\iff
\lim_{u \to 0,\; u \neq 0}
\frac{f(z+u)-f(z)}{u} = L
\]

複素版では、実数版の左右極限と違い、**全方向の \(u \in \mathbb{C}\)** に対して極限が一致することが本質になる。

したがって `complexCosmicKernel` は、

> 方向依存を失って一つへ閉じるかどうかを観測する局所生成核

として読むのがよい。

## 5.3. 第3段. 冪 kernel

冪関数では

\[
(z+u)^d - z^d = u \, P_d(z,u)
\]

が exact に成り立つ。
この \(P_d(z,u)\) を `powerKernelC d z u` として定義する。

さらに、GN との対応として

\[
powerKernelC(d,z,u) = GN_d(u,z)
\]

という変数 swap 形を補題として固定する。

これは

- 宇宙式側の \(G\)-構造
- 差分正規化核
- 微分極限核

が、すべて同じ骨格の別表現であることを示す要所じゃ。

## 5.4. 第4段. 冪 kernel の極限

\[
powerKernelC(d,z,0) = d z^{d-1}
\]

を示し、その連続性から

\[
\lim_{u \to 0} powerKernelC(d,z,u) = d z^{d-1}
\]

を得る。

ここから

\[
\text{HasDerivAt } (w \mapsto w^d)\, ((d:\mathbb{C}) z^{d-1})\, z
\]

が従う。

## 5.5. 第5段. 多項式 kernel 拡張

多項式 \(p\) に対し、

\[
polynomialKernelExtC(p,z,u) := \sum_{n=0}^{\deg p} p_n \, powerKernelC(n,z,u)
\]

を定義する。

これは punctured neighborhood では元の差分商と一致し、中心では

\[
polynomialKernelExtC(p,z,0) = p'(z)
\]

となる。

ゆえに `polynomialKernelExtC` は、

> punctured kernel を中心で埋めた局所生成核

になっておる。

## 5.6. 第6段. 宇宙式 bridge

最後に平方宇宙式を複素版で書き直す。

\[
(z+u)^2 - z(z+2u) = u \bigl(powerKernelC(2,z,u) - 2z\bigr) = u^2
\]

これにより、複素差分核と宇宙式 gap が同一骨格を持つことが露出する。

---

## 6. 各段で置くべき中心定理

## 6.1. 最初に通すべき 3 本

```lean
theorem hasDerivAt_iff_tendsto_complexCosmicKernel ...
theorem sub_pow_eq_u_mul_powerKernelC ...
theorem hasDerivAt_pow_complexCosmic ...
```

この 3 本が通れば、本線はほぼ固まる。

## 6.2. 次に通すべき 3 本

```lean
theorem powerKernelC_zero ...
theorem complexCosmicKernel_polynomial_eval_eq_polynomialKernelExtC_of_ne_zero ...
theorem hasDerivAt_polynomial_eval_complexCosmic ...
```

ここまでで、冪と多項式については複素 kernel 理論が自立する。

## 6.3. 最後に置くべき bridge

```lean
theorem cdelta_pow_two_eq_u_mul_powerKernelC_two ...
theorem complex_cosmic_formula_unit_eq_u_mul_powerKernelC_two_gap ...
theorem complex_cosmic_formula_unit_eq_u_sq ...
```

---

## 7. 依存関係

推奨 import 順は次の通り。

```text
CosmicDifferenceKernelComplex
  ↓
CosmicDerivativeBasicComplex
  ↓
CosmicDerivativePowerComplex
  ↓
CosmicDerivativePowerLimitComplex
  ↓
CosmicDerivativePolynomialComplex
  ↓
CosmicFormulaDerivativeBridgeComplex
```

## 7.1. 依存上の注意

- `CosmicDifferenceKernelComplex` は `Mathlib` だけに近い薄い層にする
- `CosmicDerivativePowerComplex` は `CosmicFormulaBinom` に依存してよい
- `CosmicFormulaDerivativeBridgeComplex` は宇宙式側 bridge に専念し、解析一般論を混ぜない

---

## 8. コード骨格

## 8.1. `CosmicDifferenceKernelComplex.lean`

```lean
import Mathlib

namespace DkMath.CosmicFormula

noncomputable section

def cdelta (f : ℂ → ℂ) (z u : ℂ) : ℂ :=
  f (z + u) - f z

def complexCosmicKernel (f : ℂ → ℂ) (z u : ℂ) : ℂ :=
  cdelta f z u / u

@[simp] theorem cdelta_zero_right (f : ℂ → ℂ) (z : ℂ) :
    cdelta f z 0 = 0 := by
  simp [cdelta]

theorem cdelta_add (f g : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => f w + g w) z u = cdelta f z u + cdelta g z u := by
  unfold cdelta
  ring

theorem cdelta_mul (f g : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => f w * g w) z u
      = f (z + u) * cdelta g z u + g z * cdelta f z u := by
  unfold cdelta
  ring

end

end DkMath.CosmicFormula
```

## 8.2. `CosmicDerivativeBasicComplex.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex

namespace DkMath.CosmicFormula

theorem hasDerivAt_iff_tendsto_complexCosmicKernel
    {f : ℂ → ℂ} {z L : ℂ} :
    HasDerivAt f L z ↔
      Filter.Tendsto (fun u : ℂ => complexCosmicKernel f z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds L) := by
  simpa [complexCosmicKernel, cdelta, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_iff_tendsto_slope_zero (f := f) (f' := L) (x := z))

end DkMath.CosmicFormula
```

## 8.3. `CosmicDerivativePowerComplex.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex
import DkMath.CosmicFormula.CosmicFormulaBinom

namespace DkMath.CosmicFormula

open scoped BigOperators
noncomputable section

def powerKernelC (d : ℕ) (z u : ℂ) : ℂ :=
  Finset.sum (Finset.range d) (fun j =>
    (Nat.choose d (j + 1) : ℂ) * z ^ (d - 1 - j) * u ^ j)

theorem sub_pow_eq_u_mul_powerKernelC (d : ℕ) (z u : ℂ) :
    (z + u) ^ d - z ^ d = u * powerKernelC d z u := by
  sorry

end

end DkMath.CosmicFormula
```

## 8.4. `CosmicDerivativePowerLimitComplex.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDerivativeBasicComplex
import DkMath.CosmicFormula.CosmicDerivativePowerComplex

namespace DkMath.CosmicFormula

theorem powerKernelC_zero (d : ℕ) (z : ℂ) :
    powerKernelC d z 0 = (d : ℂ) * z ^ (d - 1) := by
  sorry

theorem hasDerivAt_pow_complexCosmic (d : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ d) ((d : ℂ) * z ^ (d - 1)) z := by
  sorry

end DkMath.CosmicFormula
```

## 8.5. `CosmicDerivativePolynomialComplex.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDerivativePowerLimitComplex

namespace DkMath.CosmicFormula

def polynomialKernelExtC (p : Polynomial ℂ) (z u : ℂ) : ℂ :=
  Finset.sum (Finset.range (p.natDegree + 1)) (fun n =>
    p.coeff n * powerKernelC n z u)

theorem polynomialKernelExtC_zero (p : Polynomial ℂ) (z : ℂ) :
    polynomialKernelExtC p z 0 = p.derivative.eval z := by
  sorry

end DkMath.CosmicFormula
```

## 8.6. `CosmicFormulaDerivativeBridgeComplex.lean`

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex
import DkMath.CosmicFormula.CosmicDerivativePowerLimitComplex

namespace DkMath.CosmicFormula

theorem complex_cosmic_formula_unit_eq_u_sq (z u : ℂ) :
    ((z + u) ^ 2 - z * (z + 2 * u)) = u ^ 2 := by
  ring

end DkMath.CosmicFormula
```

---

## 9. 数学的意味

本設計で得られる意味は次の通りじゃ。

## 9.1. 複素微分の kernel 定式化

\[
\text{HasDerivAt } f \, L \, z
\iff
\lim_{u \to 0,\;u\neq 0}\frac{f(z+u)-f(z)}{u}=L
\]

を DkMath の cosmic kernel 言語で固定できる。

## 9.2. 冪関数の GC 骨格の露出

\[
GC_d(z,u) = \frac{(z+u)^d-z^d}{u}
\]

は、極限後に微分になるのではなく、最初から多項式 kernel を内蔵している。

## 9.3. 可除特異点型 extension の最小模型

`polynomialKernelExtC` は、中心で埋めた正則化 kernel の最初の完成例になる。

## 9.4. 宇宙式との一致

\[
(z+u)^2 - z(z+2u) = u^2
\]

が複素でも崩れぬことで、差分核・微分核・宇宙式 gap が同じ構造線上にあることが分かる。

---

## 10. 将来拡張

## 10.1. `CosmicAnalyticKernel.lean`

次段候補として

```text
lean/dk_math/DkMath/CosmicFormula/CosmicAnalyticKernel.lean
```

を置き、次を扱う。

- `powerKernelC d z` が \(u\) に関して entire
- `polynomialKernelExtC p z` が analytic
- punctured kernel の removable singularity 型拡張

## 10.2. GC から CFBRC への接続

GC を複素差分骨格、CFBRC を複素観測器として見るなら、

\[
GC \to \text{complex kernel} \to \text{phase / oscillation 観測} \to \text{CFBRC}
\]

という順で接続できる。

## 10.3. KUS support への接続

複素 \(u\) に対して

- \(|u|\)
- \(\arg u\)
- 枝番号
- 周回回数

を blueprint 化すれば、局所 kernel を support つき観測量として持ち上げられる。

---

## 11. 実装優先順

## 11.1. 最優先

1. `CosmicDifferenceKernelComplex.lean`
2. `CosmicDerivativeBasicComplex.lean`
3. `CosmicDerivativePowerComplex.lean`

## 11.2. 次点

1. `CosmicDerivativePowerLimitComplex.lean`
2. `CosmicDerivativePolynomialComplex.lean`

## 11.3. 最後

1. `CosmicFormulaDerivativeBridgeComplex.lean`

---

## 12. 注意点

## 12.1. `hasDerivAt_iff_tendsto_slope_zero`

mathlib 側で \(\mathbb{C} \to \mathbb{C}\) にそのまま通る前提で書けるが、版差がある場合は specialized lemma を噛ませる。

## 12.2. `CosmicFormulaBinom.GN` の一般性

`GN` が \(\mathbb{C}\) 係数へ自然に持ち上がることを確認する。
もし係数体が固定されているなら、先に `CosmicFormulaBinom` 側の抽象化が要る。

## 12.3. `Polynomial` 関連補題名

`Polynomial.derivative_eval` や `as_sum_range_C_mul_X_pow` などは版差があるので、実ビルドで補正する。

## 12.4. `Holomorphic` 命名は後段へ残す

本設計の中心は「局所微分核」であり、解析接続や `AnalyticAt` 一般論はまだ次段じゃ。
ゆえに、ファイル名は `Derivative*Complex` を本線とする。

---

## 13. まとめ

複素版の核心はこれじゃ。

> **解析接続をいきなり証明するのではなく、まず複素差分核を exact に定義し、その内部に埋め込まれている局所生成則を露出する。**

それにより、

\[
\text{差分核} \to \text{複素微分} \to \text{冪 kernel} \to \text{多項式 kernel} \to \text{宇宙式 bridge}
\]

という安全な主線が得られる。

この流れなら、

- Core = 局所生成核
- Beam = 近傍へ伸びる展開則
- Gap = punctured center / 特異境界

という宇宙式の見方を失わずに、複素解析側へ橋を架けられる。

---

## 14. 最短着手メモ

本当に最短で行くなら、まずこの 3 本を通す。

```lean
theorem hasDerivAt_iff_tendsto_complexCosmicKernel ...
theorem sub_pow_eq_u_mul_powerKernelC ...
theorem hasDerivAt_pow_complexCosmic ...
```

ここが通れば、複素版 GC の核はほぼ立つ。
その先は多項式拡張と宇宙式 bridge を順に積めばよい。
