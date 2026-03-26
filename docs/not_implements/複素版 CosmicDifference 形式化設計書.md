# 複素版 `CosmicDifference*` 形式化設計書

## 1. 目的

本設計は、既存の実数版

- `DkMath.CosmicFormula.CosmicDifferenceKernel`
- `DkMath.CosmicFormula.CosmicDerivativeBasic`
- `DkMath.CosmicFormula.CosmicDerivativePower`
- `DkMath.CosmicFormula.CosmicDerivativePowerLimit`
- `DkMath.CosmicFormula.CosmicDerivativePolynomial`
- `DkMath.CosmicFormula.CosmicFormulaDerivativeBridge`

を、そのまま **複素数 \(\mathbb{C}\) 版** へ持ち上げるための実装設計である。

狙いは二つある。

1. **複素微分の局所核** を、差分核
   \[
   K_f(z,u) := \frac{f(z+u)-f(z)}{u}
   \qquad (u \neq 0)
   \]

   として形式化すること。

2. その差分核を通して、正則性・局所生成核・可除特異点型の延長を
   **cosmic kernel の視点** から扱える土台を作ること。

ここで大切なのは、解析接続そのものをいきなり形式化するのではなく、まず

\[
\text{差分核} \to \text{複素微分} \to \text{冪核} \to \text{多項式核拡張}
\]

の流れを、既存の実数版と平行に複素数版で固定することである。

---

## 2. 提案ファイル構成

以下の 5 本を提案する。

```text
lean/dk_math/DkMath/CosmicFormula/CosmicDifferenceKernelComplex.lean
lean/dk_math/DkMath/CosmicFormula/CosmicHolomorphicBasic.lean
lean/dk_math/DkMath/CosmicFormula/CosmicHolomorphicPower.lean
lean/dk_math/DkMath/CosmicFormula/CosmicHolomorphicPolynomial.lean
lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDerivativeBridgeComplex.lean
```

命名理由は、

- `DifferenceKernel` は差分核の exact algebra
- `HolomorphicBasic` 以降で複素微分橋
- 最後に宇宙式への橋

という役割分担を明確にするためである。

---

## 3. 実装方針の要点

## 3.1. 基本方針

実数版で既に成立している

- `delta`
- `cosmicKernel`
- `HasDerivAt ↔ punctured limit`
- `powerKernel`
- `polynomialKernelExt`

を、**係数体 \(\mathbb{R}\) を \(\mathbb{C}\) に替えてそのまま持ち上げる**。

差分核の exact law は純代数なので、そのまま複素化できる。

## 3.2. 複素解析として何が増えるか

複素数版では、微分係数の極限

\[
\lim_{u \to 0,\;u \neq 0} \frac{f(z+u)-f(z)}{u}
\]

が、実数の左右極限ではなく、**全方向の \(u \in \mathbb{C}\)** に対して一つへ潰れることが本質になる。

つまり cosmic kernel は、複素世界では

> **局所生成核が方向依存を失って一つに閉じるかどうかを観測する道具**

となる。

---

## 4. 第1段. 差分核の複素版

以下をまず新設する。

```lean
import Mathlib

#print "file: DkMath.CosmicFormula.CosmicDifferenceKernelComplex"

namespace DkMath.CosmicFormula

noncomputable section

/--
Complex forward difference:
`cdelta f z u = f (z+u) - f z`.
-/
def cdelta (f : ℂ → ℂ) (z u : ℂ) : ℂ :=
  f (z + u) - f z

/--
Complex cosmic kernel:
`complexCosmicKernel f z u = (f(z+u)-f(z))/u`.
-/
def complexCosmicKernel (f : ℂ → ℂ) (z u : ℂ) : ℂ :=
  cdelta f z u / u

@[simp] theorem cdelta_zero_right (f : ℂ → ℂ) (z : ℂ) :
    cdelta f z 0 = 0 := by
  simp [cdelta]

theorem cdelta_add (f g : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => f w + g w) z u = cdelta f z u + cdelta g z u := by
  unfold cdelta
  ring

theorem cdelta_sub (f g : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => f w - g w) z u = cdelta f z u - cdelta g z u := by
  unfold cdelta
  ring

theorem cdelta_smul (a : ℂ) (f : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => a * f w) z u = a * cdelta f z u := by
  unfold cdelta
  ring

/--
Discrete product rule over `ℂ`.
-/
theorem cdelta_mul (f g : ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => f w * g w) z u
      = f (z + u) * cdelta g z u + g z * cdelta f z u := by
  unfold cdelta
  ring

theorem cdelta_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z u : ℂ) :
    cdelta (fun w => Finset.sum s (fun i => F i w)) z u
      = Finset.sum s (fun i => cdelta (F i) z u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [cdelta]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, cdelta_add, ih]

theorem complexCosmicKernel_eq (f : ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel f z u = (f (z + u) - f z) / u := by
  rfl

theorem complexCosmicKernel_add (f g : ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel (fun w => f w + g w) z u
      = complexCosmicKernel f z u + complexCosmicKernel g z u := by
  simp [complexCosmicKernel, cdelta_add, add_div]

theorem complexCosmicKernel_sub (f g : ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel (fun w => f w - g w) z u
      = complexCosmicKernel f z u - complexCosmicKernel g z u := by
  simp [complexCosmicKernel, cdelta_sub, sub_div]

theorem complexCosmicKernel_smul (a : ℂ) (f : ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel (fun w => a * f w) z u
      = a * complexCosmicKernel f z u := by
  simp [complexCosmicKernel, cdelta_smul, div_eq_mul_inv, mul_assoc]

theorem complexCosmicKernel_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel (fun w => Finset.sum s (fun i => F i w)) z u
      = Finset.sum s (fun i => complexCosmicKernel (F i) z u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [complexCosmicKernel, cdelta]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, complexCosmicKernel_add, ih]

/--
Product rule in kernel form over `ℂ`.
-/
theorem complexCosmicKernel_mul (f g : ℂ → ℂ) (z u : ℂ) :
    complexCosmicKernel (fun w => f w * g w) z u
      = f (z + u) * complexCosmicKernel g z u + g z * complexCosmicKernel f z u := by
  calc
    complexCosmicKernel (fun w => f w * g w) z u
        = cdelta (fun w => f w * g w) z u / u := rfl
    _ = (f (z + u) * cdelta g z u + g z * cdelta f z u) / u := by
      rw [cdelta_mul]
    _ = (f (z + u) * cdelta g z u) / u + (g z * cdelta f z u) / u := by
      rw [add_div]
    _ = f (z + u) * (cdelta g z u / u) + g z * (cdelta f z u / u) := by
      simp [div_eq_mul_inv, mul_left_comm, mul_comm]
    _ = f (z + u) * complexCosmicKernel g z u + g z * complexCosmicKernel f z u := rfl

end

end DkMath.CosmicFormula
```

---

## 5. 第2段. 複素微分との橋

ここでは、`HasDerivAt` と punctured limit を接続する。

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex

#print "file: DkMath.CosmicFormula.CosmicHolomorphicBasic"

namespace DkMath.CosmicFormula

/--
Complex derivative criterion in cosmic-kernel form.

`HasDerivAt f L z` iff
`complexCosmicKernel f z u -> L` as `u -> 0`, `u ≠ 0`.
-/
theorem hasDerivAt_iff_tendsto_complexCosmicKernel
    {f : ℂ → ℂ} {z L : ℂ} :
    HasDerivAt f L z ↔
      Filter.Tendsto (fun u : ℂ => complexCosmicKernel f z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds L) := by
  simpa [complexCosmicKernel, cdelta, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_iff_tendsto_slope_zero (f := f) (f' := L) (x := z))

theorem tendsto_complexCosmicKernel_of_hasDerivAt
    {f : ℂ → ℂ} {z L : ℂ}
    (h : HasDerivAt f L z) :
    Filter.Tendsto (fun u : ℂ => complexCosmicKernel f z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds L) :=
  (hasDerivAt_iff_tendsto_complexCosmicKernel).1 h

theorem hasDerivAt_of_tendsto_complexCosmicKernel
    {f : ℂ → ℂ} {z L : ℂ}
    (h :
      Filter.Tendsto (fun u : ℂ => complexCosmicKernel f z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds L)) :
    HasDerivAt f L z :=
  (hasDerivAt_iff_tendsto_complexCosmicKernel).2 h

theorem hasDerivAt_id_complexCosmic (z : ℂ) :
    HasDerivAt (fun w : ℂ => w) 1 z := by
  simpa using (hasDerivAt_id z)

theorem tendsto_complexCosmicKernel_id (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => complexCosmicKernel (fun w : ℂ => w) z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds (1 : ℂ)) := by
  exact tendsto_complexCosmicKernel_of_hasDerivAt (hasDerivAt_id_complexCosmic z)

theorem hasDerivAt_const_complexCosmic (z c : ℂ) :
    HasDerivAt (fun _ : ℂ => c) 0 z := by
  simpa using (hasDerivAt_const z c)

theorem tendsto_complexCosmicKernel_const (z c : ℂ) :
    Filter.Tendsto (fun u : ℂ => complexCosmicKernel (fun _ : ℂ => c) z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ))) (nhds (0 : ℂ)) := by
  exact tendsto_complexCosmicKernel_of_hasDerivAt (hasDerivAt_const_complexCosmic z c)
```

### 補足

ここで得られるのは、複素正則性の最小核である。

- 実数版では「左右から極限が一致」
- 複素版では「全方向の \(u\) から極限が一致」

ゆえに `complexCosmicKernel` は、複素微分の **方向独立な局所生成核** を観測する装置となる。

---

## 6. 第3段. 冪関数の複素 kernel

宇宙式側との接続を見せる中核である。

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.CosmicFormula.CosmicHolomorphicPower"

namespace DkMath.CosmicFormula

open scoped BigOperators

noncomputable section

/--
Complex power kernel:
the polynomial quotient of `(z+u)^d - z^d` by `u`.
-/
def powerKernelC (d : ℕ) (z u : ℂ) : ℂ :=
  Finset.sum (Finset.range d) (fun j =>
    (Nat.choose d (j + 1) : ℂ) * z ^ (d - 1 - j) * u ^ j)

/--
Compatibility with `GN` after scalar lift to `ℂ`.
-/
theorem powerKernelC_eq_GN_swap (d : ℕ) (z u : ℂ) :
    powerKernelC d z u = DkMath.CosmicFormulaBinom.GN d u z := by
  unfold powerKernelC DkMath.CosmicFormulaBinom.GN
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
Exact factorization over `ℂ`:
`(z+u)^d - z^d = u * powerKernelC d z u`.
-/
theorem sub_pow_eq_u_mul_powerKernelC (d : ℕ) (z u : ℂ) :
    (z + u) ^ d - z ^ d = u * powerKernelC d z u := by
  have h :=
    (DkMath.CosmicFormulaBinom.cosmic_id_csr' (R := ℂ) (d := d) (x := u) (u := z))
  calc
    (z + u) ^ d - z ^ d = (u + z) ^ d - z ^ d := by
      simp [add_comm]
    _ = (u * DkMath.CosmicFormulaBinom.GN d u z + z ^ d) - z ^ d := by
      rw [h]
    _ = u * DkMath.CosmicFormulaBinom.GN d u z := by
      ring
    _ = u * powerKernelC d z u := by
      rw [powerKernelC_eq_GN_swap]

theorem complexCosmicKernel_pow_eq_powerKernelC_of_ne_zero
    (d : ℕ) (z u : ℂ) (hu : u ≠ 0) :
    complexCosmicKernel (fun w : ℂ => w ^ d) z u = powerKernelC d z u := by
  unfold complexCosmicKernel cdelta
  calc
    ((z + u) ^ d - z ^ d) / u = (u * powerKernelC d z u) / u := by
      rw [sub_pow_eq_u_mul_powerKernelC]
    _ = powerKernelC d z u := by
      exact mul_div_cancel_left₀ (powerKernelC d z u) hu
```

### この段の意味

\[
(z+u)^d - z^d = u \, P_d(z,u)
\]

が exact に立つことにより、複素微分係数は極限後に急に現れるのではなく、**差分の内部に最初から局所生成多項式として埋め込まれている** と読める。

これが「生成則の生成理由」を見るための第一の窓になる。

---

## 7. 第4段. 冪 kernel の極限と複素微分

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicHolomorphicBasic
import DkMath.CosmicFormula.CosmicHolomorphicPower

#print "file: DkMath.CosmicFormula.CosmicHolomorphicPowerLimit"

namespace DkMath.CosmicFormula

theorem continuous_powerKernelC (d : ℕ) (z : ℂ) :
    Continuous (fun u : ℂ => powerKernelC d z u) := by
  unfold powerKernelC
  continuity

theorem powerKernelC_zero (d : ℕ) (z : ℂ) :
    powerKernelC d z 0 = (d : ℂ) * z ^ (d - 1) := by
  cases d with
  | zero =>
      simp [powerKernelC]
  | succ n =>
      unfold powerKernelC
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [hj0]
      · simp

theorem tendsto_powerKernelC_zero (d : ℕ) (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => powerKernelC d z u)
      (nhds (0 : ℂ))
      (nhds ((d : ℂ) * z ^ (d - 1))) := by
  simpa [powerKernelC_zero] using (continuous_powerKernelC d z).tendsto 0

theorem tendsto_powerKernelC_zero_punctured (d : ℕ) (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => powerKernelC d z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
      (nhds ((d : ℂ) * z ^ (d - 1))) :=
  (tendsto_powerKernelC_zero d z).mono_left nhdsWithin_le_nhds

theorem hasDerivAt_pow_complexCosmic (d : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ d) ((d : ℂ) * z ^ (d - 1)) z := by
  have hpow :
      Filter.Tendsto (fun u : ℂ => powerKernelC d z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
        (nhds ((d : ℂ) * z ^ (d - 1))) :=
    tendsto_powerKernelC_zero_punctured d z
  have hcosmic :
      Filter.Tendsto (fun u : ℂ => complexCosmicKernel (fun w : ℂ => w ^ d) z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
        (nhds ((d : ℂ) * z ^ (d - 1))) := by
    refine tendsto_nhdsWithin_congr ?hEq hpow
    intro u hu
    have hu0 : u ≠ 0 := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
    exact (complexCosmicKernel_pow_eq_powerKernelC_of_ne_zero d z u hu0).symm
  exact hasDerivAt_of_tendsto_complexCosmicKernel hcosmic
```

---

## 8. 第5段. 多項式の複素 kernel 拡張

ここで、可除特異点型の「中心で埋まる kernel」を作る。

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicHolomorphicPowerLimit

#print "file: DkMath.CosmicFormula.CosmicHolomorphicPolynomial"

namespace DkMath.CosmicFormula

theorem complexCosmicKernel_monomial_of_ne_zero
    (a z u : ℂ) (n : ℕ) (hu : u ≠ 0) :
    complexCosmicKernel (fun w : ℂ => a * w ^ n) z u = a * powerKernelC n z u := by
  calc
    complexCosmicKernel (fun w : ℂ => a * w ^ n) z u
        = a * complexCosmicKernel (fun w : ℂ => w ^ n) z u := by
          simpa using (complexCosmicKernel_smul a (fun w : ℂ => w ^ n) z u)
    _ = a * powerKernelC n z u := by
      rw [complexCosmicKernel_pow_eq_powerKernelC_of_ne_zero n z u hu]

theorem complexCosmicKernel_eval_monomial_of_ne_zero
    (a z u : ℂ) (n : ℕ) (hu : u ≠ 0) :
    complexCosmicKernel (fun w : ℂ => (Polynomial.monomial n a).eval w) z u
      = a * powerKernelC n z u := by
  simpa [Polynomial.eval_monomial] using
    (complexCosmicKernel_monomial_of_ne_zero a z u n hu)

/--
Polynomial kernel extension over `ℂ`.
-/
def polynomialKernelExtC (p : Polynomial ℂ) (z u : ℂ) : ℂ :=
  Finset.sum (Finset.range (p.natDegree + 1)) (fun n => p.coeff n * powerKernelC n z u)

theorem complexCosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernelC_of_ne_zero
    (p : Polynomial ℂ) (z u : ℂ) (hu : u ≠ 0) :
    complexCosmicKernel (fun w : ℂ => p.eval w) z u
      = Finset.sum (Finset.range (p.natDegree + 1))
          (fun n => p.coeff n * powerKernelC n z u) := by
  have hfun :
      (fun w : ℂ => p.eval w)
        = (fun w : ℂ =>
            Finset.sum (Finset.range (p.natDegree + 1))
              (fun n => p.coeff n * w ^ n)) := by
    funext w
    calc
      p.eval w
          = (Finset.sum (Finset.range (p.natDegree + 1))
              (fun n => Polynomial.C (p.coeff n) * Polynomial.X ^ n)).eval w := by
              exact congrArg (fun q : Polynomial ℂ => q.eval w) p.as_sum_range_C_mul_X_pow
      _ = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => (Polynomial.C (p.coeff n) * Polynomial.X ^ n).eval w) := by
            rw [Polynomial.eval_finset_sum]
      _ = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => p.coeff n * w ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp
  rw [hfun]
  rw [complexCosmicKernel_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa using
    (complexCosmicKernel_monomial_of_ne_zero (a := p.coeff n) (z := z) (u := u) (n := n) hu)

theorem complexCosmicKernel_polynomial_eval_eq_polynomialKernelExtC_of_ne_zero
    (p : Polynomial ℂ) (z u : ℂ) (hu : u ≠ 0) :
    complexCosmicKernel (fun w : ℂ => p.eval w) z u = polynomialKernelExtC p z u := by
  simpa [polynomialKernelExtC] using
    (complexCosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernelC_of_ne_zero p z u hu)

theorem derivative_eval_eq_sum_range_coeff_mul_powC
    (p : Polynomial ℂ) (z : ℂ) :
    p.derivative.eval z
      = Finset.sum (Finset.range (p.natDegree + 1))
          (fun n => p.coeff n * ((n : ℂ) * z ^ (n - 1))) := by
  rw [Polynomial.derivative_eval]
  simpa [mul_assoc] using
    (p.sum_over_range
      (f := fun n a => a * (n : ℂ) * z ^ (n - 1))
      (h := by intro n; simp))

theorem continuous_polynomialKernelExtC (p : Polynomial ℂ) (z : ℂ) :
    Continuous (fun u : ℂ => polynomialKernelExtC p z u) := by
  unfold polynomialKernelExtC
  refine continuous_finset_sum (s := Finset.range (p.natDegree + 1)) ?_
  intro n hn
  exact (continuous_const.mul (continuous_powerKernelC n z))

theorem polynomialKernelExtC_zero (p : Polynomial ℂ) (z : ℂ) :
    polynomialKernelExtC p z 0 = p.derivative.eval z := by
  unfold polynomialKernelExtC
  calc
    Finset.sum (Finset.range (p.natDegree + 1))
      (fun n => p.coeff n * powerKernelC n z 0)
        = Finset.sum (Finset.range (p.natDegree + 1))
            (fun n => p.coeff n * ((n : ℂ) * z ^ (n - 1))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [powerKernelC_zero]
    _ = p.derivative.eval z := by
      simpa using (derivative_eval_eq_sum_range_coeff_mul_powC p z).symm

theorem tendsto_polynomialKernelExtC_zero (p : Polynomial ℂ) (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => polynomialKernelExtC p z u)
      (nhds (0 : ℂ))
      (nhds (p.derivative.eval z)) := by
  simpa [polynomialKernelExtC_zero] using (continuous_polynomialKernelExtC p z).tendsto 0

theorem tendsto_polynomialKernelExtC_zero_punctured (p : Polynomial ℂ) (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => polynomialKernelExtC p z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
      (nhds (p.derivative.eval z)) :=
  (tendsto_polynomialKernelExtC_zero p z).mono_left nhdsWithin_le_nhds

theorem tendsto_complexCosmicKernel_polynomial_eval (p : Polynomial ℂ) (z : ℂ) :
    Filter.Tendsto (fun u : ℂ => complexCosmicKernel (fun w : ℂ => p.eval w) z u)
      (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
      (nhds (p.derivative.eval z)) := by
  have hExt :
      Filter.Tendsto (fun u : ℂ => polynomialKernelExtC p z u)
        (nhdsWithin (0 : ℂ) (Set.compl ({(0 : ℂ)} : Set ℂ)))
        (nhds (p.derivative.eval z)) :=
    tendsto_polynomialKernelExtC_zero_punctured p z
  refine tendsto_nhdsWithin_congr ?hEq hExt
  intro u hu
  have hu0 : u ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hu
  exact (complexCosmicKernel_polynomial_eval_eq_polynomialKernelExtC_of_ne_zero p z u hu0).symm

theorem hasDerivAt_polynomial_eval_complexCosmic (p : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => p.eval w) (p.derivative.eval z) z := by
  exact hasDerivAt_of_tendsto_complexCosmicKernel
    (tendsto_complexCosmicKernel_polynomial_eval p z)
```

### この段の意味

ここで

\[
\texttt{polynomialKernelExtC } p \, z \, u
\]

は、\(u=0\) に穴がある差分商を、中心で埋めた **正則化された局所生成核** になっている。

これにより、

- punctured neighborhood では元の差分核と一致し
- 中心では導関数値に一致し
- 全体として連続に閉じる

という「可除特異点」型の構造が明確になる。

---

## 9. 第6段. 宇宙式への複素橋

平方宇宙式の複素版は、本質的には同じ形で立つ。

```lean
import Mathlib
import DkMath.CosmicFormula.CosmicDifferenceKernelComplex
import DkMath.CosmicFormula.CosmicHolomorphicPowerLimit
import DkMath.CosmicFormula.CosmicFormulaBasic

#print "file: DkMath.CosmicFormula.CosmicFormulaDerivativeBridgeComplex"

namespace DkMath.CosmicFormula

theorem cdelta_pow_two_eq_u_mul_powerKernelC_two (z u : ℂ) :
    cdelta (fun w : ℂ => w ^ 2) z u = u * powerKernelC 2 z u := by
  simpa [cdelta] using (sub_pow_eq_u_mul_powerKernelC 2 z u)

theorem complex_cosmic_formula_unit_eq_cdelta_pow_two_sub_two_mul (z u : ℂ) :
    ((z + u) ^ 2 - z * (z + 2 * u))
      = cdelta (fun w : ℂ => w ^ 2) z u - 2 * z * u := by
  simp [cdelta]
  ring

theorem complex_cosmic_formula_unit_eq_u_mul_powerKernelC_two_gap (z u : ℂ) :
    ((z + u) ^ 2 - z * (z + 2 * u))
      = u * (powerKernelC 2 z u - 2 * z) := by
  rw [complex_cosmic_formula_unit_eq_cdelta_pow_two_sub_two_mul, cdelta_pow_two_eq_u_mul_powerKernelC_two]
  ring

theorem complex_cosmic_formula_unit_eq_u_sq (z u : ℂ) :
    ((z + u) ^ 2 - z * (z + 2 * u)) = u ^ 2 := by
  ring
```

ここで見えるのは、複素でもなお

\[
(z+u)^2 - z(z+2u) = u^2
\]

が崩れず、差分核と宇宙式 gap が同じ骨格を持つことである。

---

## 10. ここまでで得られる数学的意味

この複素版形式化によって、まず次が得られる。

## 10.1. 複素微分の kernel 定式化

\[
\text{HasDerivAt } f \, L \, z
\iff
\lim_{u \to 0,\;u\neq 0} \frac{f(z+u)-f(z)}{u} = L
\]

を DkMath の cosmic kernel 言語で固定できる。

## 10.2. 冪関数・多項式の局所生成核

差分は偶然に導関数へ落ちるのではなく、最初から

\[
(z+u)^d - z^d = u \, P_d(z,u)
\]

として **生成核 \(P_d\) を内蔵している** 。

## 10.3. 可除特異点型 extension の原型

`polynomialKernelExtC` は、解析接続の全面実装ではないが、少なくとも

> punctured kernel を中心で埋めて閉じる

という可除特異点の最初の形式になる。

---

## 11. 次段の拡張計画

ここから先に、複素解析らしい話が始まる。

## 11.1. `AnalyticAt` への橋

次のファイル候補を置ける。

```text
lean/dk_math/DkMath/CosmicFormula/CosmicAnalyticKernel.lean
```

狙いは次。

- `powerKernelC d z` が \(u\) の entire function である
- `polynomialKernelExtC p z` が \(u\) に関して analytic
- `complexCosmicKernel` が punctured neighborhood で analytic であり、ext により中心で埋まる

欲しい定理の型は例えばこうじゃ。

```lean
/--
`powerKernelC d z` is entire as a function of `u`.
-/
theorem analyticAt_powerKernelC (d : ℕ) (z u₀ : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => powerKernelC d z u) u₀ := by
  -- polynomial in `u`
  sorry
```

## 11.2. 可除特異点の一般定理へ

次は「多項式でなく一般の punctured kernel」が対象になる。

例えば、

```lean
/--
Prototype removable-singularity theorem in cosmic-kernel style.
-/
theorem exists_analytic_extension_of_complexCosmicKernel
    {f : ℂ → ℂ} {z : ℂ}
    (hpunct : AnalyticOnNhd ℂ (fun u : ℂ => complexCosmicKernel f z u) ({0}ᶜ))
    (hbd    : LocallyBoundedAround 0 (fun u : ℂ => complexCosmicKernel f z u)) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
      EqOn g (fun u => complexCosmicKernel f z u) ({0}ᶜ) := by
  sorry
```

ここはすぐには閉じなくてよい。
まずは多項式・冪・有理型の具体例から入るのがよい。

## 11.3. KUS support との接続

最後に、複素 \(u\) の support を

- 大きさ \(|u|\)
- 偏角 \(\arg u\)
- 枝番号
- 周回回数

まで含む blueprint に持ち上げる。

すると、差分核は単なる複素数値ではなく、

> **support を保持した局所生成観測量**

として扱える。

ここで初めて、モノドロミーや branch cut を KUS 的に記述する道が開く。

---

## 12. 実装優先順

おすすめの実装順は次の通り。

## 12.1. すぐ書くべき 3 本

1. `CosmicDifferenceKernelComplex.lean`
2. `CosmicHolomorphicBasic.lean`
3. `CosmicHolomorphicPower.lean`

ここは実数版の複素化なので、比較的安全に進む。

## 12.2. 次に書く 2 本

4. `CosmicHolomorphicPowerLimit.lean`
5. `CosmicHolomorphicPolynomial.lean`

ここで `powerKernelC_zero` と `polynomialKernelExtC_zero` が要点になる。

## 12.3. その後

6. `CosmicFormulaDerivativeBridgeComplex.lean`
7. `CosmicAnalyticKernel.lean`（将来）

---

## 13. 注意点

## 13.1. `hasDerivAt_iff_tendsto_slope_zero` の一般性

上のコードは、mathlib 現行版で `ℂ → ℂ` に対してそのまま使える前提で書いている。
もしインスタンス解決で詰まる場合は、`HasDerivAt` の一般形から specialized lemma を噛ませればよい。

## 13.2. `CosmicFormulaBinom.GN` の係数体

`GN` が `R := ℂ` で使えるよう、係数体の抽象化が十分に一般であることを確認する。
もし `ℝ` 固定なら、先に `CosmicFormulaBinom` を半環一般へ引き上げる必要がある。

## 13.3. `Polynomial` の theorem 名

`Polynomial.hasDerivAt`, `Polynomial.derivative_eval`, `as_sum_range_C_mul_X_pow`, `sum_over_range` は、版によって細部が揺れることがある。
そこだけは実際のビルドで合わせる。

---

## 14. 一言でいうと

今回の複素版形式化の核心はこれじゃ。

> **解析接続をいきなり証明するのではなく、まず複素差分核を exact に定義し、その kernel の内部に埋め込まれている局所生成則を露出する。**

その上で、

\[
\text{差分核} \to \text{複素微分} \to \text{可除特異点型 extension} \to \text{解析接続}
\]

と進めるのがよい。

これなら、宇宙式の **Core / Beam / Gap** の見方も失われぬ。

- Core = 局所生成核
- Beam = 近傍へ伸びる展開則
- Gap = punctured center, 分岐, 特異

この三つを保ったまま、複素解析側へ橋を架けられるからじゃ。

---

## 15. 最短の着手用メモ

本当に最短で行くなら、まずこの 3 補題を通せばよい。

```lean
theorem hasDerivAt_iff_tendsto_complexCosmicKernel ...
theorem sub_pow_eq_u_mul_powerKernelC ...
theorem hasDerivAt_pow_complexCosmic ...
```

ここが通れば、あとは多項式拡張は実数版の写しでかなり押し切れる。
