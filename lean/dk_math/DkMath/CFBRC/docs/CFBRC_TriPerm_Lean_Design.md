# CFBRC の三角置換の Lean 実装設計

> 🐺賢狼

**Lean 実装設計** として、まず **(d=2) の橋を完全に固定** してから、一般 (d) へ広げる流れじゃ。

## 1. 目的

今回 Lean で固定したい中核は、次の橋じゃ。

\[
(a'+x)^2-x^2=
a'(a'+2x)=
a^2\cos^2\phi=
\Re G_2(a\cos\phi, a\sin\phi)
\]

ただし

\[
a' = a-x,\qquad x=a\sin\phi,
\qquad
G_d(X,\Theta)=(X+i\Theta)^d-(i\Theta)^d
\]

である。

これを Lean では、次の **3 層構造** で実装するのが最も綺麗じゃ。

* **代数層** ：冪の差の因数分解と Body
* **三角層** ：\(x=a\sin\phi\) による Body の位相化
* **複素層** ：CFBRC の実部としての Body

---

## 2. 推奨ファイル構成

わっちの推奨配置はこれじゃ。

```text
DkMath/
  CFBRC/
    TrigBridge/
      Basic.lean
      Trig.lean
      Complex.lean
      Main.lean
```

### 2A. `Basic.lean`

* `body2` の定義
* 因数分解補題
* `a' = a - x` の潰し込み補題

### 2B. `Trig.lean`

* `x = a * sin φ` による変換
* `body2 = a^2 * cos^2 φ` の補題

### 2C. `Complex.lean`

* `cfbrc` の定義
* `d=2` の展開
* `Complex.re` が `X^2` になる補題
* 極座標代入補題

### 2D. `Main.lean`

* 全橋を結ぶ最終定理
* 将来の一般 \(d\) 用の入口定理

もし RH 側に寄せたいなら `DkMath.RH.CFBRC.TrigBridge.*` でもよいが、
今回の橋は **RH 専用ではなく、代数・三角・複素の一般橋** じゃから、独立配置のほうが後々美しい。

---

## 3. 実装方針

重要なのは、**最初から全部を \(\mathbb{R}\) や \(\mathbb{C}\) にしない** ことじゃ。

### 3A. 代数層

`CommRing` 上で一般化して証明する。

### 3B. 三角層

\(\mathbb{R}\) に降ろして `Real.sin_sq_add_cos_sq` を使う。

### 3C. 複素層

\(\mathbb{R}\) を \(\mathbb{C}\) に埋め込んで `Complex.re` を取る。

この分離をしておくと、証明の大半は `ring`、`nlinarith`、`simp` で通る。

---

## 4. 中核定義

まずは `Basic.lean` の核じゃ。

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace DkMath
namespace CFBRC
namespace TrigBridge

/-- Quadratic Body: `(a' + x)^2 - x^2`. -/
def body2 {α : Type*} [Ring α] (ap x : α) : α :=
  (ap + x)^2 - x^2

/-- CFBRC core polynomial. -/
def cfbrc (d : ℕ) (X Θ : ℂ) : ℂ :=
  (X + Complex.I * Θ)^d - (Complex.I * Θ)^d

/-- Real-input version of `cfbrc`, coerced into `ℂ`. -/
def cfbrcℝ (d : ℕ) (X Θ : ℝ) : ℂ :=
  cfbrc d X Θ

end TrigBridge
end CFBRC
end DkMath
```

---

## 5. 代数層 `Basic.lean`

まず Body の純代数補題を固定する。

```lean
namespace DkMath
namespace CFBRC
namespace TrigBridge

lemma body2_factor {α : Type*} [CommRing α] (ap x : α) :
    body2 ap x = ap * (ap + 2 * x) := by
  simp [body2, pow_two]
  ring

lemma body2_sub {α : Type*} [CommRing α] (a x : α) :
    body2 (a - x) x = a^2 - x^2 := by
  simp [body2, pow_two]
  ring

lemma body2_sub_factor {α : Type*} [CommRing α] (a x : α) :
    body2 (a - x) x = (a - x) * ((a - x) + 2 * x) := by
  rw [body2_factor]

end TrigBridge
end CFBRC
end DkMath
```

ここでのポイントは、

\[
(a'+x)^2-x^2=a'(a'+2x)
\]

と

\[
(a-x+x)^2-x^2=a^2-x^2
\]

を **別補題として分ける** ことじゃ。
両者は意味が違う。

* `body2_factor` は **Body 生成**
* `body2_sub` は **Body の再表示**
* `body2_sub_factor` は **両者の接続点**

---

## 6. 三角層 `Trig.lean`

次に

\[
x=a\sin\phi
\]

を入れて Body を `cos^2` に落とす。

```lean
import DkMath.CFBRC.TrigBridge.Basic

noncomputable section

namespace DkMath
namespace CFBRC
namespace TrigBridge

lemma sq_sub_sin_eq_cos (a φ : ℝ) :
    a^2 - (a * Real.sin φ)^2 = a^2 * (Real.cos φ)^2 := by
  nlinarith [Real.sin_sq_add_cos_sq φ]

lemma body2_trig (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = a^2 * (Real.cos φ)^2 := by
  calc
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
        = a^2 - (a * Real.sin φ)^2 := by
            simp [body2, pow_two]
            ring
    _ = a^2 * (Real.cos φ)^2 := by
            exact sq_sub_sin_eq_cos a φ

lemma body2_factor_trig (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = a^2 * (Real.cos φ)^2 := by
  calc
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
        = body2 (a * (1 - Real.sin φ)) (a * Real.sin φ) := by
            symm
            exact body2_factor _ _
    _ = a^2 * (Real.cos φ)^2 := by
            exact body2_trig a φ

end TrigBridge
end CFBRC
end DkMath
```

この層の核は

\[
a'(a'+2x)=a^2\cos^2\phi
\]

を三角恒等式へ落とすところじゃ。
`nlinarith [Real.sin_sq_add_cos_sq φ]` がとても効く。

---

## 7. 複素層 `Complex.lean`

次に CFBRC の (d=2) 実部を固定する。

```lean
import DkMath.CFBRC.TrigBridge.Basic

noncomputable section

namespace DkMath
namespace CFBRC
namespace TrigBridge

lemma cfbrc_two_re (X Θ : ℝ) :
    Complex.re (cfbrcℝ 2 X Θ) = X^2 := by
  simp [cfbrcℝ, cfbrc, pow_two]
  ring

lemma cfbrc_two_im (X Θ : ℝ) :
    Complex.im (cfbrcℝ 2 X Θ) = 2 * X * Θ := by
  simp [cfbrcℝ, cfbrc, pow_two]
  ring

lemma cfbrc_two_re_polar (a φ : ℝ) :
    Complex.re (cfbrcℝ 2 (a * Real.cos φ) (a * Real.sin φ))
      = a^2 * (Real.cos φ)^2 := by
  rw [cfbrc_two_re]
  ring

lemma cfbrc_two_im_polar (a φ : ℝ) :
    Complex.im (cfbrcℝ 2 (a * Real.cos φ) (a * Real.sin φ))
      = 2 * a^2 * Real.sin φ * Real.cos φ := by
  rw [cfbrc_two_im]
  ring

end TrigBridge
end CFBRC
end DkMath
```

ここで本質は

\[
G_2(X,\Theta)=(X+i\Theta)^2-(i\Theta)^2=X^2+2iX\Theta
\]

ゆえに

\[
\Re G_2(X,\Theta)=X^2
\]

となる点じゃ。
そして極座標的代入

\[
X=a\cos\phi,\qquad \Theta=a\sin\phi
\]

により

\[
\Re G_2(a\cos\phi,a\sin\phi)=a^2\cos^2\phi
\]

を得る。

---

## 8. 最終橋 `Main.lean`

最後に三層を連結して、欲しかった橋の主定理にする。

```lean
import DkMath.CFBRC.TrigBridge.Trig
import DkMath.CFBRC.TrigBridge.Complex

noncomputable section

namespace DkMath
namespace CFBRC
namespace TrigBridge

theorem body2_eq_re_cfbrc2 (a φ : ℝ) :
    body2 (a * (1 - Real.sin φ)) (a * Real.sin φ)
      = Complex.re (cfbrcℝ 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_trig, cfbrc_two_re_polar]

theorem factor_eq_re_cfbrc2 (a φ : ℝ) :
    (a * (1 - Real.sin φ)) * ((a * (1 - Real.sin φ)) + 2 * (a * Real.sin φ))
      = Complex.re (cfbrcℝ 2 (a * Real.cos φ) (a * Real.sin φ)) := by
  rw [body2_factor_trig, cfbrc_two_re_polar]

end TrigBridge
end CFBRC
end DkMath
```

この `factor_eq_re_cfbrc2` が、ぬしの今回の主張をほぼそのまま Lean 化した姿じゃな。

すなわち

\[
(a'+x)^2-x^2=a'(a'+2x)=a^2\cos^2\phi=\Re G_2(a\cos\phi,a\sin\phi)
\]

の **二次橋の定理** じゃ。

---

## 9. 命名の推奨

定理名は意味が見えるように、次の規則を勧めるぞ。

### 9A. 代数

* `body2_factor`
* `body2_sub`
* `body2_sub_factor`

### 9B. 三角

* `sq_sub_sin_eq_cos`
* `body2_trig`
* `body2_factor_trig`

### 9C. 複素

* `cfbrc_two_re`
* `cfbrc_two_im`
* `cfbrc_two_re_polar`
* `cfbrc_two_im_polar`

### 9D. 主定理

* `body2_eq_re_cfbrc2`
* `factor_eq_re_cfbrc2`

見ただけで層が解るようになる。

---

## 10. 証明戦術の使い分け

ここは実務的に大事じゃ。

### 10A. `ring`

純代数の展開・整理はほぼこれでよい。

### 10B. `simp [body2, cfbrc, pow_two]`

定義展開と二乗展開。

### 10C. `nlinarith [Real.sin_sq_add_cos_sq φ]`

\[
a^2-(a\sin\phi)^2=a^2\cos^2\phi
\]
の決着。

### 10D. `rw`

層をまたぐ橋は、計算より `rw` の鎖のほうが読みやすい。

---

## 11. 一段先の一般化設計

(d=2) を固定した後は、こう広げるのが筋じゃ。

### 11A. 一般 (d) CFBRC

```lean
lemma cfbrc_expand (d : ℕ) (X Θ : ℂ) :
    cfbrc d X Θ
      = ∑ k in Finset.Icc 1 d,
          (Nat.choose d k : ℂ) * X^k * (Complex.I * Θ)^(d-k) := by
  -- binomial theorem route
  sorry
```

### 11B. 実部抽出

`Complex.re (cfbrc d X Θ)` の一般式を作る。

### 11C. 二次は特殊に綺麗

(d=2) だけは `cos²` が直接出る。
ここを **特殊ブリッジ定理** として固定しておく。

つまり一般化の順は

\[
d=2 \text{ を完成}
\;\to\;
CFBRC 一般展開
\;\to\;
実部・虚部の高調波構造
\]

がよい。

---

## 12. 実装優先順位

わっちなら次の順でコミットする。

### 12A. 第1コミット

`Basic.lean`

* 定義
* `body2_factor`
* `body2_sub`

### 12B. 第2コミット

`Trig.lean`

* `sq_sub_sin_eq_cos`
* `body2_trig`
* `body2_factor_trig`

### 12C. 第3コミット

`Complex.lean`

* `cfbrc`
* `cfbrc_two_re`
* `cfbrc_two_im`
* 極座標代入補題

### 12D. 第4コミット

`Main.lean`

* `body2_eq_re_cfbrc2`
* `factor_eq_re_cfbrc2`

この順なら、途中で止まっても成果が明確に残る。

---

## 13. 最終的な Lean 設計の一言要約

今回 Lean で固定すべき核心は、これじゃ。

\[
\boxed{
\text{二次 Body は、三角置換により } a^2\cos^2\phi \text{ へ写り、同時に CFBRC } G_2 \text{ の実部でもある}
}
\]

つまり Lean 上では、

* **冪差 Body**
* **三角位相 Body**
* **CFBRC 実部 Body**

の 3 つを別補題で固定し、最後に 1 本へ束ねる。
これが最も堅く、美しい実装設計じゃ。
