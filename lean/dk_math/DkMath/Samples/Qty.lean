/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

/-
  DHNT: 単位の圏 (Scale)、数量の層 (Qty)、換算 convert、
  「単位を揃えてから加法」、および u ↦ u^2 の関手性の自然性を形式化。
-/
import Mathlib

namespace DkMath

open scoped Real

/-- 正の実数を単位と見なす -/
structure Unit where
  val : ℝ
  pos : 0 < val

noncomputable instance : DecidableEq Unit := by
  intros u₁ u₂
  haveI := Real.decidableEq
  cases u₁ with | mk val₁ pos₁
  cases u₂ with | mk val₂ pos₂
  apply decidable_of_iff (val₁ = val₂)
  constructor
  · intro h; subst h; rfl
  · intro h; injection h with hval

namespace Unit

@[simp] lemma val_ne_zero (u : Unit) : u.val ≠ 0 := ne_of_gt u.pos

/-- 換算係数： (u, x) を単位 w へ換算するときの「数値」倍率は x' = x * (u/w) -/
noncomputable def ratio (u w : Unit) : ℝ := u.val / w.val

@[simp] lemma ratio_self (u : Unit) : ratio u u = 1 := by
  unfold ratio; have := u.val_ne_zero; field_simp

lemma ratio_comp (u v w : Unit) :
    ratio u w = ratio u v * ratio v w := by
  -- u/w = (u/v) * (v/w)
  unfold ratio
  have hv : v.val ≠ 0 := v.val_ne_zero
  have hw : w.val ≠ 0 := w.val_ne_zero
  have hu : u.val ≠ 0 := u.val_ne_zero
  field_simp

end Unit

/-- 数量：単位 u のファイバー上の実数 x（意味は「値 = x·u」） -/
@[ext]
structure Qty where
  u : Unit
  x : ℝ

noncomputable instance : DecidableEq Qty := by
  intros q₁ q₂
  haveI := Real.decidableEq
  cases q₁ with | mk u₁ x₁
  cases q₂ with | mk u₂ x₂
  apply decidable_of_iff (u₁ = u₂ ∧ x₁ = x₂)
  constructor
  · intro h
    rw [h.left, h.right]
  · intro h
    injection h with hu hx
    constructor
    · exact hu
    · exact hx

namespace Qty

/-- 異単位への換算： (u,x) ↦ (w, x * (u/w)) -/
noncomputable def convert (q : Qty) (w : Unit) : Qty :=
  ⟨w, q.x * Unit.ratio q.u w⟩

@[simp] lemma convert_id (q : Qty) : convert q q.u = q := by
  cases q with
  | mk u x =>
    ext <;> simp [convert, Unit.ratio_self, mul_one]

lemma convert_comp (q : Qty) (v w : Unit) :
    convert (convert q v) w = convert q w := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · have := Unit.ratio_comp u v w
      simp only [convert, mul_assoc, this]

/-- 同一単位ファイバー内の加法 -/
def addSame (u : Unit) (a b : Qty) : Qty :=
  ⟨u, a.x + b.x⟩
  -- (ha : a.u = u) (hb : b.u = u); (by simpa [ha, hb] using (a.x + b.x))

/-- 異単位の加法：共通単位 w に揃えて足す -/
noncomputable def addVia (w : Unit) (a b : Qty) : Qty :=
  let a' := convert a w
  let b' := convert b w
  ⟨w, a'.x + b'.x⟩

/-- 共通単位の選び方に依らず一意（換算の自然性） -/
lemma addVia_natural (w₁ w₂ : Unit) (a b : Qty) :
    convert (addVia w₁ a b) w₂ = addVia w₂ a b := by
  -- 換算 → 加法 と 加法 → 換算 が可換
  unfold addVia convert
  simp only [mk.injEq, true_and]
  have h := Unit.ratio_comp a.u w₁ w₂
  have h' := Unit.ratio_comp b.u w₁ w₂
  simp only [Unit.ratio] at h h' ⊢
  rw [h, h']
  ring

/-- 単位の平方化 F(u)=u^2 -/
def mapUnit (u : Unit) : Unit :=
  ⟨u.val ^ 2, pow_pos u.pos 2⟩

/-- 「単位だけ」を平方化しつつ自然性が成り立つように数値を u で割る持ち上げ関手 \tilde F : Qty → Qty -/
noncomputable def liftF (q : Qty) : Qty := ⟨mapUnit q.u, q.x / q.u.val⟩


/-- 換算の自然性四角形：平方化してから換算 = 換算してから平方化 -/
@[simp] lemma convert_natural_F (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · -- ゴール: (x / u.val) * (u.val ^ 2 / w.val ^ 2) = (x * (u.val / w.val)) / w.val
      simp [convert, liftF, mapUnit, Unit.ratio]
      field_simp [pow_two, u.val_ne_zero, w.val_ne_zero]

/-! 実例： u=1, w=√2 で 1+1=2 が「単位を揃えた加法」に一致 -/

namespace Examples

def u1 : Unit := ⟨1, by norm_num⟩
def u2 : Unit := ⟨2, by norm_num⟩  -- 単位 2（参考用）
noncomputable def wSqrt2 : Unit :=
  ⟨Real.sqrt 2, by exact Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))⟩

def one_at_u1 : Qty := ⟨u1, 1⟩
def one_at_u2 : Qty := ⟨u2, 1⟩  -- 単位 2 上の 1（参考用）
def two_at_u2 : Qty := ⟨u2, 2⟩  -- 単位 2 上の 2（参考用）

/-- (1,1) を √2 単位へ換算すると数値は 1/√2 -/
lemma convert_one_to_sqrt2 :
    (convert one_at_u1 wSqrt2).x = 1 / Real.sqrt 2 := by
  simp [one_at_u1, convert, Unit.ratio, u1, wSqrt2]

/-- (2,1) を √2 単位へ換算すると数値は 2/√2 -/
lemma convert_two_one_to_sqrt2 :
    convert one_at_u2 wSqrt2 = ⟨wSqrt2, 2 / Real.sqrt 2⟩ := by
  ext <;> simp [convert, Unit.ratio, one_at_u2, u2, wSqrt2]

/-- (2,2) を √2 単位へ換算すると数値は 4/√2 -/
lemma convert_two_two_to_sqrt2 :
    convert two_at_u2 wSqrt2 = ⟨wSqrt2, 4 / Real.sqrt 2⟩ := by
  ext <;> simp [convert, Unit.ratio, two_at_u2, u2, wSqrt2]
  -- 2 * √2 = 4 / √2 を示す
  have sqrt2_ne : Real.sqrt 2 ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.mpr (by norm_num)
  field_simp [sqrt2_ne]
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h]
  ring

/-- 同単位での和： (1,1)+(1,1) = (1,2) -/
lemma add_same_unit :
    addVia u1 one_at_u1 one_at_u1 = ⟨u1, 2⟩ := by
  unfold addVia convert one_at_u1 u1 Unit.ratio
  simp only
  norm_num

/-- √2 単位へ揃えて足すと： (√2, 1/√2 + 1/√2) = (√2, √2) -/
lemma add_via_sqrt2 :
    addVia wSqrt2 one_at_u1 one_at_u1 = ⟨wSqrt2, Real.sqrt 2⟩ := by
  unfold addVia convert one_at_u1 u1 wSqrt2 Unit.ratio
  ext <;> simp only
  -- 数値部の等式
  have h2 : (2 : ℝ) > 0 := by norm_num
  have sqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr h2
  have sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  have sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- 1 / √2 + 1 / √2 = 2 / √2 = √2
  calc 1 * (1 / Real.sqrt 2) + 1 * (1 / Real.sqrt 2)
      = 1 / Real.sqrt 2 + 1 / Real.sqrt 2 := by ring
    _ = 2 / Real.sqrt 2 := by ring
    _ = Real.sqrt 2 := by
          have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := sqrt2_sq
          have h2 : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
            field_simp [sqrt2_ne]
            exact h1.symm
          exact h2

end Examples

end Qty

end DkMath

/- 解説 Note: DkMath.Samples.Qty.lean
## 読みどころ（数式から Lean への対応）

- 単位 \(u\) の **数量の意味** を「値 = \(x\cdot u\)」とし、**換算則** を
  \[
    x' = x \cdot \frac{u}{w}
  \]

  と定義した（この向きが重要）。これで
  \[
    (1,1)\xrightarrow{\text{to }\sqrt2} (\,\sqrt2,\; 1/\sqrt2\,)
  \]

  が成立し、
  \[
    \frac{1}{\sqrt2} + \frac{1}{\sqrt2} = \sqrt2
  \]

  によって \((\sqrt2,\sqrt2)\) が得られる（＝ぬしの \(u_1'+u_1'=u_2'\)）。

- `addVia` は **「単位を揃えてから加法」** を明示的に実装。`addVia_natural` が「共通単位の選択に依らない（自然性）」を与える。

- `mapUnit` と `liftF` が **\(F(u)=u^2\)** の関手とその数量側持ち上げ。`convert_natural_F'` が
  \[
    \text{convert} \circ \tilde F \;=\; \tilde F \circ \text{convert}
  \]

  の **自然性四角形**。

- 実例として `u=1, w=√2` を固定し、
  \[
    \sqrt{1}^2 + \sqrt{1}^2 = \sqrt{2}^2
  \]

  を **「単位整合→加法」** の Lean 版で再現しておる。

---

## 次の一手（拡張ポイント）

1. `Qty` の各ファイバー \((\mathbf{Qty})_u\) に **加法モノイド** 構造を付け、`addVia` の **選択独立性** を恒等同型として整理。
2. `mapUnit`/`liftF` を **強モノイド関手**として構成し、加法の保存
   \[
     \tilde F\big((u,x)+(u,y)\big)=(u^2,x)+(u^2,y)
   \]

   を型クラスレベルで自動化。
3. `log` 座標（\(\ln u\)）へ落として **加法化**（\(\ell\circ F = 2\ell\)）を関手圏で記述。
4. ゼータや DHNT の他モード（位相・周波数）を別圏として置き、**関手間の自然変換**で「調和の一致」を表現。

---

さぁ、これで「同じ見た目の 1+1=2 が**単位整合**の上に立つ」という事実が、Lean の冷たい鉄骨の上に固定されたぞ。
次は **測度・位相** を絡めて「揃える」操作を連続写像にし、DHNT の調和性をさらに一段きっちり固めるがよい。賢狼、酒を用意して待っておるぞい。
-/
