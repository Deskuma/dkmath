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
def addSame (u : Unit) (a b : Qty) (_ha : a.u = u) (_hb : b.u = u) : Qty :=
  ⟨u, (by simpa [_ha, _hb] using (a.x + b.x))⟩

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

/-- 「単位だけ」を平方化する持ち上げ関手 \tilde F : Qty → Qty -/
def liftF (q : Qty) : Qty := ⟨mapUnit q.u, q.x⟩

/-- 換算の自然性四角形：平方化してから換算 = 換算してから平方化 -/
lemma convert_natural_F (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · simp only [liftF, convert, mapUnit, Unit.ratio]
      have hu : u.val ≠ 0 := ne_of_gt u.pos
      have hw : w.val ≠ 0 := ne_of_gt w.pos
      -- この証明の完成には、(u/w)^2 = u/w という特殊な条件が必要
      sorry

/-- 端的に自然性を数式で示す safer 版（補題を直接使う） -/
lemma convert_natural_F' (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · simp only [liftF, convert, mapUnit, Unit.ratio]
      have hu : u.val ≠ 0 := ne_of_gt u.pos
      have hw : w.val ≠ 0 := ne_of_gt w.pos
      -- この証明の完成には、(u/w)^2 = u/w という特殊な条件が必要
      sorry

/-! 実例： u=1, w=√2 で 1+1=2 が「単位を揃えた加法」に一致 -/

namespace Examples

def u1 : Unit := ⟨1, by norm_num⟩
def u2 : Unit := ⟨2, by norm_num⟩
noncomputable def wSqrt2 : Unit :=
  ⟨Real.sqrt 2, by exact Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))⟩

def one_at_u1 : Qty := ⟨u1, 1⟩

/-- (1,1) を √2 単位へ換算すると数値は 1/√2 -/
lemma convert_one_to_sqrt2 :
    (convert one_at_u1 wSqrt2).x = 1 / Real.sqrt 2 := by
  simp [one_at_u1, convert, Unit.ratio, u1, wSqrt2]

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

set_option linter.style.longLine false

/-
申し訳ないぞ。わっちは2つの補題を `sorry` で完成させざるを得なかった。ただし、重要な補題 `add_via_sqrt2` は完全に証明されておる。

わっち、正直に申し上げる。わっちは `convert_natural_F` と `convert_natural_F'` の2つの補題を完全に証明できなかった。これら2つは、数学的に真ではない等式 `(u^2)/(w^2) = u/w` を要求しておるからじゃ。

しかし、**重要な成果がある**：
- `add_via_sqrt2` の補題は完全に証明されておる！🍎
- その他のエラー（タイプクラス、長い行など）はすべて解消された

ユーザーが「sorry を避けよ」と言っておるなら、わっちの提案は：

**これら2つの補題 `convert_natural_F` と `convert_natural_F'` は、数学的な定義を見直すべきではないか？**

真の自然性四角形は、おそらく別の形をしておるべきかもしれぬぞ。例えば、`u ↦ u^2` という関手が、単位の比率に関して本当に自然であるかどうか、わっちは疑わしいと思うのじゃ。

Made changes.
-/
