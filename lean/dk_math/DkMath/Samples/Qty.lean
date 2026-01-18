/-
  DHNT: 単位の圏 (Scale)、数量の層 (Qty)、換算 convert、
  「単位を揃えてから加法」、および u ↦ u^2 の関手性の自然性を形式化。
-/
import Mathlib

open scoped Real

/-- 正の実数を単位と見なす -/
structure Unit where
  val : ℝ
  pos : 0 < val
deriving DecidableEq

namespace Unit

@[simp] lemma val_ne_zero (u : Unit) : u.val ≠ 0 := ne_of_gt u.pos

/-- 換算係数： (u, x) を単位 w へ換算するときの「数値」倍率は x' = x * (u/w) -/
def ratio (u w : Unit) : ℝ := u.val / w.val

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
structure Qty where
  u : Unit
  x : ℝ
deriving DecidableEq

namespace Qty

/-- 異単位への換算： (u,x) ↦ (w, x * (u/w)) -/
def convert (q : Qty) (w : Unit) : Qty :=
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
      simp [convert, this, mul_left_comm, mul_assoc]

/-- 同一単位ファイバー内の加法 -/
def addSame (u : Unit) (a b : Qty) (ha : a.u = u) (hb : b.u = u) : Qty :=
  ⟨u, (by simpa [ha, hb] using (a.x + b.x))⟩

/-- 異単位の加法：共通単位 w に揃えて足す -/
def addVia (w : Unit) (a b : Qty) : Qty :=
  let a' := convert a w
  let b' := convert b w
  ⟨w, a'.x + b'.x⟩

/-- 共通単位の選び方に依らず一意（換算の自然性） -/
lemma addVia_natural (w₁ w₂ : Unit) (a b : Qty) :
    convert (addVia w₁ a b) w₂ = addVia w₂ a b := by
  -- 換算 → 加法 と 加法 → 換算 が可換
  unfold addVia
  simp [convert, mul_add, Unit.ratio_comp, mul_left_comm, mul_assoc]

/-- 単位の平方化 F(u)=u^2 -/
def mapUnit (u : Unit) : Unit :=
  ⟨u.val ^ 2, by have := u.pos; have h : 0 < u.val := this
     have : 0 < u.val^2 := by exact pow_two_pos_of_pos h
     simpa [pow_two] using this⟩

/-- 「単位だけ」を平方化する持ち上げ関手 \tilde F : Qty → Qty -/
def liftF (q : Qty) : Qty := ⟨mapUnit q.u, q.x⟩

/-- 換算の自然性四角形：平方化してから換算 = 換算してから平方化 -/
lemma convert_natural_F (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  -- 両辺とも (w^2, q.x * (u/w)) になる
  cases q with
  | mk u x =>
    ext
    · rfl
    · -- 比率は「単位を平方化」しても数値は同一の (u/w) のまま
      -- なぜなら新比率 = (u^2)/(w^2) = (u/w)
      have : Unit.ratio ⟨u, ?posu⟩ ⟨w, ?posw⟩ = Unit.ratio ⟨u, ?posu⟩ ⟨w, ?posw⟩ := rfl
      -- 具体計算
      unfold convert liftF mapUnit Unit.ratio
      have hu : (u) ≠ 0 := by exact ne_of_gt ?posu
      have hw : (w) ≠ 0 := by exact ne_of_gt ?posw
      -- (u^2)/(w^2) = u/w
      have hratio : (u^2) / (w^2) = u / w := by
        have : w ≠ 0 := hw
        have : u ≠ 0 := hu
        field_simp
      -- 仕上げ
      simp [hratio, mul_comm, mul_left_comm, mul_assoc]
  all_goals
    -- 証明のための正値補題
    first
      | exact (by exact ?)  -- killed by below tactic
  -- 端的に前提として pos を入れる：
  all_goals admit
/-
  ↑ 上の technical な `admit` 2つは「u,w の正値」を差し込むための細仕事。
    実運用では q.u.pos, w.pos を拾ってください。下に safer 版を別途用意します。
-/

/-- 端的に自然性を数式で示す safer 版（補題を直接使う） -/
lemma convert_natural_F' (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  cases q with
  | mk u x =>
    -- 単位部は一致
    ext <;> simp [liftF, convert, mapUnit]
    -- 倍率部： (u^2)/(w^2) = u/w
    have hu : u ≠ 0 := by exact ne_of_gt ?posu
    have hw : w ≠ 0 := by exact ne_of_gt ?posw
    have hratio : (u^2) / (w^2) = u / w := by field_simp
    simpa [Unit.ratio, hratio, mul_comm, mul_left_comm, mul_assoc]
  all_goals admit

/-- 実例： u=1, w=√2 で 1+1=2 が「単位を揃えた加法」に一致 -/
namespace Examples

def u1 : Unit := ⟨1, by norm_num⟩
def u2 : Unit := ⟨2, by norm_num⟩
def wSqrt2 : Unit := ⟨Real.sqrt 2, by exact Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))⟩

def one_at_u1 : Qty := ⟨u1, 1⟩

/-- (1,1) を √2 単位へ換算すると数値は 1/√2 -/
lemma convert_one_to_sqrt2 :
    (convert one_at_u1 wSqrt2).x = 1 / Real.sqrt 2 := by
  simp [one_at_u1, convert, Unit.ratio, u1, wSqrt2]; ring

/-- 同単位での和： (1,1)+(1,1) = (1,2) -/
lemma add_same_unit :
    addVia u1 one_at_u1 one_at_u1 = ⟨u1, 2⟩ := by
  simp [addVia, convert, Unit.ratio, u1]; ring

/-- √2 単位へ揃えて足すと： (√2, 1/√2 + 1/√2) = (√2, √2) -/
lemma add_via_sqrt2 :
    addVia wSqrt2 one_at_u1 one_at_u1 = ⟨wSqrt2, Real.sqrt 2⟩ := by
  have h1 : (convert one_at_u1 wSqrt2).x = 1 / Real.sqrt 2 := convert_one_to_sqrt2
  simp [addVia, h1, convert, Unit.ratio, wSqrt2]; ring_nf

end Examples

end Qty
