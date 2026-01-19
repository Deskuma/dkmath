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

namespace DHNT

open scoped Real

/-- 正の実数を単位と見なす -/
@[ext] structure Unit where
  val : ℝ
  pos : 0 < val

@[simp] instance : Mul Unit where
  mul := fun u v => ⟨u.val * v.val, mul_pos u.pos v.pos⟩

@[simp] instance : One Unit where
  one := ⟨1, zero_lt_one⟩

@[simp] instance : MulOneClass Unit where
  mul := (· * ·)
  one := 1
  mul_one u := by
    ext
    simp only [instMulUnit]
    -- u.val * 1 = u.val
    exact mul_one u.val
  one_mul u := by
    ext
    simp only [instMulUnit]
    -- 1 * u.val = u.val
    exact one_mul u.val

namespace Unit

@[simp] lemma val_ne_zero (u : Unit) : u.val ≠ 0 := ne_of_gt u.pos

/-- 換算係数： (u, x) を単位 w へ換算するときの「数値」倍率は x' = x * (u/w) -/
noncomputable def ratio (u w : Unit) : ℝ := u.val / w.val

@[simp] lemma ratio_self (u : Unit) : ratio u u = 1 := by
  unfold ratio; have := u.val_ne_zero; field_simp

@[simp] lemma ratio_comp (u v w : Unit) :
    ratio u w = ratio u v * ratio v w := by
  -- u/w = (u/v) * (v/w)
  unfold ratio
  have hv : v.val ≠ 0 := v.val_ne_zero
  have hw : w.val ≠ 0 := w.val_ne_zero
  have hu : u.val ≠ 0 := u.val_ne_zero
  field_simp

end Unit

/-- 数量：単位 u のファイバー上の実数 x（意味は「値 = x·u」） -/
@[ext] structure Qty where
  u : Unit
  x : ℝ

namespace Qty

/-- 異単位への換算： (u,x) ↦ (w, x * (u/w)) -/
noncomputable def convert (q : Qty) (w : Unit) : Qty :=
  ⟨w, q.x * Unit.ratio q.u w⟩

@[simp] lemma convert_id (q : Qty) : convert q q.u = q := by
  cases q with
  | mk u x =>
    ext <;> simp [convert, Unit.ratio_self, mul_one]

@[simp] lemma convert_comp (q : Qty) (v w : Unit) :
    convert (convert q v) w = convert q w := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · have := Unit.ratio_comp u v w
      simp [convert, this, mul_assoc]

/-- 同一単位ファイバー内の加法 -/
def addSame (u : Unit) (a b : Qty) : Qty :=
  ⟨u, a.x + b.x⟩

/-- 異単位の加法：共通単位 w に揃えて足す -/
noncomputable def addVia (w : Unit) (a b : Qty) : Qty :=
  let a' := convert a w
  let b' := convert b w
  ⟨w, a'.x + b'.x⟩

/-- 共通単位の選び方に依らず一意（換算の自然性） -/
@[simp] lemma addVia_natural (w₁ w₂ : Unit) (a b : Qty) :
    convert (addVia w₁ a b) w₂ = addVia w₂ a b := by
  -- 換算 → 加法 と 加法 → 換算 が可換
  unfold addVia convert
  ext
  · rfl
  · -- ゴール:
    --  (a.x * a.u.ratio w₁ + b.x * b.u.ratio w₁) * w₁.ratio w₂
    -- = a.x * a.u.ratio w₂ + b.x * b.u.ratio w₂
    simp only [Unit.ratio]
    -- まず左辺を分配則で展開できる形に書き換える
    rw [add_mul]
    -- 各項ごとに分母をまとめる
    rw [mul_assoc, mul_assoc]
    -- 分数の積を分母でまとめる
    rw [←mul_div_assoc, ←mul_div_assoc]
    -- これで a.x * (a.u.val / w₂.val) + b.x * (b.u.val / w₂.val) となる
    field_simp

/-- 単位の平方化 F(u)=u^2 -/
def mapUnit (u : Unit) : Unit :=
  ⟨u.val ^ 2, by exact pow_pos u.pos 2⟩

/-- 「単位だけ」を平方化しつつ自然性が成り立つように数値を u で割る持ち上げ \tilde F : Qty → Qty -/
noncomputable def liftF (q : Qty) : Qty := ⟨mapUnit q.u, q.x / q.u.val⟩

/-- 換算の自然性四角形：平方化してから換算 = 換算してから平方化 -/
@[simp] lemma convert_natural_F (q : Qty) (w : Unit) :
    convert (liftF q) (mapUnit w) = liftF (convert q w) := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · -- ゴール: (x / u.val) * (u.val ^ 2 / w.val ^ 2) = x * (u.val / w.val) / w.val
      simp [liftF, convert, mapUnit, Unit.ratio]
      field_simp [pow_two, u.val_ne_zero, w.val_ne_zero]

/-- 無次元化（スケール不変量） -/
noncomputable def coordInUnit (q : Qty) : ℝ := q.x / q.u.val

@[simp] lemma coordInUnit_convert (q : Qty) (w : Unit) :
    coordInUnit (convert q w) = coordInUnit q * (q.u.val ^ 2 / w.val ^ 2) := by
  cases q with
  | mk u x =>
    simp [coordInUnit, convert, Unit.ratio]
    field_simp

/-- liftF は「単位を平方化し、数値は無次元化」に等しい -/
@[simp] lemma liftF_eq_coordInUnit (q : Qty) :
    liftF q = ⟨mapUnit q.u, coordInUnit q⟩ := rfl

/-- 換算しても不変な「実体値」：値 = x * u -/
noncomputable def absVal (q : Qty) : ℝ := q.x * q.u.val

@[simp] lemma absVal_convert (q : Qty) (w : Unit) :
    absVal (convert q w) = absVal q := by
  cases q with
  | mk u x =>
    -- (x * (u/w)) * w = x*u
    simp [absVal, convert, Unit.ratio]
    field_simp

noncomputable def dimless (u0 : Unit) (q : Qty) : ℝ :=
  (convert q u0).x

@[simp] lemma dimless_invariant (u0) (q : Qty) (w : Unit) :
  dimless u0 (convert q w) = dimless u0 q := by
  cases q with
  | mk u x =>
    simp [dimless, Qty.convert, Unit.ratio, mul_assoc]
    -- ゴール: x * (u.val / w.val) * (w.val / u0.val) = x * (u.val / u0.val)
    field_simp [u.val_ne_zero, w.val_ne_zero, u0.val_ne_zero]
    ring_nf
    tauto

/- 実例： u=1, w=√2 で 1+1=2 が「単位を揃えた加法」に一致 -/
namespace Examples

def u1 : Unit := ⟨1, by norm_num⟩
def u2 : Unit := ⟨2, by norm_num⟩
noncomputable def wSqrt2 : Unit :=
  ⟨Real.sqrt 2, by exact Real.sqrt_pos.mpr (by norm_num : 0 < (2:ℝ))⟩

def one_at_u1 : Qty := ⟨u1, 1⟩

/-- (1,1) を √2 単位へ換算すると数値は 1/√2 -/
@[simp] lemma convert_one_to_sqrt2 :
    (convert one_at_u1 wSqrt2).x = 1 / Real.sqrt 2 := by
  simp [one_at_u1, convert, Unit.ratio, u1, wSqrt2]

/-- 同単位での和： (1,1)+(1,1) = (1,2) -/
@[simp] lemma add_same_unit :
    addVia u1 one_at_u1 one_at_u1 = ⟨u1, 2⟩ := by
  simp [addVia, convert, Unit.ratio, u1, one_at_u1]
  norm_num

/-- √2 単位へ揃えて足すと： (√2, 1/√2 + 1/√2) = (√2, √2) -/
@[simp] lemma add_via_sqrt2 :
    addVia wSqrt2 one_at_u1 one_at_u1 = ⟨wSqrt2, Real.sqrt 2⟩ := by
  simp [addVia, convert, Unit.ratio, wSqrt2, one_at_u1, u1]
  field_simp
  ring_nf
  norm_num

end Examples

end Qty

-- -------------------------------------------------------

/-- 単位を添字にした数量（型でファイバーを分ける） -/
@[ext] structure QtyT (u : Unit) where
  x : ℝ

namespace QtyT

instance (u : Unit) : Zero (QtyT u) := ⟨⟨0⟩⟩
instance (u : Unit) : Add  (QtyT u) := ⟨fun a b => ⟨a.x + b.x⟩⟩
instance (u : Unit) : AddCommMonoid (QtyT u) where
  add_assoc a b c := by
    ext
    -- (a + b + c).x = (a.x + b.x + c.x)
    -- (a + (b + c)).x = (a.x + (b.x + c.x))
    -- 実数の加法の結合法則を使う
    exact add_assoc a.x b.x c.x
  zero_add a      := by ext; exact zero_add a.x
  add_zero a      := by ext; exact add_zero a.x
  add_comm a b    := by ext; exact add_comm a.x b.x
  nsmul n a       := ⟨n • a.x⟩
  nsmul_zero a    := by ext; rfl
  nsmul_succ n a  := by ext; rw [add_nsmul, one_nsmul]; rfl

/-- 単位換算（線形） -/
noncomputable def convert {u w : Unit} (q : QtyT u) : QtyT w :=
  ⟨ q.x * Unit.ratio u w ⟩

@[simp] lemma convert_add {u w} (a b : QtyT u) :
    (convert (a + b) : QtyT w) = convert a + convert b := by
  ext
  -- (a + b).x = a.x + b.x なので、左辺は (a.x + b.x) * u.ratio w
  simp only [convert]
  -- ここで実数の分配則を使う
  exact add_mul a.x b.x (Unit.ratio u w)

@[simp] lemma convert_zero {u w} :
    (convert (0 : QtyT u) : QtyT w) = (0 : QtyT w) := by
  ext
  -- x 0 = 0 なので 0 * anything = 0
  simp only [convert]
  -- 0 * anything = 0 を使う
  exact zero_mul (Unit.ratio u w)
end QtyT

-- -------------------------------------------------------

namespace DUnit

/-- log 座標（u > 0 なので安全） -/
noncomputable def logU (u : Unit) : ℝ := Real.log u.val

@[simp] lemma logU_mapUnit (u : Unit) :
    logU (Qty.mapUnit u) = 2 * logU u := by
  -- log(u^2) = 2 log u
  have : 0 < u.val := u.pos
  simp only [logU, Qty.mapUnit, pow_two, ne_eq, this.ne', not_false_eq_true, Real.log_mul]
  rw [add_comm, ←two_mul]

end DUnit

-- -------------------------------------------------------

namespace QtyT

-- 既存の Zero, Add, AddCommMonoid に加えてスカラー倍
instance (u : Unit) : SMul ℝ (QtyT u) := ⟨fun r q => ⟨r * q.x⟩⟩

instance (u : Unit) : AddCommMonoid (QtyT u) := inferInstance   -- ぬしの定義のままでOK

instance (u : Unit) : Module ℝ (QtyT u) where
  smul_add r a b := by ext; exact mul_add r a.x b.x
  add_smul r s a := by ext; exact add_mul r s a.x
  one_smul a     := by ext; exact one_mul a.x
  zero_smul a    := by ext; exact zero_mul a.x
  smul_zero r    := by ext; exact mul_zero r
  mul_smul r s a := by ext; exact mul_smul r s a.x

/-- 変換は線形 -/
@[simp] lemma convert_smul {u w} (r : ℝ) (q : QtyT u) :
    (convert (r • q) : QtyT w) = r • (convert q : QtyT w) := by
  ext
  simp only [convert]
  change (r * q.x) * Unit.ratio u w = r * (q.x * Unit.ratio u w)
  rw [mul_assoc]

/-- 単位換算は線形同型（可逆） -/
noncomputable def convertLinEquiv {u w : Unit} : QtyT u ≃ₗ[ℝ] QtyT w :=
{ toLinearMap :=
  { toFun := fun q => convert q,
    map_add' := by
      intro a b
      ext
      simp only [convert]
      change (a.x + b.x) * Unit.ratio u w = a.x * Unit.ratio u w + b.x * Unit.ratio u w
      exact add_mul a.x b.x (Unit.ratio u w),
    map_smul' := by
      intro r q
      ext
      simp only [convert, Real.ringHom_apply]
      change (r * q.x) * Unit.ratio u w = r * (q.x * Unit.ratio u w)
      rw [mul_assoc]
  },
  invFun := fun q => (convert q : QtyT u), -- Define the inverse function
  left_inv := by
    intro q
    ext
    simp [convert, Unit.ratio]
    -- ゴール: q.x * (u.val / w.val) * (w.val / u.val) = q.x
    field_simp [u.val_ne_zero, w.val_ne_zero],
  right_inv := by
    intro q
    ext
    simp [convert, Unit.ratio]
    field_simp [u.val_ne_zero, w.val_ne_zero] }

end QtyT

-- -------------------------------------------------------

namespace Qty

@[simp] lemma addVia_comm (w : Unit) (a b : Qty) :
    addVia w a b = addVia w b a := by
  unfold addVia; simp [convert, add_comm]

@[simp] lemma addVia_assoc (w : Unit) (a b c : Qty) :
    addVia w (addVia w a b) c = addVia w a (addVia w b c) := by
  unfold addVia; simp [convert, add_assoc]

end Qty

-- -------------------------------------------------------

namespace Qty

/-- 単位の n 乗 -/
def mapUnitN (n : ℕ) (u : Unit) : Unit :=
  ⟨u.val ^ n, by exact pow_pos u.pos n⟩

/-
  単位の“掛け算”を @[simp] instance : Mul Unit として与え、
  mapUnitN を Monoid.End Unit の元として登録しておくと、
  ratio_mapUnitN が isMulHom 的に自動で転がる。
-/
-- Monoid.End のインスタンスをここで与えると、構造体の Prop 項（pos など）の
-- 証明同一性を要求する等式が発生し証明が複雑になるため削除した。
-- 必要な性質（例えば ratio の性質）は個別に補題として定義してある。

/-- F_{n+1} の持ち上げ： (u,x) ↦ (u^{n+1}, x / u^n) で自然性が閉じる（n >= 0 の標準形） -/
noncomputable def liftFN (n : ℕ) (q : Qty) : Qty :=
  ⟨mapUnitN (n + 1) q.u, q.x / q.u.val ^ n⟩

noncomputable def liftFN' (n : ℕ) (q : Qty) : Qty :=
  ⟨mapUnitN n q.u, q.x / q.u.val ^ (n - 1)⟩

/-- 自然性四角： convert ∘ liftFN = liftFN ∘ convert （n を n+1 形式で扱う） -/
@[simp] lemma convert_natural_FN (n : ℕ) (q : Qty) (w : Unit) :
  convert (liftFN n q) (mapUnitN (n + 1) w) = liftFN n (convert q w) := by
  cases q with
  | mk u x =>
    ext
    · rfl
    · simp [liftFN, mapUnitN, convert, Unit.ratio, pow_succ]
      field_simp [u.val_ne_zero, w.val_ne_zero]


end Qty

-- -------------------------------------------------------

namespace Unit

@[simp] lemma ratio_mapUnitN (n : ℕ) (u w : Unit) :
  ratio (Qty.mapUnitN n u) (Qty.mapUnitN n w)
    = (u.val / w.val) ^ n := by
  -- (u^n)/(w^n) = (u/w)^n
  induction n with
  | zero =>
      simp [Qty.mapUnitN, ratio]
  | succ n ih =>
      unfold ratio
      simp only [Qty.mapUnitN, pow_succ]
      -- ゴール: (u.val ^ n * u.val) / (w.val ^ n * w.val) = (u.val / w.val) ^ n * (u.val / w.val)
      have :
        (u.val ^ n * u.val) / (w.val ^ n * w.val)
      = (u.val ^ n / w.val ^ n) * (u.val / w.val) := by field_simp
      rw [this]
      rw [← div_pow]

@[simp] lemma ratio_mul_symm (u w : Unit) :
  ratio u w * ratio w u = 1 := by
  -- (u/w)*(w/u) = 1
  have hu : u.val ≠ 0 := u.val_ne_zero
  have hw : w.val ≠ 0 := w.val_ne_zero
  unfold ratio; field_simp [hu, hw]

@[simp] lemma ratio_symm_mul (u w : Unit) :
  ratio w u * ratio u w = 1 := by simp [mul_comm, ratio_mul_symm]

end Unit

namespace Qty

@[simp] lemma convert_natural_FN' (n : ℕ) (q : Qty) (w : Unit) :
  convert (liftFN n q) (mapUnitN (n + 1) w) = liftFN n (convert q w) := by
  cases q with
  | mk u x =>
    ext <;>
    simp [liftFN, mapUnitN, convert, Unit.ratio, pow_succ]
    field_simp [u.val_ne_zero, w.val_ne_zero]

end Qty

end DHNT

end DkMath

-- -------------------------------------------------------
/- 2026/01/19  7:50 build success with Mathlib4 leanprover-community/mathlib:
  checking out revision '2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
  leanprover/lean4:v4.26.0
---
$ lake build MathlibHello/DHNT.lean
Build completed successfully (7743 jobs).
-/
