import Mathlib

-- arbitrary interval unit

namespace DkMath
namespace Samples
namespace IntervalUnit

/-- 「2点 a,b の間」 -/
def Between (a b x : ℝ) : Prop :=
  min a b ≤ x ∧ x ≤ max a b

example : Between 2 5 3 := by
  dsimp [Between]
  constructor <;> norm_num


/-- 集合として区間 -/
def segment (a b : ℝ) : Set ℝ :=
  Set.Icc (min a b) (max a b)


/-- 「2点間の距離を 1（単位）とする」 -/
def UnitDistance {α : Type*} [PseudoMetricSpace α] (a b : α) : Prop :=
  dist a b = 1

example : UnitDistance (0 : ℝ) 1 := by
  dsimp [UnitDistance]
  norm_num [Real.dist_eq]

example : dist (0 : ℝ) 1 = 1 := by
  norm_num [Real.dist_eq]


/-- 「単位区間 [0,1]」 -/
def unitInterval : Set ℝ :=
  Set.Icc (0 : ℝ) 1


noncomputable section

/-- 「区間 [a,b] を単位区間 [0,1] に写す」 -/
def normalizeToUnit (a b x : ℝ) : ℝ :=
  (x - a) / (b - a)

def IsUnitInterval (a b : ℝ) : Prop :=
  |b - a| = 1

example (a b : ℝ) (h : b ≠ a) : normalizeToUnit a b a = 0 := by
  have h' : b - a ≠ 0 := sub_ne_zero.mpr h
  dsimp [normalizeToUnit]
  have : (a - a) / (b - a) = 0 := by
    have : a - a = 0 := by ring
    simp
  simp

example (a b : ℝ) (h : b ≠ a) : normalizeToUnit a b b = 1 := by
  have h' : b - a ≠ 0 := sub_ne_zero.mpr h
  dsimp [normalizeToUnit]
  simp [h']


end

end IntervalUnit

namespace TalkLean

variable (Person : Type) (me : Person)
variable (CanExplainMath SpeaksInLean : Person → Prop)

lemma i_speak_in_lean
  (hCannot : ¬ CanExplainMath me)
  (hBecause : ¬ CanExplainMath me → SpeaksInLean me) :
  SpeaksInLean me := by
  exact hBecause hCannot

lemma i_speak_in_lean'
  (hCannot : ¬ CanExplainMath me)
  (hBecause : ¬ CanExplainMath me → SpeaksInLean me) :
  SpeaksInLean me :=
  hBecause hCannot

end TalkLean

-- アフィン変換

namespace Affine

section
variable (a b x : ℝ)

/-- 正規化の等式 -/
lemma normalize_eq :
    (1 / (b - a)) * x + (-a / (b - a))
  = (x - a) / (b - a)
  := by
  field_simp
  ring

end

end Affine

namespace Affine

section
variable (a b : ℝ)

/-- 正規化関数 -/
noncomputable def normalize (x : ℝ) : ℝ :=
  (x - a) / (b - a)

/-- 正規化関数が a を 0 に写すことを示す -/
lemma map_a (h : b ≠ a) :
  normalize a b a = 0 := by
  dsimp [normalize]
  have h' : b - a ≠ 0 := sub_ne_zero.mpr h
  field_simp [h']
  ring

/-- 正規化関数が b を 1 に写すことを示す -/
lemma map_b (h : b ≠ a) :
  normalize a b b = 1 := by
  dsimp [normalize]
  have h' : b - a ≠ 0 := sub_ne_zero.mpr h
  field_simp [h']

end

end Affine

end Samples
end DkMath
