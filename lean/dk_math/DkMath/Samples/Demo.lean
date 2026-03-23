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
end Samples
end DkMath
