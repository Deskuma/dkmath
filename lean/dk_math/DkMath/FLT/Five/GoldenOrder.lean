/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SquareGoldenBridge
import Mathlib.NumberTheory.Zsqrtd.Basic

#print "file: DkMath.FLT.Five.GoldenOrder"

namespace DkMath.FLT.Five

/-- An integral pair representing `a + b * phi`, with `phi^2 = phi + 1`. -/
structure GoldenInt where
  fst : ℤ
  snd : ℤ
deriving DecidableEq

/-- The zero element of the integral golden order. -/
def goldenZero : GoldenInt := ⟨0, 0⟩

/-- The unit element of the integral golden order. -/
def goldenOne : GoldenInt := ⟨1, 0⟩

/-- Coordinatewise addition. -/
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩

/-- Coordinatewise negation. -/
def goldenNeg (x : GoldenInt) : GoldenInt := ⟨-x.fst, -x.snd⟩

/-- Coordinatewise subtraction. -/
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)

/-- Multiplication reduced by `phi^2 = phi + 1`. -/
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩

/-- Natural powers for the explicit golden-order API. -/
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x

/-- Extensionality in the integral basis. -/
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all

instance : Zero GoldenInt := ⟨goldenZero⟩
instance : One GoldenInt := ⟨goldenOne⟩
instance : Add GoldenInt := ⟨goldenAdd⟩
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩

@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem golden_fst_neg (x : GoldenInt) : (-x).fst = -x.fst := rfl
@[simp] theorem golden_snd_neg (x : GoldenInt) : (-x).snd = -x.snd := rfl
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl
@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl

/-- The explicit coordinate operations form the honest golden commutative ring. -/
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  refine
    { sub := goldenSub
      nsmul := @nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩
      zsmul := @zsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩ ⟨goldenNeg⟩
        (@nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

instance goldenAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { goldenAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }

instance goldenCommRing : CommRing GoldenInt := by
  refine
    { goldenAddGroupWithOne with
      npow := fun n x => goldenPow x n
      npow_zero := by intro x; rfl
      npow_succ := by
        intro n x
        change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
        rfl
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
    simp <;> ring

/-- Twice a golden integer, embedded in `Z[sqrt 5]` without changing orders. -/
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩

instance goldenFiveNonsquare : Zsqrtd.Nonsquare 5 := by
  refine ⟨fun n h => ?_⟩
  have hn : n < 3 := by
    by_contra hn
    have h3 : 3 ≤ n := Nat.le_of_not_gt hn
    have h9 : 9 ≤ n * n := by nlinarith
    omega
  interval_cases n <;> norm_num at h

theorem goldenDoubleEmbedding_injective :
    Function.Injective goldenDoubleEmbedding := by
  intro x y h
  have hsnd : x.snd = y.snd := congrArg Zsqrtd.im h
  have hfst : 2 * x.fst + x.snd = 2 * y.fst + y.snd :=
    congrArg Zsqrtd.re h
  apply GoldenInt.ext
  · omega
  · exact hsnd

/-- The doubled embedding converts a golden product to twice the embedded product. -/
theorem goldenDoubleEmbedding_mul (x y : GoldenInt) :
    goldenDoubleEmbedding x * goldenDoubleEmbedding y =
      (2 : Zsqrtd 5) * goldenDoubleEmbedding (goldenMul x y) := by
  ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring

theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have hemb : goldenDoubleEmbedding x * goldenDoubleEmbedding y = 0 := by
    rw [goldenDoubleEmbedding_mul]
    rw [show goldenMul x y = 0 by exact h]
    rfl
  rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hemb with hx | hy
  · left
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding x = 0 := hx
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl
  · right
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding y = 0 := hy
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl

instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero := GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero

instance : Nontrivial GoldenInt := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have := congrArg GoldenInt.fst h
  norm_num at this

instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _

@[simp] theorem golden_add_eq (x y : GoldenInt) : goldenAdd x y = x + y := rfl
@[simp] theorem golden_neg_eq (x : GoldenInt) : goldenNeg x = -x := rfl
@[simp] theorem golden_sub_eq (x y : GoldenInt) : goldenSub x y = x - y := rfl
@[simp] theorem golden_mul_eq (x y : GoldenInt) : goldenMul x y = x * y := rfl
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) : goldenPow x n = x ^ n := rfl

/-- The basis element `phi`. -/
def goldenPhi : GoldenInt := ⟨0, 1⟩

/-- Embed an integer in the golden order. -/
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩

/-- The nontrivial conjugation `phi |-> 1 - phi`. -/
def goldenConj (x : GoldenInt) : GoldenInt := ⟨x.fst + x.snd, -x.snd⟩

/-- The integral norm of a golden integer. -/
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2

/-- Conjugation is an involution. -/
theorem goldenConj_invol (x : GoldenInt) :
    goldenConj (goldenConj x) = x := by
  ext <;> simp [goldenConj]

/-- Conjugation respects multiplication. -/
theorem goldenConj_mul (x y : GoldenInt) :
    goldenConj (goldenMul x y) = goldenMul (goldenConj x) (goldenConj y) := by
  ext <;> simp [goldenConj, goldenMul] <;> ring

/-- The structure norm is the previously exposed binary golden norm. -/
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl

/-- Compatibility alias using the checkpoint's explicit API name. -/
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl

/-- The golden norm is multiplicative. -/
theorem goldenNorm_mul (x y : GoldenInt) :
    goldenNorm (goldenMul x y) = goldenNorm x * goldenNorm y := by
  simp [goldenNorm, goldenMul]
  ring

/-- Conjugation preserves the golden norm. -/
theorem goldenNorm_conj (x : GoldenInt) :
    goldenNorm (goldenConj x) = goldenNorm x := by
  simp [goldenNorm, goldenConj]
  ring

/-- Multiplication by the conjugate embeds the norm. -/
theorem golden_mul_conj (x : GoldenInt) :
    goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x) := by
  ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring

/-- The ramified square root `2*phi - 1` of five. -/
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩

/-- The distinguished ramifier `2 + phi`. -/
def goldenTau : GoldenInt := ⟨2, 1⟩

/-- Checkpoint-facing name for the square root of five. -/
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive

/-- Checkpoint-facing name for the ramified element above five. -/
abbrev tau : GoldenInt := goldenTau

theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide

theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]

theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide

theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]

theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]

/-- Divisibility by five of `2*M+N` explicitly extracts a factor of `tau`. -/
theorem exists_goldenTau_factor_of_five_dvd
    {M N : ℤ} (h : (5 : ℤ) ∣ 2 * M + N) :
    ∃ k : ℤ, ∃ beta : GoldenInt,
      2 * M + N = 5 * k ∧
      beta = ⟨M - k, 2 * k - M⟩ ∧
      (⟨M, N⟩ : GoldenInt) = goldenMul goldenTau beta := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ⟨M - k, 2 * k - M⟩, hk, rfl, ?_⟩
  ext <;> simp [goldenMul, goldenTau]
  · ring
  · omega

end DkMath.FLT.Five
