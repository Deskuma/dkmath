/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenDescentState
import DkMath.Lib.Cosmic.GNPhaseFactorization

#print "file: DkMath.FLT.Kummer.SevenDescentPhases"

/-! # FLT7教科書：全七位相と底の排除
一段剥離商の剰余は q-i*y という一次式になる。
yが非分岐なので零になる位相はただ一つであり、七因子の積はlambda^8を含む。
これがlambda^7しか含まない深度1の右辺と矛盾する。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt
open scoped BigOperators

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

/-- 位相0も含めた分岐補正係数。非零位相の係数は既存の円分単元。 -/
def phaseSlope (i : Fin 7) : CC :=
  if h : i.val = 0 then 0 else
    (GNRamifierTwist (by
      simp only [Finset.mem_erase, Finset.mem_range]
      exact ⟨h, i.isLt⟩ : i.val ∈ (Finset.range 7).erase 0) : CC)

/-- lambda倍で元の位相差を復元する。 -/
theorem phaseSlope_spec (i : Fin 7) :
    phaseSlope i * ramifiedUniformizer = zeta ^ i.val - 1 := by
  by_cases hi : i.val = 0
  · simp [phaseSlope, hi]
  · simp only [phaseSlope, dite_eq_right hi]
    exact GNRamifierTwist_spec _

/-- 全七位相を剰余体上の一次座標にする。 -/
theorem phaseSlope_residue (i : Fin 7) :
    ramifiedEval (phaseSlope i) = -(i.val : ZMod 7) := by
  by_cases hi : i.val = 0
  · simp [phaseSlope, hi]
  · simp only [phaseSlope, dite_eq_right hi]
    exact ramifiedEval_GNRamifierTwist _

/-- 正深度の式を分岐剰余へ送ると x+y=0 となる。 -/
theorem State.uniformizer_dvd_sum {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    ramifiedUniformizer ∣ E.x + E.y := by
  apply (ramifiedEval_eq_zero_iff_dvd _).mp
  have he := congrArg ramifiedEval E.equation
  simp only [map_add, map_pow, map_mul, ramifiedEval_uniformizer,
    ZMod.pow_card, zero_pow (Nat.ne_of_gt hm), zero_mul, mul_zero] at he
  simpa only [map_add] using he

/-- 実際に割った同じ商を全位相で共有する。 -/
def State.center {m : ℕ} (E : State m) (hm : 1 ≤ m) : CC :=
  (E.uniformizer_dvd_sum hm).choose

/-- centerの来歴。 -/
theorem State.center_spec {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    E.x + E.y = ramifiedUniformizer * E.center hm :=
  (E.uniformizer_dvd_sum hm).choose_spec

/-- 全七位相の一段剥離商。 -/
def State.quotient {m : ℕ} (E : State m) (hm : 1 ≤ m) (i : Fin 7) : CC :=
  E.center hm + phaseSlope i * E.y

/-- 七つすべての線形因子を、同じ中心から復元する。 -/
theorem State.quotient_spec {m : ℕ} (E : State m) (hm : 1 ≤ m) (i : Fin 7) :
    E.x + zeta ^ i.val * E.y = ramifiedUniformizer * E.quotient hm i := by
  have hs := phaseSlope_spec i
  have hc := E.center_spec hm
  unfold State.quotient
  linear_combination hc - hs * E.y

/-- yの剰余は非零。 -/
theorem State.y_residue_ne_zero {m : ℕ} (E : State m) : ramifiedEval E.y ≠ 0 :=
  fun h => E.y_away ((ramifiedEval_eq_zero_iff_dvd _).mp h)

/-- 剥離商が分岐素点に属する唯一の位相。 -/
def State.distinguishedPhase {m : ℕ} (E : State m) (hm : 1 ≤ m) : Fin 7 :=
  ⟨(ramifiedEval (E.center hm) / ramifiedEval E.y).val, ZMod.val_lt _⟩

/-- 特別な位相の剥離商はさらにlambdaで割れる。 -/
theorem State.distinguished_dvd {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    ramifiedUniformizer ∣ E.quotient hm (E.distinguishedPhase hm) := by
  apply (ramifiedEval_eq_zero_iff_dvd _).mp
  simp only [State.quotient, map_add, map_mul, phaseSlope_residue,
    State.distinguishedPhase, ZMod.natCast_zmod_val]
  have hn := E.y_residue_ne_zero
  field_simp
  ring

/-- 他の六位相は一段剥離後に非分岐。一意性を有限探索でなく一次式で示す。 -/
theorem State.quotient_dvd_iff {m : ℕ} (E : State m) (hm : 1 ≤ m) (i : Fin 7) :
    ramifiedUniformizer ∣ E.quotient hm i ↔ i = E.distinguishedPhase hm := by
  constructor
  · intro hd
    have hz := (ramifiedEval_eq_zero_iff_dvd _).mpr hd
    simp only [State.quotient, map_add, map_mul, phaseSlope_residue] at hz
    have he : (i.val : ZMod 7) = ramifiedEval (E.center hm) / ramifiedEval E.y := by
      apply (eq_div_iff E.y_residue_ne_zero).mpr
      linear_combination -hz
    apply Fin.ext
    change i.val = (ramifiedEval (E.center hm) / ramifiedEval E.y).val
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] using hv
  · rintro rfl
    exact E.distinguished_dvd hm

/-- GNの全位相積を使い、七つのlambdaを一度に取り出す。 -/
theorem State.product_quotients {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    E.x ^ 7 + E.y ^ 7 = ramifiedUniformizer ^ 7 * ∏ i : Fin 7, E.quotient hm i := by
  have hf := DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod_fin
    (by decide : 0 < 7) zeta_isPrimitiveRoot (E.x + E.y) (-E.y)
  have hn : (-E.y) ^ 7 = -(E.y ^ 7) := by ring
  rw [add_neg_cancel_right, hn, sub_neg_eq_add] at hf
  rw [hf]
  calc
    _ = ∏ i : Fin 7, (ramifiedUniformizer * E.quotient hm i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hs := E.quotient_spec hm i
      linear_combination hs
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- 全七位相に加えて特別な位相の追加一段がある。 -/
theorem State.uniformizer_pow_eight_dvd {m : ℕ} (E : State m) (hm : 1 ≤ m) :
    ramifiedUniformizer ^ 8 ∣ E.x ^ 7 + E.y ^ 7 := by
  classical
  have hp : ramifiedUniformizer ∣ ∏ i : Fin 7, E.quotient hm i :=
    (E.distinguished_dvd hm).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  rw [E.product_quotients hm]
  exact mul_dvd_mul_left (ramifiedUniformizer ^ 7) hp

/-- 深度1は不可能。単元やzへ追加の七乗性を要求せず、zの非分岐性を使う。 -/
theorem no_state_one : ¬ Nonempty (State 1) := by
  rintro ⟨E⟩
  obtain ⟨w, hw⟩ := E.uniformizer_pow_eight_dvd (by decide)
  have hc : (E.epsilon : CC) * E.z ^ 7 = ramifiedUniformizer * w := by
    apply mul_left_cancel₀ (pow_ne_zero 7 ramifiedUniformizer_ne_zero)
    calc
      _ = E.x ^ 7 + E.y ^ 7 := by rw [E.equation]; ring
      _ = _ := by rw [hw]; ring
  have hr := congrArg ramifiedEval hc
  simp only [map_mul, map_pow, ramifiedEval_uniformizer, zero_mul] at hr
  have hz : ramifiedEval E.z ^ 7 = 0 :=
    (mul_eq_zero.mp hr).resolve_left (E.epsilon.isUnit.map ramifiedEval).ne_zero
  exact E.z_away ((ramifiedEval_eq_zero_iff_dvd _).mp (eq_zero_of_pow_eq_zero hz))

end
end DkMath.FLT.Kummer.SevenDescent
