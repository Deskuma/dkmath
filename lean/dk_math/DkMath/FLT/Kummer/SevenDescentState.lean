/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRamifiedFrobenius
import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance

#print "file: DkMath.FLT.Kummer.SevenDescentState"

/-! # FLT7教科書：反復する状態
元の自然数反例を、円分整数環の同じ七乗方程式へ一度だけ入れる。
大域的な互いに素性も保存する設計とし、次章の剥離イデアルを簡潔にする。
GN/GTailは恒等式を保存し、降下の測度は分岐深度である。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven
open DkMath.FLT.Kummer.SevenPrimaryNorm DkMath.FLT.Kummer.SevenRealGN
open SevenCyclotomicDegreeSixInt
open DkMath.CosmicFormulaBinom

local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 元の自然数反例へ毎回戻る必要はない。七乗方程式と分岐条件を反復状態にする。 -/
structure State (m : ℕ) where
  x : CC
  y : CC
  z : CC
  epsilon : CCˣ
  coprime : IsCoprime x y
  y_away : ¬ ramifiedUniformizer ∣ y
  z_away : ¬ ramifiedUniformizer ∣ z
  equation : x ^ 7 + y ^ 7 = (epsilon : CC) * (ramifiedUniformizer ^ m * z) ^ 7

/-- お手本 exists_solution' の最後の代数操作。
係数比の七乗根を供給したときだけ正規化でき、同じy,zの非分岐性を保つ。 -/
theorem normalize_weighted (m : ℕ) (x y z : CC) (u v e k : CCˣ)
    (hxy : IsCoprime x y)
    (hy : ¬ ramifiedUniformizer ∣ y) (hz : ¬ ramifiedUniformizer ∣ z)
    (h : (u : CC) * x ^ 7 + (v : CC) * y ^ 7 =
      (e : CC) * (ramifiedUniformizer ^ m * z) ^ 7)
    (hk : u / v = k ^ 7) :
    ∃ E : State m, E.x = (k : CC) * x ∧ E.y = y ∧ E.z = z := by
  have hu : u = v * k ^ 7 := by
    rw [← hk]
    simp [div_eq_mul_inv, mul_left_comm]
  refine ⟨{
    x := (k : CC) * x
    y := y
    z := z
    epsilon := e / v
    coprime := (isCoprime_mul_unit_left_left k.isUnit x y).mpr hxy
    y_away := hy
    z_away := hz
    equation := ?_ }, rfl, rfl, rfl⟩
  apply mul_left_cancel₀ v.isUnit.ne_zero
  have hcancel : (v : CC) * ((e / v : CCˣ) : CC) = (e : CC) := by
    change ((v * (e / v) : CCˣ) : CC) = _
    congr 1
    simp [div_eq_mul_inv]
  rw [← mul_assoc, hcancel]
  rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow] at h
  linear_combination h

/-- GTailの一層目は、同じ加法方程式をgap=x+y, parameter=-yで表す。恒等式を壊さない。 -/
theorem seventh_sum_eq_gtail (x y : CC) :
    x ^ 7 + y ^ 7 = (x + y) * DkMath.CosmicFormula.GTail 7 1 (x + y) (-y) := by
  have ht := DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap 7 (x + y) (-y)
  have hn : (-y) ^ 7 = -(y ^ 7) := by ring
  rw [add_neg_cancel_right, hn] at ht
  linear_combination ht

/-- GN版も元の等式をそのまま保存する。 -/
theorem seventh_sum_eq_gn (x y : CC) :
    x ^ 7 + y ^ 7 = (x + y) * GN 7 (x + y) (-y) := by
  have ht := cosmic_id_csr' (R := CC) 7 (x + y) (-y)
  have hn : (-y) ^ 7 = -(y ^ 7) := by ring
  rw [add_neg_cancel_right, hn] at ht
  linear_combination ht

/-- 降下状態をGNに翻訳しても右辺の単元・分岐深度・根を交換しない。 -/
theorem State.gn_equation {m : ℕ} (E : State m) :
    (E.x + E.y) * GN 7 (E.x + E.y) (-E.y) =
      (E.epsilon : CC) * (ramifiedUniformizer ^ m * E.z) ^ 7 := by
  rw [← seventh_sum_eq_gn]
  exact E.equation

/-- お手本のπ=ζ-1とDkMathのlambda=1-ζの符号差は単元へ吸収できる。 -/
theorem State.pi_equation {m : ℕ} (E : State m) :
    E.x ^ 7 + E.y ^ 7 =
      ((E.epsilon * ((-1 : CCˣ) ^ m) ^ 7 : CCˣ) : CC) *
        ((zeta - 1) ^ m * E.z) ^ 7 := by
  have hl : ramifiedUniformizer = (-1 : CC) * (zeta - 1) := by
    unfold ramifiedUniformizer
    ring
  rw [E.equation, hl]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, mul_pow]
  ring

/-- 分岐評価から整数上の可除性を正確に回復する。 -/
theorem uniformizer_dvd_int_iff (n : ℤ) :
    ramifiedUniformizer ∣ (n : CC) ↔ (7 : ℤ) ∣ n := by
  rw [← ramifiedEval_eq_zero_iff_dvd]
  simp only [map_intCast]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n 7

/-- 元のramified summitから直接初期状態を作る。実三次orbit・common primeは不要。 -/
theorem initial_state_of_summit (s : PrimitiveRamifiedSummitPacket) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (State m) := by
  have hn : ¬ IsUnit ramifiedUniformizer := by
    intro hu
    have hz := hu.map ramifiedEval
    rw [ramifiedEval_uniformizer] at hz
    exact not_isUnit_zero hz
  have hd0 : (s.distinguished : CC) ≠ 0 := by
    apply Int.cast_ne_zero.mpr
    rw [s.distinguished_eq]
    have hg : (s.gapRoot : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.gapRoot_pos)
    have hr : (s.residualRoot : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.residualRoot_pos)
    exact mul_ne_zero (mul_ne_zero (by decide) hg) hr
  have hf := FiniteMultiplicity.of_not_isUnit hn hd0
  obtain ⟨z, hz, hza⟩ := hf.exists_eq_pow_mul_and_not_dvd
  have hd : (7 : ℤ) ∣ s.distinguished := by
    refine ⟨(s.gapRoot : ℤ) * s.residualRoot, ?_⟩
    rw [s.distinguished_eq]
    ring
  have hld := (uniformizer_dvd_int_iff s.distinguished).mpr hd
  have hm : 1 ≤ multiplicity ramifiedUniformizer (s.distinguished : CC) :=
    Nat.one_le_iff_ne_zero.mpr ((multiplicity_ne_zero hf).mpr hld)
  refine ⟨_, hm, ⟨{
    x := (s.endpointLeft : CC)
    y := -(s.endpointRight : CC)
    z := z
    epsilon := 1
    coprime := (s.endpoint_coprime.map (Int.castRingHom CC)).neg_right
    y_away := ?_
    z_away := hza
    equation := ?_ }⟩⟩
  · intro hy
    have hd := (uniformizer_dvd_int_iff s.endpointRight).mp (dvd_neg.mp hy)
    exact s.endpointRight_not_seven_dvd hd
  · have he := congrArg (Int.castRingHom CC) s.fermat_eq
    simp only [map_sub, map_pow] at he
    change (s.endpointLeft : CC) ^ 7 - (s.endpointRight : CC) ^ 7 =
      (s.distinguished : CC) ^ 7 at he
    simp only [Units.val_one, one_mul]
    change (s.endpointLeft : CC) ^ 7 + (-(s.endpointRight : CC)) ^ 7 =
      (ramifiedUniformizer ^ multiplicity ramifiedUniformizer (s.distinguished : CC) * z) ^ 7
    rw [← hz]
    have hneg : (-(s.endpointRight : CC)) ^ 7 = -((s.endpointRight : CC) ^ 7) := by ring
    rw [hneg]
    exact he

/-- DkMath既存のCase I排除と三端点の符号正規化を経て、任意のprimitive反例が初期状態へ入る。 -/
theorem initial_state_of_counterexample {a b c : ℕ} (source : CounterexamplePack a b c) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (State m) := by
  obtain ⟨r⟩ := nonempty_primitiveCounterexampleRamifiedProvenance source
  exact initial_state_of_summit r.summit

-- Depth zero really is inhabited; the positive-depth guard cannot be dropped.
example : Nonempty (State 0) := by
  have h1 : ¬ ramifiedUniformizer ∣ (1 : CC) := by
    intro hd
    have := (uniformizer_dvd_int_iff 1).mp hd
    norm_num at this
  exact ⟨{
    x := 0
    y := 1
    z := 1
    epsilon := 1
    coprime := isCoprime_one_right
    y_away := h1
    z_away := h1
    equation := by simp }⟩

end
end DkMath.FLT.Kummer.SevenDescent
