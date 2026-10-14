/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CoordinateNormalForm
import DkMath.Lib.NumberTheory.TraceOnePowerLanding
import Mathlib.Tactic

#print "file: DkMath.FLT.Seven.PrimeTraceOneRamifiedObstruction"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.Lib.NumberTheory

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! The specialized packet is kept separate from the generic quadratic
residual packet.  These lemmas only expose the norm and coordinate facts that
are already present in the specialized packet. -/

theorem SevenQuadraticSeventhPowerPacket.root_norm_eq
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    norm p.root = (p.residual.powerSplit.b : ℤ) := by
  have hpows : norm p.root ^ 7 =
      (p.residual.powerSplit.b : ℤ) ^ 7 := by
    rw [← traceOne_norm_pow, ← p.residual_eq,
      p.residual.residual_norm_eq]
  have hnonneg : 0 ≤ norm p.root := traceOneNegTwo_norm_nonneg p.root
  have habspows : Int.natAbs (norm p.root) ^ 7 =
      p.residual.powerSplit.b ^ 7 := by
    calc
      Int.natAbs (norm p.root) ^ 7 =
          Int.natAbs (norm p.root ^ 7) := by rw [Int.natAbs_pow]
      _ = Int.natAbs ((p.residual.powerSplit.b : ℤ) ^ 7) :=
        congrArg Int.natAbs hpows
      _ = p.residual.powerSplit.b ^ 7 := by simp
  have habs : Int.natAbs (norm p.root) =
      p.residual.powerSplit.b :=
    Nat.pow_left_injective (by decide : 7 ≠ 0) habspows
  calc
    norm p.root = (Int.natAbs (norm p.root) : ℤ) :=
      (Int.natAbs_of_nonneg hnonneg).symm
    _ = (p.residual.powerSplit.b : ℤ) := congrArg Nat.cast habs

theorem SevenQuadraticSeventhPowerPacket.root_norm_not_seven_dvd
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    ¬ (7 : ℤ) ∣ norm p.root := by
  rw [p.root_norm_eq]
  intro h
  exact p.residual.powerSplit.seven_not_dvd_b (Int.ofNat_dvd.mp h)

theorem SevenQuadraticSeventhPowerPacket.root_linear_mod_seven_ne_zero
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    (p.root.fst : ZMod 7) + 4 * (p.root.snd : ZMod 7) ≠ 0 := by
  intro hlinear
  apply p.root_norm_not_seven_dvd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  rw [traceOneNorm_mod_seven_eq_linear_sq, hlinear]
  simp

theorem SevenQuadraticSeventhPowerPacket.ramified_coordinates_mod_seven_ne_zero
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    (ramifiedSeventhFst p.root.fst p.root.snd : ZMod 7) ≠ 0 ∧
      (ramifiedSeventhSnd p.root.fst p.root.snd : ZMod 7) ≠ 0 := by
  have hlin := p.root_linear_mod_seven_ne_zero
  constructor
  · rw [ramifiedSeventhFst_mod_seven]
    intro hzero
    apply hlin
    linear_combination -hzero
  · rw [ramifiedSeventhSnd_mod_seven]
    intro hzero
    rcases mul_eq_zero.mp hzero with htwo | hzero
    · exact (by decide : (2 : ZMod 7) ≠ 0) htwo
    · exact hlin hzero

private theorem strip_seven_from_product
    {n : ℕ} {v core : ℤ}
    (hprod : (7 : ℤ) ^ (n + 1) ∣ v * core)
    (hcore : ¬ (7 : ℤ) ∣ core) :
    ∃ w : ℤ, v = 7 * w ∧ (7 : ℤ) ^ n ∣ w * core := by
  have hseven : (7 : ℤ) ∣ v * core := by
    apply dvd_trans (show (7 : ℤ) ∣ 7 ^ (n + 1) by
      refine ⟨7 ^ n, ?_⟩
      ring)
    exact hprod
  rcases (Prime.dvd_mul (by norm_num : Prime (7 : ℤ))).mp hseven with hv | hc
  · rcases hv with ⟨w, hw⟩
    rcases hprod with ⟨k, hk⟩
    refine ⟨w, hw, ⟨k, ?_⟩⟩
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * (w * core) = (7 * w) * core := by ring
      _ = v * core := by rw [hw]
      _ = 7 ^ (n + 1) * k := hk
      _ = 7 * (7 ^ n * k) := by ring
  · exact False.elim (hcore hc)

theorem SevenQuadraticSeventhPowerPacket.seven_pow_five_dvd_root_snd
    {x y z : ℕ} (p : SevenQuadraticSeventhPowerPacket x y z) :
    (7 : ℤ) ^ 5 ∣ p.root.snd := by
  let q := ramifiedCoordinateNormalForm_of_packet p
  let s := p.residual.powerSplit
  let u := p.root.fst
  let v := p.root.snd
  let H : ℤ := 2 * (z : ℤ) ^ 2 + 3 * (z : ℤ) * (y : ℤ) +
    2 * (y : ℤ) ^ 2
  have hyz : y ≤ z :=
    (right_lt_of_fermat7Equation s.sevenAdic.counterexample.hx
      s.sevenAdic.counterexample.hEq).le
  have hgap : (z : ℤ) - (y : ℤ) =
      (7 : ℤ) ^ 6 * (s.a : ℤ) ^ 7 := by
    rw [← Int.ofNat_sub hyz]
    exact_mod_cast s.gap_eq
  have hcoord : -(7 : ℤ) * seventhPowerSnd u v =
      ((z : ℤ) - (y : ℤ)) * H := by
    have hfst : cyclotomicSevenFst (z : ℤ) (y : ℤ) =
        ramifiedSeventhFst u v := by
      have hroot : q.seventhPower.root = p.root := by rfl
      simpa only [u, v, hroot] using q.fst_eq
    have hsnd : cyclotomicSevenSnd (z : ℤ) (y : ℤ) =
        ramifiedSeventhSnd u v := by
      have hroot : q.seventhPower.root = p.root := by rfl
      simpa only [u, v, hroot] using q.snd_eq
    calc
      -(7 : ℤ) * seventhPowerSnd u v =
          2 * ramifiedSeventhFst u v + ramifiedSeventhSnd u v := by
            rw [ramifiedSeventhFst_eq, ramifiedSeventhSnd_eq]
            ring
      _ = 2 * cyclotomicSevenFst (z : ℤ) (y : ℤ) +
          cyclotomicSevenSnd (z : ℤ) (y : ℤ) := by
            rw [hfst, hsnd]
      _ = ((z : ℤ) - (y : ℤ)) * H := by
            simp [H, cyclotomicSevenFst, cyclotomicSevenSnd]
            ring
  have hH : (7 : ℤ) ∣ H := by
    have hgap7 : (7 : ℤ) ∣ (z : ℤ) - (y : ℤ) := by
      rw [hgap]
      refine ⟨(7 : ℤ) ^ 5 * (s.a : ℤ) ^ 7, ?_⟩
      ring
    rcases hgap7 with ⟨d, hd⟩
    refine ⟨(y : ℤ) ^ 2 + 7 * d * (y : ℤ) + 14 * d ^ 2, ?_⟩
    have hz : (z : ℤ) = (y : ℤ) + 7 * d := by linarith
    dsimp [H]
    rw [hz]
    ring
  have hseven6 : (7 : ℤ) ^ 6 ∣ seventhPowerSnd u v := by
    have hdiv : (7 : ℤ) ^ 7 ∣ 7 * seventhPowerSnd u v := by
      rw [hgap] at hcoord
      rcases hH with ⟨h, hh⟩
      refine ⟨-(s.a : ℤ) ^ 7 * h, ?_⟩
      calc
        7 * seventhPowerSnd u v =
            - (-(7 : ℤ) * seventhPowerSnd u v) := by ring
        _ = - ((7 : ℤ) ^ 6 * (s.a : ℤ) ^ 7 * H) := by rw [hcoord]
        _ = (7 : ℤ) ^ 7 * (-(s.a : ℤ) ^ 7 * h) := by rw [hh]; ring
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * seventhPowerSnd u v = 7 ^ 7 * k := hk
      _ = 7 * (7 ^ 6 * k) := by ring
  have hcore : ¬ (7 : ℤ) ∣ seventhPowerSndCore u v := by
    exact seven_not_dvd_seventhPowerSndCore_of_norm
      (p.root_norm_not_seven_dvd)
  have hprod : (7 : ℤ) ^ 5 ∣ v * seventhPowerSndCore u v := by
    rw [seventhPowerSnd_eq_seven_mul] at hseven6
    rcases hseven6 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * (v * seventhPowerSndCore u v) =
          7 * v * seventhPowerSndCore u v := by ring
      _ = 7 ^ 6 * k := hk
      _ = 7 * (7 ^ 5 * k) := by ring
  rcases strip_seven_from_product hprod hcore with ⟨w₁, hv₁, h₁⟩
  rcases strip_seven_from_product h₁ hcore with ⟨w₂, hw₁, h₂⟩
  rcases strip_seven_from_product h₂ hcore with ⟨w₃, hw₂, h₃⟩
  rcases strip_seven_from_product h₃ hcore with ⟨w₄, hw₃, h₄⟩
  rcases strip_seven_from_product h₄ hcore with ⟨w₅, hw₄, h₅⟩
  refine ⟨w₅, ?_⟩
  calc
    v = 7 * w₁ := hv₁
    _ = 7 * (7 * w₂) := by rw [hw₁]
    _ = 7 * (7 * (7 * w₃)) := by rw [hw₂]
    _ = 7 * (7 * (7 * (7 * (7 * w₅)))) := by rw [hw₃, hw₄]
    _ = 7 ^ 5 * w₅ := by ring

end DkMath.FLT.Seven
