/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.FirstCoordinateRemainders

#print "file: DkMath.FLT.Seven.RoutingSevenPivot"

namespace DkMath.FLT.Seven

theorem CoprimeTripleRouting.c11_dvd_row1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c11 ∣ a₁ := by
  simpa only [r.row1] using
    (show r.c11 ∣ r.c11 * r.c12 * r.c13 from ⟨r.c12 * r.c13, by ring⟩)
theorem CoprimeTripleRouting.c12_dvd_row1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c12 ∣ a₁ := by
  simpa only [r.row1] using
    (show r.c12 ∣ r.c11 * r.c12 * r.c13 from ⟨r.c11 * r.c13, by ring⟩)
theorem CoprimeTripleRouting.c13_dvd_row1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c13 ∣ a₁ := by
  simpa only [r.row1] using
    (show r.c13 ∣ r.c11 * r.c12 * r.c13 from ⟨r.c11 * r.c12, by ring⟩)
theorem CoprimeTripleRouting.c21_dvd_row2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c21 ∣ a₂ := by
  simpa only [r.row2] using
    (show r.c21 ∣ r.c21 * r.c22 * r.c23 from ⟨r.c22 * r.c23, by ring⟩)
theorem CoprimeTripleRouting.c22_dvd_row2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c22 ∣ a₂ := by
  simpa only [r.row2] using
    (show r.c22 ∣ r.c21 * r.c22 * r.c23 from ⟨r.c21 * r.c23, by ring⟩)
theorem CoprimeTripleRouting.c23_dvd_row2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c23 ∣ a₂ := by
  simpa only [r.row2] using
    (show r.c23 ∣ r.c21 * r.c22 * r.c23 from ⟨r.c21 * r.c22, by ring⟩)
theorem CoprimeTripleRouting.c31_dvd_row3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c31 ∣ a₃ := by
  simpa only [r.row3] using
    (show r.c31 ∣ r.c31 * r.c32 * r.c33 from ⟨r.c32 * r.c33, by ring⟩)
theorem CoprimeTripleRouting.c32_dvd_row3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c32 ∣ a₃ := by
  simpa only [r.row3] using
    (show r.c32 ∣ r.c31 * r.c32 * r.c33 from ⟨r.c31 * r.c33, by ring⟩)
theorem CoprimeTripleRouting.c33_dvd_row3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c33 ∣ a₃ := by
  simpa only [r.row3] using
    (show r.c33 ∣ r.c31 * r.c32 * r.c33 from ⟨r.c31 * r.c32, by ring⟩)

theorem CoprimeTripleRouting.c11_dvd_col1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c11 ∣ b₁ := by
  simpa only [r.col1] using
    (show r.c11 ∣ r.c11 * r.c21 * r.c31 from ⟨r.c21 * r.c31, by ring⟩)
theorem CoprimeTripleRouting.c21_dvd_col1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c21 ∣ b₁ := by
  simpa only [r.col1] using
    (show r.c21 ∣ r.c11 * r.c21 * r.c31 from ⟨r.c11 * r.c31, by ring⟩)
theorem CoprimeTripleRouting.c31_dvd_col1 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c31 ∣ b₁ := by
  simpa only [r.col1] using
    (show r.c31 ∣ r.c11 * r.c21 * r.c31 from ⟨r.c11 * r.c21, by ring⟩)
theorem CoprimeTripleRouting.c12_dvd_col2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c12 ∣ b₂ := by
  simpa only [r.col2] using
    (show r.c12 ∣ r.c12 * r.c22 * r.c32 from ⟨r.c22 * r.c32, by ring⟩)
theorem CoprimeTripleRouting.c22_dvd_col2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c22 ∣ b₂ := by
  simpa only [r.col2] using
    (show r.c22 ∣ r.c12 * r.c22 * r.c32 from ⟨r.c12 * r.c32, by ring⟩)
theorem CoprimeTripleRouting.c32_dvd_col2 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c32 ∣ b₂ := by
  simpa only [r.col2] using
    (show r.c32 ∣ r.c12 * r.c22 * r.c32 from ⟨r.c12 * r.c22, by ring⟩)
theorem CoprimeTripleRouting.c13_dvd_col3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c13 ∣ b₃ := by
  simpa only [r.col3] using
    (show r.c13 ∣ r.c13 * r.c23 * r.c33 from ⟨r.c23 * r.c33, by ring⟩)
theorem CoprimeTripleRouting.c23_dvd_col3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c23 ∣ b₃ := by
  simpa only [r.col3] using
    (show r.c23 ∣ r.c13 * r.c23 * r.c33 from ⟨r.c13 * r.c33, by ring⟩)
theorem CoprimeTripleRouting.c33_dvd_col3 {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (r : CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) : r.c33 ∣ b₃ := by
  simpa only [r.col3] using
    (show r.c33 ∣ r.c13 * r.c23 * r.c33 from ⟨r.c13 * r.c23, by ring⟩)

inductive AwayRoutingSevenPivot {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Prop
  | rowY (h11 : 7 ∣ r.routing.c11)
      (h12 : ¬ 7 ∣ r.routing.c12) (h13 : ¬ 7 ∣ r.routing.c13)
      (h21 : ¬ 7 ∣ r.routing.c21) (h22 : ¬ 7 ∣ r.routing.c22)
      (h23 : ¬ 7 ∣ r.routing.c23) (h31 : ¬ 7 ∣ r.routing.c31)
      (h32 : ¬ 7 ∣ r.routing.c32) (h33 : ¬ 7 ∣ r.routing.c33)
  | rowZ (h21 : 7 ∣ r.routing.c21)
      (h11 : ¬ 7 ∣ r.routing.c11) (h12 : ¬ 7 ∣ r.routing.c12)
      (h13 : ¬ 7 ∣ r.routing.c13) (h22 : ¬ 7 ∣ r.routing.c22)
      (h23 : ¬ 7 ∣ r.routing.c23) (h31 : ¬ 7 ∣ r.routing.c31)
      (h32 : ¬ 7 ∣ r.routing.c32) (h33 : ¬ 7 ∣ r.routing.c33)
  | rowSum (h31 : 7 ∣ r.routing.c31)
      (h11 : ¬ 7 ∣ r.routing.c11) (h12 : ¬ 7 ∣ r.routing.c12)
      (h13 : ¬ 7 ∣ r.routing.c13) (h21 : ¬ 7 ∣ r.routing.c21)
      (h22 : ¬ 7 ∣ r.routing.c22) (h23 : ¬ 7 ∣ r.routing.c23)
      (h32 : ¬ 7 ∣ r.routing.c32) (h33 : ¬ 7 ∣ r.routing.c33)

private theorem seven_not_dvd_leftPart {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : ¬ 7 ∣ r.cubic.rootTriple.leftPart := by
  rw [r.cubic.rootTriple.leftPart_eq]
  intro h
  apply r.cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore
  rw [seventhPowerSndCore_factor, Int.natAbs_mul]
  exact dvd_mul_of_dvd_left h _

private theorem seven_not_dvd_rightPart {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : ¬ 7 ∣ r.cubic.rootTriple.rightPart := by
  rw [r.cubic.rootTriple.rightPart_eq]
  intro h
  apply r.cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore
  rw [seventhPowerSndCore_factor, Int.natAbs_mul]
  exact dvd_mul_of_dvd_right h _

theorem awayRoutingSevenPivot_of_packet {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : AwayRoutingSevenPivot r := by
  have h12 : ¬ 7 ∣ r.routing.c12 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c12_dvd_col2)
  have h22 : ¬ 7 ∣ r.routing.c22 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c22_dvd_col2)
  have h32 : ¬ 7 ∣ r.routing.c32 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c32_dvd_col2)
  have h13 : ¬ 7 ∣ r.routing.c13 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c13_dvd_col3)
  have h23 : ¬ 7 ∣ r.routing.c23 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c23_dvd_col3)
  have h33 : ¬ 7 ∣ r.routing.c33 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c33_dvd_col3)
  cases r.cubic.transfer.source with
  | right hy hz hsum hcarrier =>
      have h21 : ¬ 7 ∣ r.routing.c21 := fun h => hz (h.trans r.routing.c21_dvd_row2)
      have h31 : ¬ 7 ∣ r.routing.c31 := fun h => hsum (h.trans r.routing.c31_dvd_row3)
      have h11 : 7 ∣ r.routing.c11 := by
        have := hy
        rw [r.routing.row1] at this
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp this with h | h13'
        · exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h |>.resolve_right h12
        · exact False.elim (h13 h13')
      exact .rowY h11 h12 h13 h21 h22 h23 h31 h32 h33
  | left hz hy hsum hcarrier =>
      have h11 : ¬ 7 ∣ r.routing.c11 := fun h => hy (h.trans r.routing.c11_dvd_row1)
      have h31 : ¬ 7 ∣ r.routing.c31 := fun h => hsum (h.trans r.routing.c31_dvd_row3)
      have h21 : 7 ∣ r.routing.c21 := by
        rw [r.routing.row2] at hz
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hz with h | h23'
        · exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h |>.resolve_right h22
        · exact False.elim (h23 h23')
      exact .rowZ h21 h11 h12 h13 h22 h23 h31 h32 h33
  | sum hsum hy hz hcarrier =>
      have h11 : ¬ 7 ∣ r.routing.c11 := fun h => hy (h.trans r.routing.c11_dvd_row1)
      have h21 : ¬ 7 ∣ r.routing.c21 := fun h => hz (h.trans r.routing.c21_dvd_row2)
      have h31 : 7 ∣ r.routing.c31 := by
        rw [r.routing.row3] at hsum
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hsum with h | h33'
        · exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h |>.resolve_right h32
        · exact False.elim (h33 h33')
      exact .rowSum h31 h11 h12 h13 h21 h22 h23 h32 h33

structure AwayRoutingPivotDepth {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Type where
  pivot : ℕ
  pivot_source : pivot = r.routing.c11 ∨ pivot = r.routing.c21 ∨ pivot = r.routing.c31
  carrier_eq : padicValNat 7 pivot = padicValNat 7 r.cubic.transfer.carrier
  root_eq : padicValNat 7 pivot = 1 + padicValNat 7 r.cubic.rootTriple.vPart

theorem nonempty_awayRoutingPivotDepth {x y z : ℕ}
    (r : AwayCubicRoutingPacket x y z) : Nonempty (AwayRoutingPivotDepth r) := by
  have row1_ne : r.routing.c11 * r.routing.c12 * r.routing.c13 ≠ 0 := by
    rw [← r.routing.row1]; exact r.cubic.endpointTriple.first_pos.ne'
  have row2_ne : r.routing.c21 * r.routing.c22 * r.routing.c23 ≠ 0 := by
    rw [← r.routing.row2]; exact r.cubic.endpointTriple.second_pos.ne'
  have row3_ne : r.routing.c31 * r.routing.c32 * r.routing.c33 ≠ 0 := by
    rw [← r.routing.row3]; exact r.cubic.endpointTriple.third_pos.ne'
  have h12 : ¬ 7 ∣ r.routing.c12 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c12_dvd_col2)
  have h22 : ¬ 7 ∣ r.routing.c22 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c22_dvd_col2)
  have h32 : ¬ 7 ∣ r.routing.c32 := fun h =>
    seven_not_dvd_leftPart r (h.trans r.routing.c32_dvd_col2)
  have h13 : ¬ 7 ∣ r.routing.c13 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c13_dvd_col3)
  have h23 : ¬ 7 ∣ r.routing.c23 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c23_dvd_col3)
  have h33 : ¬ 7 ∣ r.routing.c33 := fun h =>
    seven_not_dvd_rightPart r (h.trans r.routing.c33_dvd_col3)
  cases r.cubic.transfer.source with
  | right hy hz hs hc =>
      have heq : padicValNat 7 r.routing.c11 = padicValNat 7 r.cubic.transfer.carrier := by
        calc
          _ = padicValNat 7 (r.routing.c11 * r.routing.c12 * r.routing.c13) :=
            (padicValNat_unique_factor_of_triple
          (by exact fun h => row1_ne (by simp [h]))
          (by exact fun h => row1_ne (by simp [h]))
          (by exact fun h => row1_ne (by simp [h]))
          h12 h13).symm
          _ = padicValNat 7 y := congrArg (padicValNat 7) r.routing.row1.symm
          _ = _ := congrArg (padicValNat 7) hc.symm
      exact ⟨⟨r.routing.c11, Or.inl rfl, heq, by
        rw [heq, r.cubic.transfer.valuation_eq, r.cubic.rootTriple.vPart_eq,
          ← r.cubic.normal_eq]⟩⟩
  | left hz hy hs hc =>
      have heq : padicValNat 7 r.routing.c21 = padicValNat 7 r.cubic.transfer.carrier := by
        calc
          _ = padicValNat 7 (r.routing.c21 * r.routing.c22 * r.routing.c23) :=
            (padicValNat_unique_factor_of_triple
          (by exact fun h => row2_ne (by simp [h]))
          (by exact fun h => row2_ne (by simp [h]))
          (by exact fun h => row2_ne (by simp [h]))
          h22 h23).symm
          _ = padicValNat 7 z := congrArg (padicValNat 7) r.routing.row2.symm
          _ = _ := congrArg (padicValNat 7) hc.symm
      exact ⟨⟨r.routing.c21, Or.inr (Or.inl rfl), heq, by
        rw [heq, r.cubic.transfer.valuation_eq, r.cubic.rootTriple.vPart_eq,
          ← r.cubic.normal_eq]⟩⟩
  | sum hs hy hz hc =>
      have heq : padicValNat 7 r.routing.c31 = padicValNat 7 r.cubic.transfer.carrier := by
        calc
          _ = padicValNat 7 (r.routing.c31 * r.routing.c32 * r.routing.c33) :=
            (padicValNat_unique_factor_of_triple
          (by exact fun h => row3_ne (by simp [h]))
          (by exact fun h => row3_ne (by simp [h]))
          (by exact fun h => row3_ne (by simp [h]))
          h32 h33).symm
          _ = padicValNat 7 (y + z) := congrArg (padicValNat 7) r.routing.row3.symm
          _ = _ := congrArg (padicValNat 7) hc.symm
      exact ⟨⟨r.routing.c31, Or.inr (Or.inr rfl), heq, by
        rw [heq, r.cubic.transfer.valuation_eq, r.cubic.rootTriple.vPart_eq,
          ← r.cubic.normal_eq]⟩⟩

end DkMath.FLT.Seven
