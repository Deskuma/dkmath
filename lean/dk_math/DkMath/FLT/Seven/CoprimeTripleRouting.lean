/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CubicSecondCoordinateSplit

#print "file: DkMath.FLT.Seven.CoprimeTripleRouting"

namespace DkMath.FLT.Seven

structure AwayEndpointCoprimeTriple (x y z : ℕ) : Type where
  normal : AwayCoordinateNormalForm x y z
  first_pos : 0 < y
  second_pos : 0 < z
  third_pos : 0 < y + z
  coprime_first_second : Nat.Coprime y z
  coprime_first_third : Nat.Coprime y (y + z)
  coprime_second_third : Nat.Coprime z (y + z)

def awayEndpointCoprimeTriple {x y z : ℕ} (p : AwayCoordinateNormalForm x y z) :
    AwayEndpointCoprimeTriple x y z where
  normal := p
  first_pos := p.counterexample.hy
  second_pos := p.counterexample.hz
  third_pos := Nat.add_pos_left p.counterexample.hy z
  coprime_first_second := coprime_y_z_of_counterexamplePack p.counterexample
  coprime_first_third := by
    simpa [add_comm] using (Nat.coprime_add_self_right).2
      (coprime_y_z_of_counterexamplePack p.counterexample)
  coprime_second_third := by
    simpa [Nat.coprime_comm, add_comm] using
      (Nat.coprime_add_self_right).2
        (coprime_y_z_of_counterexamplePack p.counterexample).symm

structure AwayCubicProductPacket (x y z : ℕ) : Type where
  transfer : AwayValuationTransferPacket x y z
  endpointTriple : AwayEndpointCoprimeTriple x y z
  rootTriple : AwayRootCoprimeTriple x y z
  product_eq : y * z * (y + z) =
    7 * rootTriple.vPart * rootTriple.leftPart * rootTriple.rightPart

theorem nonempty_awayCubicProductPacket {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayCubicProductPacket x y z) := by
  rcases nonempty_awayValuationTransferPacket p with ⟨transfer⟩
  let root := awayRootCoprimeTriple p
  exact ⟨{
    transfer := transfer
    endpointTriple := awayEndpointCoprimeTriple p
    rootTriple := root
    product_eq := by
      simpa [root] using away_endpoint_product_cubic_load_eq p }⟩

structure CoprimeTripleRouting
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℕ) : Type where
  c11 : ℕ
  c12 : ℕ
  c13 : ℕ
  c21 : ℕ
  c22 : ℕ
  c23 : ℕ
  c31 : ℕ
  c32 : ℕ
  c33 : ℕ
  row1 : a₁ = c11 * c12 * c13
  row2 : a₂ = c21 * c22 * c23
  row3 : a₃ = c31 * c32 * c33
  col1 : b₁ = c11 * c21 * c31
  col2 : b₂ = c12 * c22 * c32
  col3 : b₃ = c13 * c23 * c33
  row1_coprime : Nat.Coprime c11 c12 ∧ Nat.Coprime c11 c13 ∧ Nat.Coprime c12 c13
  row2_coprime : Nat.Coprime c21 c22 ∧ Nat.Coprime c21 c23 ∧ Nat.Coprime c22 c23
  row3_coprime : Nat.Coprime c31 c32 ∧ Nat.Coprime c31 c33 ∧ Nat.Coprime c32 c33
  col1_coprime : Nat.Coprime c11 c21 ∧ Nat.Coprime c11 c31 ∧ Nat.Coprime c21 c31
  col2_coprime : Nat.Coprime c12 c22 ∧ Nat.Coprime c12 c32 ∧ Nat.Coprime c22 c32
  col3_coprime : Nat.Coprime c13 c23 ∧ Nat.Coprime c13 c33 ∧ Nat.Coprime c23 c33

theorem nonempty_coprimeTripleRouting
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (_ha_pos : 0 < a₁ ∧ 0 < a₂ ∧ 0 < a₃)
    (_hb_pos : 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃)
    (ha12 : Nat.Coprime a₁ a₂) (ha13 : Nat.Coprime a₁ a₃)
    (ha23 : Nat.Coprime a₂ a₃) (hb12 : Nat.Coprime b₁ b₂)
    (hb13 : Nat.Coprime b₁ b₃) (hb23 : Nat.Coprime b₂ b₃)
    (hprod : a₁ * a₂ * a₃ = b₁ * b₂ * b₃) :
    Nonempty (CoprimeTripleRouting a₁ a₂ a₃ b₁ b₂ b₃) := by
  have ha1dvd : a₁ ∣ b₁ * b₂ * b₃ := by rw [← hprod]; exact ⟨a₂ * a₃, by ring⟩
  have ha2dvd : a₂ ∣ b₁ * b₂ * b₃ := by rw [← hprod]; exact ⟨a₁ * a₃, by ring⟩
  have ha3dvd : a₃ ∣ b₁ * b₂ * b₃ := by rw [← hprod]; exact ⟨a₁ * a₂, by ring⟩
  have hb1dvd : b₁ ∣ a₁ * a₂ * a₃ := by rw [hprod]; exact ⟨b₂ * b₃, by ring⟩
  have hb2dvd : b₂ ∣ a₁ * a₂ * a₃ := by rw [hprod]; exact ⟨b₁ * b₃, by ring⟩
  have hb3dvd : b₃ ∣ a₁ * a₂ * a₃ := by rw [hprod]; exact ⟨b₁ * b₂, by ring⟩
  let c11 := Nat.gcd a₁ b₁; let c12 := Nat.gcd a₁ b₂; let c13 := Nat.gcd a₁ b₃
  let c21 := Nat.gcd a₂ b₁; let c22 := Nat.gcd a₂ b₂; let c23 := Nat.gcd a₂ b₃
  let c31 := Nat.gcd a₃ b₁; let c32 := Nat.gcd a₃ b₂; let c33 := Nat.gcd a₃ b₃
  refine ⟨{
    c11 := c11
    c12 := c12
    c13 := c13
    c21 := c21
    c22 := c22
    c23 := c23
    c31 := c31
    c32 := c32
    c33 := c33
    row1 := ?_
    row2 := ?_
    row3 := ?_
    col1 := ?_
    col2 := ?_
    col3 := ?_
    row1_coprime := ?_
    row2_coprime := ?_
    row3_coprime := ?_
    col1_coprime := ?_
    col2_coprime := ?_
    col3_coprime := ?_ }⟩
  · dsimp [c11, c12, c13]
    symm
    calc
      _ = Nat.gcd a₁ (b₁ * (b₂ * b₃)) := by
        rw [(hb12.mul_right hb13).gcd_mul, hb23.gcd_mul]
        ring
      _ = a₁ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using ha1dvd)
  · dsimp [c21, c22, c23]
    symm
    calc
      _ = Nat.gcd a₂ (b₁ * (b₂ * b₃)) := by
        rw [(hb12.mul_right hb13).gcd_mul, hb23.gcd_mul]
        ring
      _ = a₂ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using ha2dvd)
  · dsimp [c31, c32, c33]
    symm
    calc
      _ = Nat.gcd a₃ (b₁ * (b₂ * b₃)) := by
        rw [(hb12.mul_right hb13).gcd_mul, hb23.gcd_mul]
        ring
      _ = a₃ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using ha3dvd)
  · dsimp [c11, c21, c31]
    symm
    rw [Nat.gcd_comm a₁ b₁, Nat.gcd_comm a₂ b₁, Nat.gcd_comm a₃ b₁]
    calc
      _ = Nat.gcd b₁ (a₁ * (a₂ * a₃)) := by
        rw [(ha12.mul_right ha13).gcd_mul, ha23.gcd_mul]
        ring
      _ = b₁ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using hb1dvd)
  · dsimp [c12, c22, c32]
    symm
    rw [Nat.gcd_comm a₁ b₂, Nat.gcd_comm a₂ b₂, Nat.gcd_comm a₃ b₂]
    calc
      _ = Nat.gcd b₂ (a₁ * (a₂ * a₃)) := by
        rw [(ha12.mul_right ha13).gcd_mul, ha23.gcd_mul]
        ring
      _ = b₂ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using hb2dvd)
  · dsimp [c13, c23, c33]
    symm
    rw [Nat.gcd_comm a₁ b₃, Nat.gcd_comm a₂ b₃, Nat.gcd_comm a₃ b₃]
    calc
      _ = Nat.gcd b₃ (a₁ * (a₂ * a₃)) := by
        rw [(ha12.mul_right ha13).gcd_mul, ha23.gcd_mul]
        ring
      _ = b₃ := Nat.gcd_eq_left_iff_dvd.mpr (by simpa [mul_assoc] using hb3dvd)
  · exact ⟨hb12.gcd_both a₁ a₁, hb13.gcd_both a₁ a₁, hb23.gcd_both a₁ a₁⟩
  · exact ⟨hb12.gcd_both a₂ a₂, hb13.gcd_both a₂ a₂, hb23.gcd_both a₂ a₂⟩
  · exact ⟨hb12.gcd_both a₃ a₃, hb13.gcd_both a₃ a₃, hb23.gcd_both a₃ a₃⟩
  · simpa [Nat.gcd_comm] using
      (show Nat.Coprime (Nat.gcd b₁ a₁) (Nat.gcd b₁ a₂) ∧
          Nat.Coprime (Nat.gcd b₁ a₁) (Nat.gcd b₁ a₃) ∧
          Nat.Coprime (Nat.gcd b₁ a₂) (Nat.gcd b₁ a₃) from
        ⟨ha12.gcd_both b₁ b₁, ha13.gcd_both b₁ b₁, ha23.gcd_both b₁ b₁⟩)
  · simpa [Nat.gcd_comm] using
      (show Nat.Coprime (Nat.gcd b₂ a₁) (Nat.gcd b₂ a₂) ∧
          Nat.Coprime (Nat.gcd b₂ a₁) (Nat.gcd b₂ a₃) ∧
          Nat.Coprime (Nat.gcd b₂ a₂) (Nat.gcd b₂ a₃) from
        ⟨ha12.gcd_both b₂ b₂, ha13.gcd_both b₂ b₂, ha23.gcd_both b₂ b₂⟩)
  · simpa [Nat.gcd_comm] using
      (show Nat.Coprime (Nat.gcd b₃ a₁) (Nat.gcd b₃ a₂) ∧
          Nat.Coprime (Nat.gcd b₃ a₁) (Nat.gcd b₃ a₃) ∧
          Nat.Coprime (Nat.gcd b₃ a₂) (Nat.gcd b₃ a₃) from
        ⟨ha12.gcd_both b₃ b₃, ha13.gcd_both b₃ b₃, ha23.gcd_both b₃ b₃⟩)

structure AwayCubicRoutingPacket (x y z : ℕ) : Type where
  cubic : AwayCubicProductPacket x y z
  routing : CoprimeTripleRouting y z (y + z)
    (7 * cubic.rootTriple.vPart) cubic.rootTriple.leftPart cubic.rootTriple.rightPart

theorem nonempty_awayCubicRoutingPacket {x y z : ℕ}
    (p : AwayCoordinateNormalForm x y z) :
    Nonempty (AwayCubicRoutingPacket x y z) := by
  rcases nonempty_awayCubicProductPacket p with ⟨cubic⟩
  have h7core : ¬ 7 ∣ cubic.rootTriple.leftPart * cubic.rootTriple.rightPart := by
    rw [cubic.rootTriple.leftPart_eq, cubic.rootTriple.rightPart_eq,
      ← Int.natAbs_mul, ← seventhPowerSndCore_factor]
    exact cubic.rootTriple.normal.seven_not_dvd_natAbs_sndCore
  have h7L : ¬ 7 ∣ cubic.rootTriple.leftPart := fun h =>
    h7core (dvd_mul_of_dvd_left h _)
  have h7R : ¬ 7 ∣ cubic.rootTriple.rightPart := fun h =>
    h7core (dvd_mul_of_dvd_right h _)
  have h7copL : Nat.Coprime 7 cubic.rootTriple.leftPart :=
    (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr h7L
  have h7copR : Nat.Coprime 7 cubic.rootTriple.rightPart :=
    (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr h7R
  have hb12 := h7copL.mul_left cubic.rootTriple.coprime_v_left
  have hb13 := h7copR.mul_left cubic.rootTriple.coprime_v_right
  rcases nonempty_coprimeTripleRouting
    ⟨cubic.endpointTriple.first_pos, cubic.endpointTriple.second_pos,
      cubic.endpointTriple.third_pos⟩
    ⟨Nat.mul_pos (by norm_num) cubic.rootTriple.vPart_pos,
      cubic.rootTriple.leftPart_pos, cubic.rootTriple.rightPart_pos⟩
    cubic.endpointTriple.coprime_first_second
    cubic.endpointTriple.coprime_first_third
    cubic.endpointTriple.coprime_second_third hb12 hb13
    cubic.rootTriple.coprime_left_right (by simpa [mul_assoc] using cubic.product_eq) with ⟨r⟩
  exact ⟨⟨cubic, r⟩⟩

end DkMath.FLT.Seven
