/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Gauge.Dyadic
import DkMath.CosmicFormula.PowerGapBeamGcd
import DkMath.Lib.NumberTheory.PowerFactor

#print "file: DkMath.FLT.Two.GaugeCalibration"

/-!
# FLT2 gauge calibration

This module isolates the arithmetic square-landing mechanism at exponent two.
It is intentionally separate from the public exponent/value gauge facade and
does not invoke the final Pythagorean-triple classification theorem.
-/

namespace DkMath.FLT.Two

open DkMath.CosmicFormula.PowerGapBeam
open DkMath.NumberTheory.Gauge

/-- Positive primitive natural square solutions. -/
structure PrimitiveSquareSolution where
  x : ℕ
  y : ℕ
  z : ℕ
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hEq : x ^ 2 + y ^ 2 = z ^ 2
  hcop : Nat.Coprime x y

/-! ## Elementary parity and square-difference helpers -/

private lemma even_sq {n : ℕ} (hn : Even n) : Even (n ^ 2) := by
  rw [even_iff_two_dvd] at hn ⊢
  simpa [pow_two] using dvd_mul_of_dvd_left hn n

private lemma odd_sq_mod_four {n : ℕ} (hn : Odd n) : n ^ 2 % 4 = 1 := by
  rcases hn with ⟨k, rfl⟩
  have hrewrite : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by
    ring
  rw [hrewrite]
  omega

private lemma even_sq_mod_four {n : ℕ} (hn : Even n) : n ^ 2 % 4 = 0 := by
  rcases hn with ⟨k, rfl⟩
  have hrewrite : (k + k) ^ 2 = 4 * (k * k) := by
    ring
  rw [hrewrite]
  omega

private lemma odd_not_even {n : ℕ} (hn : Odd n) : ¬Even n := by
  intro he
  rcases hn with ⟨k, hk⟩
  rcases he with ⟨l, hl⟩
  omega

private lemma even_not_odd {n : ℕ} (hn : Even n) : ¬Odd n := by
  intro ho
  exact odd_not_even ho hn

private lemma nat_sq_sub_sq_eq_mul {a b : ℕ} (hba : b ≤ a) :
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  have hba' : a - b + b = a := Nat.sub_add_cancel hba
  calc
    a ^ 2 - b ^ 2 = (a - b + b) ^ 2 - b ^ 2 := by rw [hba']
    _ = (a - b) * (a - b + 2 * b) := by
      have hle : b ^ 2 ≤ (a - b + b) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.le_add_left b (a - b)) 2
      apply (Nat.sub_eq_iff_eq_add' hle).2
      ring
    _ = (a - b) * (a + b) := by
      congr 1
      omega

private lemma not_both_even {x y : ℕ} (hcop : Nat.Coprime x y)
    (hx : Even x) (hy : Even y) : False := by
  have htwo : 2 ∣ Nat.gcd x y :=
    Nat.dvd_gcd (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hy)
  rw [hcop.gcd_eq_one] at htwo
  norm_num at htwo

private lemma not_both_odd {x y z : ℕ}
    (hEq : x ^ 2 + y ^ 2 = z ^ 2)
    (hx : Odd x) (hy : Odd y) : False := by
  have hmod := congrArg (fun n : ℕ => n % 4) hEq
  rw [Nat.add_mod, odd_sq_mod_four hx, odd_sq_mod_four hy] at hmod
  rcases Nat.even_or_odd z with hz | hz
  · rw [even_sq_mod_four hz] at hmod
    norm_num at hmod
  · rw [odd_sq_mod_four hz] at hmod
    norm_num at hmod

/-! ## Primitive parity orientation -/

/-- A primitive positive square solution has exactly one even leg. -/
theorem primitiveSquareSolution_parity (P : PrimitiveSquareSolution) :
    (Even P.x ∧ Odd P.y) ∨ (Odd P.x ∧ Even P.y) := by
  rcases Nat.even_or_odd P.x with hx | hx <;>
    rcases Nat.even_or_odd P.y with hy | hy
  · exact False.elim (not_both_even P.hcop hx hy)
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact False.elim (not_both_odd P.hEq hx hy)

/-- In the orientation with even `x` and odd `y`, the hypotenuse is odd. -/
theorem primitiveSquareSolution_z_odd
    (P : PrimitiveSquareSolution) (hx : Even P.x) (hy : Odd P.y) : Odd P.z := by
  have hsq : Odd (P.x ^ 2 + P.y ^ 2) :=
    Even.add_odd (even_sq hx) (Odd.pow (n := 2) hy)
  have hsqz : Odd (P.z ^ 2) := by
    rw [← P.hEq]
    exact hsq
  by_contra hnot
  have hz_even : Even P.z := Nat.not_odd_iff_even.mp hnot
  exact odd_not_even hsqz (even_sq hz_even)

/-! ## Arithmetic coprimality and the exact shared gauge -/

private lemma primitiveSquareSolution_coprime_y_z
    (P : PrimitiveSquareSolution) : Nat.Coprime P.y P.z := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd P.y P.z
  have hgy : g ∣ P.y := Nat.gcd_dvd_left _ _
  have hgz : g ∣ P.z := Nat.gcd_dvd_right _ _
  have hgy_sq : g ∣ P.y ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hgy P.y
  have hgz_sq : g ∣ P.z ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hgz P.z
  have hgx_sq_add : g ∣ P.x ^ 2 + P.y ^ 2 := by
    rw [P.hEq]
    exact hgz_sq
  have hgx_sq : g ∣ P.x ^ 2 := (Nat.dvd_add_left hgy_sq).mp hgx_sq_add
  have hgcd : g ∣ Nat.gcd (P.x ^ 2) P.y := Nat.dvd_gcd hgx_sq hgy
  have hpowcop : Nat.Coprime (P.x ^ 2) P.y := P.hcop.pow_left 2
  rw [hpowcop.gcd_eq_one] at hgcd
  exact Nat.dvd_one.mp hgcd

private lemma primitiveSquareSolution_gap_beam_gcd_dvd_two
    (P : PrimitiveSquareSolution) (_hx : Even P.x) (_hy : Odd P.y) :
    Nat.gcd (P.z - P.y) (P.z + P.y) ∣ 2 := by
  have hyz : P.y ≤ P.z := by
    have hsq : P.y ^ 2 ≤ P.z ^ 2 := by
      rw [← P.hEq]
      exact Nat.le_add_left _ _
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  have hyz_cop : Nat.Coprime P.y P.z := primitiveSquareSolution_coprime_y_z P
  have hcop_int : Int.gcd (P.z : ℤ) (P.y : ℤ) = 1 := by
    simpa [Int.gcd_natCast_natCast] using hyz_cop.symm.gcd_eq_one
  have hdiv_int :=
    DkMath.CosmicFormula.PowerGapBeam.gcd_powerGap_powerBeam_dvd_d_of_coprime_int
      (d := 2) (x := (P.y : ℤ)) (z := (P.z : ℤ)) (by norm_num) hcop_int
  rw [powerGap_eq_sub, powerBeam_two, ← Int.ofNat_sub hyz] at hdiv_int
  rw [Int.gcd_eq_natAbs] at hdiv_int
  have hgap_abs : ((P.z - P.y : ℕ) : ℤ).natAbs = P.z - P.y := by simp
  have hbeam_abs : ((P.z : ℤ) + (P.y : ℤ)).natAbs = P.z + P.y := by
    have hnonneg : (0 : ℤ) ≤ (P.z : ℤ) + (P.y : ℤ) := by positivity
    have hcast := Int.natAbs_of_nonneg hnonneg
    exact_mod_cast hcast
  rw [hgap_abs, hbeam_abs] at hdiv_int
  exact hdiv_int

private lemma primitiveSquareSolution_gap_beam_even
    (P : PrimitiveSquareSolution) (hx : Even P.x) (hy : Odd P.y) :
    2 ∣ P.z - P.y ∧ 2 ∣ P.z + P.y := by
  have hz : Odd P.z := primitiveSquareSolution_z_odd P hx hy
  constructor
  · rcases hz with ⟨k, hk⟩
    rcases hy with ⟨l, hl⟩
    rw [hk, hl]
    omega
  · rcases hz with ⟨k, hk⟩
    rcases hy with ⟨l, hl⟩
    rw [hk, hl]
    omega

theorem primitiveSquareSolution_gap_beam_gcd_eq_two
    (P : PrimitiveSquareSolution) (hx : Even P.x) (hy : Odd P.y) :
    Nat.gcd (P.z - P.y) (P.z + P.y) = 2 := by
  have heven := primitiveSquareSolution_gap_beam_even P hx hy
  have hlow : 2 ∣ Nat.gcd (P.z - P.y) (P.z + P.y) :=
    Nat.dvd_gcd heven.1 heven.2
  have hupp := primitiveSquareSolution_gap_beam_gcd_dvd_two P hx hy
  exact Nat.dvd_antisymm hupp hlow

/-! ## Gauge strip, normalized square body, and square landing -/

/-- The principal Prop-valued gauge-normalized square-landing packet. -/
def PrimitiveSquareLandingGaugeSplit (x y z : ℕ) : Prop :=
  ∃ A B X r s : ℕ,
    Even x ∧ Odd y ∧ Odd z ∧
    z - y = 2 * A ∧ z + y = 2 * B ∧
    Nat.Coprime A B ∧ x = 2 * X ∧ X ^ 2 = A * B ∧
    A = r ^ 2 ∧ B = s ^ 2 ∧
    z - y = 2 * r ^ 2 ∧ z + y = 2 * s ^ 2

private lemma primitiveSquareSolution_square_gap_beam
    (P : PrimitiveSquareSolution) (hyz : P.y ≤ P.z) :
    P.x ^ 2 = (P.z - P.y) * (P.z + P.y) := by
  have hdiff : P.z ^ 2 - P.y ^ 2 = P.x ^ 2 := by
    apply (Nat.sub_eq_iff_eq_add' (by
      rw [← P.hEq]
      exact Nat.le_add_left _ _)).2
    simpa [Nat.add_comm] using P.hEq.symm
  rw [nat_sq_sub_sq_eq_mul hyz] at hdiff
  exact hdiff.symm

private lemma primitiveSquareSolution_gap_beam_coprime_after_strip
    (P : PrimitiveSquareSolution) (hx : Even P.x) (hy : Odd P.y)
    (hgap : 2 ∣ P.z - P.y) (hbeam : 2 ∣ P.z + P.y) :
    Nat.Coprime ((P.z - P.y) / 2) ((P.z + P.y) / 2) := by
  have hgcd : Nat.gcd (P.z - P.y) (P.z + P.y) = 2 :=
    primitiveSquareSolution_gap_beam_gcd_eq_two P hx hy
  have hgap_eq : P.z - P.y = 2 * ((P.z - P.y) / 2) := by
    rw [Nat.mul_div_cancel' hgap]
  have hbeam_eq : P.z + P.y = 2 * ((P.z + P.y) / 2) := by
    rw [Nat.mul_div_cancel' hbeam]
  have hscaled :
      Nat.gcd (2 * ((P.z - P.y) / 2)) (2 * ((P.z + P.y) / 2)) = 2 := by
    rw [← hgap_eq, ← hbeam_eq]
    exact hgcd
  rw [Nat.gcd_mul_left] at hscaled
  have hcancel :
      2 * Nat.gcd ((P.z - P.y) / 2) ((P.z + P.y) / 2) = 2 * 1 := by
    simpa using hscaled
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcancel

private lemma primitiveSquareSolution_x_even_half_square
    (P : PrimitiveSquareSolution) (hx : Even P.x)
    (hgap : 2 ∣ P.z - P.y) (hbeam : 2 ∣ P.z + P.y) :
    (P.x / 2) ^ 2 = ((P.z - P.y) / 2) * ((P.z + P.y) / 2) := by
  have hbody := primitiveSquareSolution_square_gap_beam P (by
    have hsq : P.y ^ 2 ≤ P.z ^ 2 := by
      rw [← P.hEq]
      exact Nat.le_add_left _ _
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq)
  rcases hx with ⟨k, hk⟩
  have hx_eq : P.x = 2 * (P.x / 2) := by
    have hdiv : P.x / 2 = k := by omega
    calc
      P.x = k + k := hk
      _ = 2 * k := by omega
      _ = 2 * (P.x / 2) := by rw [hdiv]
  rw [hx_eq] at hbody
  have hgap_eq : P.z - P.y = 2 * ((P.z - P.y) / 2) :=
    (Nat.mul_div_cancel' hgap).symm
  have hbeam_eq : P.z + P.y = 2 * ((P.z + P.y) / 2) :=
    (Nat.mul_div_cancel' hbeam).symm
  rw [hgap_eq, hbeam_eq] at hbody
  have hscaled :
      4 * (P.x / 2) ^ 2 =
        4 * (((P.z - P.y) / 2) * ((P.z + P.y) / 2)) := by
    calc
      4 * (P.x / 2) ^ 2 = (2 * (P.x / 2)) ^ 2 := by ring
      _ = (2 * ((P.z - P.y) / 2)) * (2 * ((P.z + P.y) / 2)) := hbody
      _ = 4 * (((P.z - P.y) / 2) * ((P.z + P.y) / 2)) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hscaled

theorem primitiveSquareSolution_gap_beam_sq
    (P : PrimitiveSquareSolution) (_hx : Even P.x) (_hy : Odd P.y) :
    (P.x : ℤ) ^ 2 =
      powerGap (P.y : ℤ) (P.z : ℤ) * powerBeam 2 (P.y : ℤ) (P.z : ℤ) := by
  have hyz : P.y ≤ P.z := by
    have hsq : P.y ^ 2 ≤ P.z ^ 2 := by
      rw [← P.hEq]
      exact Nat.le_add_left _ _
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  have hnat := primitiveSquareSolution_square_gap_beam P hyz
  have hcast :
      ((P.x ^ 2 : ℕ) : ℤ) =
        (((P.z - P.y) * (P.z + P.y) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  calc
    (P.x : ℤ) ^ 2 = ((P.x ^ 2 : ℕ) : ℤ) := by norm_num
    _ = (((P.z - P.y) * (P.z + P.y) : ℕ) : ℤ) := hcast
    _ = ((P.z - P.y : ℕ) : ℤ) * ((P.z + P.y : ℕ) : ℤ) := by norm_num
    _ = powerGap (P.y : ℤ) (P.z : ℤ) * powerBeam 2 (P.y : ℤ) (P.z : ℤ) := by
      rw [powerGap_eq_sub, powerBeam_two]
      rw [Int.ofNat_sub hyz]
      norm_num

theorem primitiveSquareSolution_gauge_split
    (P : PrimitiveSquareSolution) (hx : Even P.x) (hy : Odd P.y) :
    PrimitiveSquareLandingGaugeSplit P.x P.y P.z := by
  have hz : Odd P.z := primitiveSquareSolution_z_odd P hx hy
  have heven := primitiveSquareSolution_gap_beam_even P hx hy
  let A := (P.z - P.y) / 2
  let B := (P.z + P.y) / 2
  let X := P.x / 2
  have hgap_eq : P.z - P.y = 2 * A := by
    dsimp [A]
    exact (Nat.mul_div_cancel' heven.1).symm
  have hbeam_eq : P.z + P.y = 2 * B := by
    dsimp [B]
    exact (Nat.mul_div_cancel' heven.2).symm
  have hcop : Nat.Coprime A B := by
    dsimp [A, B]
    exact primitiveSquareSolution_gap_beam_coprime_after_strip P hx hy heven.1 heven.2
  have hbody : X ^ 2 = A * B := by
    dsimp [A, B, X]
    exact primitiveSquareSolution_x_even_half_square P hx heven.1 heven.2
  have hx_eq : P.x = 2 * X := by
    dsimp [X]
    rcases hx with ⟨k, hk⟩
    have hdiv : P.x / 2 = k := by omega
    calc
      P.x = k + k := hk
      _ = 2 * k := by omega
      _ = 2 * (P.x / 2) := by rw [hdiv]
  rcases DkMath.Lib.NumberTheory.power_factor_split (d := 2) hcop hbody.symm with
    ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  refine ⟨A, B, X, r, s, hx, hy, hz, hgap_eq, hbeam_eq, hcop, hx_eq,
    hbody, hr, hs, ?_, ?_⟩
  · rw [hgap_eq, hr]
  · rw [hbeam_eq, hs]

/-- Every primitive positive solution admits the oriented gauge split, possibly
with the two observed legs exchanged. -/
theorem primitiveSquareSolution_oriented_gauge_split
    (P : PrimitiveSquareSolution) :
    PrimitiveSquareLandingGaugeSplit P.x P.y P.z ∨
      PrimitiveSquareLandingGaugeSplit P.y P.x P.z := by
  rcases primitiveSquareSolution_parity P with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl (primitiveSquareSolution_gauge_split P hx hy)
  · let Q : PrimitiveSquareSolution :=
      { x := P.y
        y := P.x
        z := P.z
        hx := P.hy
        hy := P.hx
        hz := P.hz
        hEq := by simpa [Nat.add_comm] using P.hEq
        hcop := P.hcop.symm }
    exact Or.inr (primitiveSquareSolution_gauge_split Q hy hx)

end DkMath.FLT.Two

#print axioms DkMath.FLT.Two.primitiveSquareSolution_parity
#print axioms DkMath.FLT.Two.primitiveSquareSolution_z_odd
#print axioms DkMath.FLT.Two.primitiveSquareSolution_gap_beam_gcd_eq_two
#print axioms DkMath.FLT.Two.primitiveSquareSolution_gap_beam_sq
#print axioms DkMath.FLT.Two.primitiveSquareSolution_gauge_split
#print axioms DkMath.FLT.Two.primitiveSquareSolution_oriented_gauge_split
