/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.PowerGapBeam
import DkMath.NumberTheory.GdcDivD

#print "file: DkMath.CosmicFormula.PowerGapBeamGcd"

/-!
# GCD Control for Power Gap/Beam

This file connects the Power Gap/Beam vocabulary to the existing
`GcdDiffPow` divisibility theorem.
-/

namespace DkMath.CosmicFormula.PowerGapBeam

open DkMath.Algebra.DiffPow

/-! ## GCD Bridge -/

/-- Under the primitive condition `gcd z x = 1`, the common divisor of the
    Power Gap and Power Beam divides the degree `d`.

This is the Power Gap/Beam wrapper around
`DkMath.NumberTheory.GcdDiffPow.gcd_divides_d`. -/
theorem gcd_powerGap_powerBeam_dvd_d_of_coprime_int
    {d : ℕ} {x z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1) :
    Int.gcd (powerGap x z) (powerBeam d x z) ∣ d := by
  simpa [powerGap, powerBeam, DkMath.Algebra.DiffPow.diffPowSum] using
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d (a := z) (b := x) (d := d) hd hcop

/-- If a prime `p` does not divide `d`, then under `gcd z x = 1` it cannot
    divide both the Power Gap and the Power Beam. -/
theorem prime_not_dvd_d_not_dvd_powerGap_and_powerBeam
    {d p : ℕ} {x z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hpnd : ¬ p ∣ d) :
    ¬ (p ∣ (powerGap x z).natAbs ∧ p ∣ (powerBeam d x z).natAbs) := by
  intro hboth
  have hgcd_dvd_d : Int.gcd (powerGap x z) (powerBeam d x z) ∣ d :=
    gcd_powerGap_powerBeam_dvd_d_of_coprime_int (d := d) (x := x) (z := z) hd hcop
  have hp_dvd_gcd : p ∣ Int.gcd (powerGap x z) (powerBeam d x z) := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.dvd_gcd hboth.1 hboth.2
  exact hpnd (dvd_trans hp_dvd_gcd hgcd_dvd_d)

/-! ## FLT Datum Bridge -/

/-- An FLT-style equation gives both the Power Gap/Beam product expression
    and the gcd control for the same observed side. -/
theorem flt_eq_forces_powerGapBeam_and_gcd
    {d : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d) :
    y ^ d = powerGap x z * powerBeam d x z ∧
      Int.gcd (powerGap x z) (powerBeam d x z) ∣ d := by
  constructor
  · exact flt_eq_forces_powerGapBeam d x y z hflt
  · exact gcd_powerGap_powerBeam_dvd_d_of_coprime_int (d := d) (x := x) (z := z) hd hcop

/-- Symmetric FLT datum bridge, observing the `x` side via the gap from `y` to `z`. -/
theorem flt_eq_forces_powerGapBeam_and_gcd_symm
    {d : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z y = 1)
    (hflt : x ^ d + y ^ d = z ^ d) :
    x ^ d = powerGap y z * powerBeam d y z ∧
      Int.gcd (powerGap y z) (powerBeam d y z) ∣ d := by
  constructor
  · exact flt_eq_forces_powerGapBeam_symm d x y z hflt
  · exact gcd_powerGap_powerBeam_dvd_d_of_coprime_int (d := d) (x := y) (z := z) hd hcop

/-- In an FLT-style primitive context, a prime not dividing `d` that divides the
    Power Beam cannot also divide the corresponding Power Gap. -/
theorem flt_beam_prime_not_dvd_gap_of_not_dvd_d
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (_hflt : x ^ d + y ^ d = z ^ d)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    ¬ p ∣ (powerGap x z).natAbs := by
  intro hgap
  exact prime_not_dvd_d_not_dvd_powerGap_and_powerBeam
    (d := d) (p := p) (x := x) (z := z) hd hcop hpnd ⟨hgap, hbeam⟩

/-- Symmetric version of `flt_beam_prime_not_dvd_gap_of_not_dvd_d`. -/
theorem flt_beam_prime_not_dvd_gap_of_not_dvd_d_symm
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z y = 1)
    (_hflt : x ^ d + y ^ d = z ^ d)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d y z).natAbs) :
    ¬ p ∣ (powerGap y z).natAbs := by
  intro hgap
  exact prime_not_dvd_d_not_dvd_powerGap_and_powerBeam
    (d := d) (p := p) (x := y) (z := z) hd hcop hpnd ⟨hgap, hbeam⟩

/-! ## Valuation Bridge -/

/-- If a prime does not divide the integer gap, then the p-adic valuation of
    `gap * beam` comes entirely from `beam`. -/
theorem padicValNat_natAbs_mul_eq_right_of_not_dvd_left
    {p : ℕ} {gap beam : ℤ}
    (hp : Nat.Prime p)
    (hgap : ¬ p ∣ gap.natAbs) :
    padicValNat p (gap * beam).natAbs = padicValNat p beam.natAbs := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hbeam : beam.natAbs = 0
  · have hprod : (gap * beam).natAbs = 0 := by
      have hbeam_int : beam = 0 := Int.natAbs_eq_zero.mp hbeam
      simp [hbeam_int]
    simp [hprod, hbeam]
  · have hgap_ne : gap.natAbs ≠ 0 := by
      intro hzero
      exact hgap (by simp [hzero])
    have hgap_val : padicValNat p gap.natAbs = 0 :=
      padicValNat.eq_zero_of_not_dvd (p := p) (n := gap.natAbs) hgap
    calc
      padicValNat p (gap * beam).natAbs
          = padicValNat p (gap.natAbs * beam.natAbs) := by
              rw [Int.natAbs_mul]
      _ = padicValNat p gap.natAbs + padicValNat p beam.natAbs := by
              exact padicValNat.mul hgap_ne hbeam
      _ = padicValNat p beam.natAbs := by
              simp [hgap_val]

/-- In an FLT-style primitive context, a prime dividing the Beam but not the
    degree has product valuation equal to the Beam valuation. -/
theorem flt_padicValNat_product_eq_beam_of_beam_prime
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    padicValNat p (powerGap x z * powerBeam d x z).natAbs =
      padicValNat p (powerBeam d x z).natAbs := by
  have hgap : ¬ p ∣ (powerGap x z).natAbs :=
    flt_beam_prime_not_dvd_gap_of_not_dvd_d
      (d := d) (p := p) (x := x) (y := y) (z := z) hd hcop hflt hpnd hbeam
  exact padicValNat_natAbs_mul_eq_right_of_not_dvd_left
    (p := p) (gap := powerGap x z) (beam := powerBeam d x z) hp hgap

/-- Symmetric version of `flt_padicValNat_product_eq_beam_of_beam_prime`. -/
theorem flt_padicValNat_product_eq_beam_of_beam_prime_symm
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z y = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d y z).natAbs) :
    padicValNat p (powerGap y z * powerBeam d y z).natAbs =
      padicValNat p (powerBeam d y z).natAbs := by
  have hgap : ¬ p ∣ (powerGap y z).natAbs :=
    flt_beam_prime_not_dvd_gap_of_not_dvd_d_symm
      (d := d) (p := p) (x := x) (y := y) (z := z) hd hcop hflt hpnd hbeam
  exact padicValNat_natAbs_mul_eq_right_of_not_dvd_left
    (p := p) (gap := powerGap y z) (beam := powerBeam d y z) hp hgap

/-! ## Power Valuation Bridge -/

/-- In an FLT-style primitive context, a prime dividing the Beam but not the
    degree forces the Beam valuation to be a multiple of `d`. -/
theorem flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs) :
    padicValNat p (powerBeam d x z).natAbs =
      d * padicValNat p y.natAbs := by
  have hprod : y ^ d = powerGap x z * powerBeam d x z :=
    flt_eq_forces_powerGapBeam d x y z hflt
  have hval_prod :
      padicValNat p (powerGap x z * powerBeam d x z).natAbs =
        padicValNat p (powerBeam d x z).natAbs :=
    flt_padicValNat_product_eq_beam_of_beam_prime
      (d := d) (p := p) (x := x) (y := y) (z := z) hd hcop hflt hp hpnd hbeam
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    padicValNat p (powerBeam d x z).natAbs
        = padicValNat p (powerGap x z * powerBeam d x z).natAbs := hval_prod.symm
    _ = padicValNat p (y ^ d).natAbs := by rw [← hprod]
    _ = padicValNat p (y.natAbs ^ d) := by rw [Int.natAbs_pow]
    _ = d * padicValNat p y.natAbs := by
          exact padicValNat.pow d hy_ne

/-- Symmetric version of `flt_padicValNat_beam_eq_d_mul_y_of_beam_prime`. -/
theorem flt_padicValNat_beam_eq_d_mul_x_of_beam_prime_symm
    {d p : ℕ} {x y z : ℤ}
    (hd : 1 ≤ d)
    (hcop : Int.gcd z y = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hx_ne : x.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d y z).natAbs) :
    padicValNat p (powerBeam d y z).natAbs =
      d * padicValNat p x.natAbs := by
  have hprod : x ^ d = powerGap y z * powerBeam d y z :=
    flt_eq_forces_powerGapBeam_symm d x y z hflt
  have hval_prod :
      padicValNat p (powerGap y z * powerBeam d y z).natAbs =
        padicValNat p (powerBeam d y z).natAbs :=
    flt_padicValNat_product_eq_beam_of_beam_prime_symm
      (d := d) (p := p) (x := x) (y := y) (z := z) hd hcop hflt hp hpnd hbeam
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    padicValNat p (powerBeam d y z).natAbs
        = padicValNat p (powerGap y z * powerBeam d y z).natAbs := hval_prod.symm
    _ = padicValNat p (x ^ d).natAbs := by rw [← hprod]
    _ = padicValNat p (x.natAbs ^ d) := by rw [Int.natAbs_pow]
    _ = d * padicValNat p x.natAbs := by
          exact padicValNat.pow d hx_ne

/-! ## Valuation Contradiction Bridge -/

/-- A positive valuation bounded by one cannot be a multiple of `d ≥ 2`. -/
theorem padicValNat_eq_d_mul_and_le_one_contradiction
    {d v k : ℕ}
    (hd : 2 ≤ d)
    (hv_pos : 1 ≤ v)
    (hv_le_one : v ≤ 1)
    (hv_eq : v = d * k) :
    False := by
  have hv_one : v = 1 := by omega
  have hk_pos : 1 ≤ k := by
    by_contra hk_not
    have hk_zero : k = 0 := by omega
    have hv_zero : v = 0 := by
      rw [hv_eq, hk_zero]
      simp
    omega
  have htwo_le : 2 ≤ d * k := by
    calc
      2 ≤ d := hd
      _ ≤ d * k := by
        exact Nat.le_mul_of_pos_right d hk_pos
  omega

/-- If a nonzero natural number is divisible by a prime, its p-adic valuation is positive. -/
theorem one_le_padicValNat_of_prime_dvd
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hn : n ≠ 0)
    (hdvd : p ∣ n) :
    1 ≤ padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_pow : p ^ 1 ∣ n := by
    simpa using hdvd
  exact (@padicValNat_dvd_iff_le p (Fact.mk hp) n 1 hn).mp hp_pow

/-- A Beam prime with valuation at most one contradicts the FLT power valuation
    constraint when `2 ≤ d`. -/
theorem flt_beam_prime_val_le_one_contradiction
    {d p : ℕ} {x y z : ℤ}
    (hd1 : 1 ≤ d)
    (hd2 : 2 ≤ d)
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d x z).natAbs)
    (hbeam_ne : (powerBeam d x z).natAbs ≠ 0)
    (hbeam_le_one : padicValNat p (powerBeam d x z).natAbs ≤ 1) :
    False := by
  have hval_eq :
      padicValNat p (powerBeam d x z).natAbs =
        d * padicValNat p y.natAbs :=
    flt_padicValNat_beam_eq_d_mul_y_of_beam_prime
      (d := d) (p := p) (x := x) (y := y) (z := z)
      hd1 hcop hflt hy_ne hp hpnd hbeam
  have hval_pos : 1 ≤ padicValNat p (powerBeam d x z).natAbs :=
    one_le_padicValNat_of_prime_dvd hp hbeam_ne hbeam
  exact padicValNat_eq_d_mul_and_le_one_contradiction
    hd2 hval_pos hbeam_le_one hval_eq

/-- Symmetric version of `flt_beam_prime_val_le_one_contradiction`. -/
theorem flt_beam_prime_val_le_one_contradiction_symm
    {d p : ℕ} {x y z : ℤ}
    (hd1 : 1 ≤ d)
    (hd2 : 2 ≤ d)
    (hcop : Int.gcd z y = 1)
    (hflt : x ^ d + y ^ d = z ^ d)
    (hx_ne : x.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d)
    (hbeam : p ∣ (powerBeam d y z).natAbs)
    (hbeam_ne : (powerBeam d y z).natAbs ≠ 0)
    (hbeam_le_one : padicValNat p (powerBeam d y z).natAbs ≤ 1) :
    False := by
  have hval_eq :
      padicValNat p (powerBeam d y z).natAbs =
        d * padicValNat p x.natAbs :=
    flt_padicValNat_beam_eq_d_mul_x_of_beam_prime_symm
      (d := d) (p := p) (x := x) (y := y) (z := z)
      hd1 hcop hflt hx_ne hp hpnd hbeam
  have hval_pos : 1 ≤ padicValNat p (powerBeam d y z).natAbs :=
    one_le_padicValNat_of_prime_dvd hp hbeam_ne hbeam
  exact padicValNat_eq_d_mul_and_le_one_contradiction
    hd2 hval_pos hbeam_le_one hval_eq

end DkMath.CosmicFormula.PowerGapBeam
