/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSector

/-!
# Certified inversion of the zero-sector equation

Set `X = 2*r+s`, `U = X^2+5*s^2`, `W = 4*d^5`, and
`A = U-W`, `B = U+W`. The diagonal quartic identity and the tenth-power split
give `A*B = 4*Q^5` for `Q = 5^5*c^8`, while `B = A+8*d^5` records their exact
separation. `GoldenZeroSectorCandidate` retains every positivity, coprimality,
norm, and source equation needed to certify this transformation.
-/

#print "file: DkMath.FLT.Five.SignedGoldenZeroSectorInversion"

namespace DkMath.FLT.Five

/-- The diagonal coordinate `X = 2*r+s`. -/
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s

/-- The positive quadratic quantity `U = X^2+5*s^2`. -/
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2

/-- The quantity `W = 4*d^5` supplied by `|H(r,s)| = d^10`. -/
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5

/-- The lower inversion factor `A = U-W`. -/
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d

/-- The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`. -/
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8

/-- Exact diagonalization of the quartic second-coordinate factor. -/
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorX
  ring

/-- The quartic second-coordinate factor is nonnegative for all integer inputs. -/
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  have hdiag : 0 ≤
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
    positivity
  have hident := sixteen_mul_goldenFifthSndFactor_eq r s
  nlinarith

/--
All raw hypotheses supplied by the zero-sector arithmetic receiver, including the
chosen tenth-power split.  No norm or coprimality provenance is discarded.
-/
structure GoldenZeroSectorCandidate where
  r : ℤ
  s : ℤ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  five_not_dvd_b : ¬ 5 ∣ b
  norm_eq_or_eq_neg :
    goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)
  product_eq :
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10
  coprime_coords : Nat.Coprime r.natAbs s.natAbs
  s_natAbs_eq : s.natAbs = 5 ^ 6 * c ^ 10
  H_natAbs_eq : (goldenFifthSndFactor r s).natAbs = d ^ 10

/-- Direct constructor in the argument order used by the arithmetic receiver. -/
def goldenZeroSectorCandidate_of_raw
    (r s : ℤ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (h5b : ¬ 5 ∣ b)
    (hNorm : goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
      goldenNorm ⟨r, s⟩ = -(b : ℤ))
    (hProduct : s * goldenFifthSndFactor r s =
      -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10)
    (hrs : Nat.Coprime r.natAbs s.natAbs)
    (c d : ℕ)
    (hsAbs : s.natAbs = 5 ^ 6 * c ^ 10)
    (hHAbs : (goldenFifthSndFactor r s).natAbs = d ^ 10) :
    GoldenZeroSectorCandidate where
  r := r
  s := s
  a := a
  b := b
  c := c
  d := d
  a_pos := ha
  b_pos := hb
  coprime_a_b := hab
  five_not_dvd_b := h5b
  norm_eq_or_eq_neg := hNorm
  product_eq := hProduct
  coprime_coords := hrs
  s_natAbs_eq := hsAbs
  H_natAbs_eq := hHAbs

/-- Primitive coordinates make the visible coordinate coprime to its quartic. -/
theorem coprime_natAbs_goldenFifthSndFactor_of_coprime
    (r s : ℤ) (hrs : Nat.Coprime r.natAbs s.natAbs) :
    Nat.Coprime s.natAbs (goldenFifthSndFactor r s).natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqs, hqH⟩
  have hqsZ : (q : ℤ) ∣ s := Int.natCast_dvd.mpr hqs
  have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor r s :=
    Int.natCast_dvd.mpr hqH
  have hqR4 : (q : ℤ) ∣ r ^ 4 := by
    have htail : (q : ℤ) ∣ goldenFifthSndFactor r s - r ^ 4 := by
      rcases hqsZ with ⟨k, hk⟩
      refine ⟨k * (2 * r ^ 3 + 4 * r ^ 2 * s +
        3 * r * s ^ 2 + s ^ 3), ?_⟩
      simp only [goldenFifthSndFactor]
      rw [hk]
      ring
    convert dvd_sub hqHZ htail using 1
    all_goals first | ring | rfl
  have hqr4 : q ∣ r.natAbs ^ 4 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
  have hqr : q ∣ r.natAbs := hqPrime.dvd_of_dvd_pow hqr4
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs) hrs

namespace GoldenZeroSectorCandidate

/-- The signed product in every candidate is strictly negative. -/
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)

/-- The quartic factor in a zero-sector candidate is strictly positive. -/
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s := by
  have hnonneg := goldenFifthSndFactor_nonneg p.r p.s
  have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
    intro hzero
    have hpneg := p.product_neg
    rw [hzero, mul_zero] at hpneg
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The visible zero-sector coordinate has the forced negative sign. -/
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  rcases mul_neg_iff.mp p.product_neg with h | h
  · exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
  · exact h.1

/-- The tenth-power base in the visible coordinate is nonzero. -/
theorem c_pos (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  by_contra hc
  have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
  have hsAbsZero : p.s.natAbs = 0 := by
    simpa [hc0] using p.s_natAbs_eq
  have hs0 : p.s = 0 := Int.natAbs_eq_zero.mp hsAbsZero
  have hsneg := p.s_neg
  omega

/-- The tenth-power base in the quartic factor is nonzero. -/
theorem d_pos (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  by_contra hd
  have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
  have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
    simpa [hd0] using p.H_natAbs_eq
  have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
    Int.natAbs_eq_zero.mp hHAbsZero
  have hHpos := p.H_pos
  omega

/-- Exact sign removal for the visible coordinate. -/
theorem s_eq_neg_five_pow_mul_tenth (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10) := by
  have habs : (p.s.natAbs : ℤ) =
      (5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10 := by
    exact_mod_cast p.s_natAbs_eq
  have hsabs : (p.s.natAbs : ℤ) = -p.s :=
    Int.ofNat_natAbs_of_nonpos p.s_neg.le
  linarith

/-- Exact sign removal for the positive quartic factor. -/
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  have habs : ((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
      (p.d : ℤ) ^ 10 := by
    exact_mod_cast p.H_natAbs_eq
  rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs
  exact habs

/-- Natural absolute-value form of the signed product equation. -/
theorem natAbs_product_eq (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, pow_succ] using h

/-- The original tenth-power base is exactly the product of the split bases. -/
theorem a_eq_c_mul_d (p : GoldenZeroSectorCandidate) : p.a = p.c * p.d := by
  have hprod := p.natAbs_product_eq
  rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod
  have hpows : (p.c * p.d) ^ 10 = p.a ^ 10 := by
    apply Nat.mul_left_cancel (by positivity : 0 < 5 ^ 6)
    calc
      5 ^ 6 * (p.c * p.d) ^ 10 =
          (5 ^ 6 * p.c ^ 10) * p.d ^ 10 := by ring
      _ = 5 ^ 6 * p.a ^ 10 := hprod
  exact (Nat.pow_left_injective (by norm_num : 10 ≠ 0) hpows).symm

/-- The two split tenth-power bases inherit coprimality. -/
theorem coprime_c_d (p : GoldenZeroSectorCandidate) :
    Nat.Coprime p.c p.d := by
  have hcop := coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.r p.s p.coprime_coords
  have hc : p.c ∣ p.s.natAbs := by
    rw [p.s_natAbs_eq]
    exact dvd_mul_of_dvd_right (dvd_pow_self p.c (by decide : 10 ≠ 0)) _
  have hd : p.d ∣ (goldenFifthSndFactor p.r p.s).natAbs := by
    rw [p.H_natAbs_eq]
    exact dvd_pow_self p.d (by decide : 10 ≠ 0)
  exact (hcop.of_dvd_left hc).of_dvd_right hd

/-- The quartic factor retains the packet's exclusion of the prime five. -/
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq
    (⟨p.r, p.s⟩ : GoldenInt)
  have hnormSq : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ ^ 2 := by
    convert dvd_sub hH hdiff using 1
    all_goals first | ring | rfl
  have hnorm : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  apply p.five_not_dvd_b
  rcases p.norm_eq_or_eq_neg with h | h
  · rw [h] at hnorm
    exact_mod_cast hnorm
  · rw [h] at hnorm
    exact_mod_cast (Int.dvd_neg.mp hnorm)

/-- The quartic tenth-power base is not divisible by five. -/
theorem five_not_dvd_d (p : GoldenZeroSectorCandidate) : ¬ 5 ∣ p.d := by
  intro h5d
  apply p.five_not_dvd_H
  rw [p.H_eq_tenth]
  exact dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)

/-- The primitive-coordinate quartic is odd. -/
theorem H_odd (p : GoldenZeroSectorCandidate) :
    Odd (goldenFifthSndFactor p.r p.s) := by
  have hterm2 : Even (2 * p.r ^ 3 * p.s) :=
    (even_two.mul_right (p.r ^ 3)).mul_right p.s
  have hfour : Even (4 : ℤ) := ⟨2, by norm_num⟩
  have hterm3 : Even (4 * p.r ^ 2 * p.s ^ 2) :=
    (hfour.mul_right (p.r ^ 2)).mul_right (p.s ^ 2)
  rcases Int.even_or_odd p.r with hr | hr <;>
    rcases Int.even_or_odd p.s with hs | hs
  · exfalso
    have hrNat : Even p.r.natAbs := hr.natAbs
    have hsNat : Even p.s.natAbs := hs.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega)
      hrNat.two_dvd hsNat.two_dvd) p.coprime_coords
  · unfold goldenFifthSndFactor
    have hterm1 : Even (p.r ^ 4) :=
      hr.pow_of_ne_zero (by decide : 4 ≠ 0)
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hr.mul_left 3).mul_right (p.s ^ 3)
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add hterm2).add hterm3).add hterm4).add_odd hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hs.pow_of_ne_zero (by decide : 3 ≠ 0)).mul_left (3 * p.r)
    have hterm5 : Even (p.s ^ 4) :=
      hs.pow_of_ne_zero (by decide : 4 ≠ 0)
    exact (((hterm1.add_even hterm2).add_even hterm3).add_even hterm4).add_even hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hthree : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have hterm4 : Odd (3 * p.r * p.s ^ 3) :=
      (hthree.mul hr).mul hs.pow
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add_even hterm2).add_even hterm3).add_odd hterm4).add_odd hterm5

/-- Consequently the tenth-power base `d` is odd. -/
theorem d_odd (p : GoldenZeroSectorCandidate) : Odd p.d := by
  have hH := p.H_odd
  rw [p.H_eq_tenth] at hH
  have hdZ : Odd (p.d : ℤ) :=
    (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
  exact_mod_cast hdZ

/-- The diagonal sum is nonnegative independently of the candidate hypotheses. -/
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  positivity

/-- The reconstructed square coordinate is retained exactly. -/
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 := by
  unfold zeroSectorU
  ring

/-- The diagonal quartic identity becomes a difference of two squares. -/
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4 := by
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq p.r p.s
  rw [p.H_eq_tenth] at hdiag
  unfold zeroSectorU zeroSectorW
  calc
    (zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2) ^ 2 -
        (4 * (p.d : ℤ) ^ 5) ^ 2 =
        (zeroSectorX p.r p.s ^ 4 +
          10 * zeroSectorX p.r p.s ^ 2 * p.s ^ 2 +
          5 * p.s ^ 4 - 16 * (p.d : ℤ) ^ 10) +
          20 * p.s ^ 4 := by ring
    _ = 20 * p.s ^ 4 := by rw [← hdiag]; ring

/-- Before sign removal, the two inversion factors multiply to `20*s^4`. -/
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 := by
      unfold zeroSectorA zeroSectorB
      ring
    _ = 20 * p.s ^ 4 := p.discriminant_eq

/-- Central fifth-power product of the positive inversion factors. -/
theorem factor_product (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        20 * p.s ^ 4 := p.factor_product_twenty
    _ = 4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
      rw [p.s_eq_neg_five_pow_mul_tenth]
      unfold zeroSectorQ
      push_cast
      ring

/-- Exact distance between the upper and lower inversion factors. -/
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring

/-- Exact sum of the two inversion factors. -/
theorem factor_sum (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d + zeroSectorB p.r p.s p.d =
      2 * zeroSectorU p.r p.s := by
  unfold zeroSectorA zeroSectorB
  ring

/-- The tenth-power square root contribution is strictly positive. -/
theorem W_pos (p : GoldenZeroSectorCandidate) : 0 < zeroSectorW p.d := by
  unfold zeroSectorW
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity

/-- The upper inversion factor is strictly positive. -/
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]

/-- The lower inversion factor is strictly positive. -/
theorem A_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorA p.r p.s p.d := by
  have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
  have hprod : 0 <
      zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d := by
    rw [p.factor_product_twenty]
    positivity
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.1
  · exact (not_lt_of_ge p.B_pos.le h.2).elim

/-- The two factors occur in their forced strict order. -/
theorem A_lt_B (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d < zeroSectorB p.r p.s p.d := by
  have hdiff := p.factor_difference
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
  linarith

/-- Natural representative of the positive lower factor. -/
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs

/-- Natural representative of the positive upper factor. -/
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs

/-- Cast equation for the positive lower natural representative. -/
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le

/-- Cast equation for the positive upper natural representative. -/
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le

/-- The natural representatives are both positive. -/
theorem A0_pos (p : GoldenZeroSectorCandidate) : 0 < p.A0 := by
  by_contra hpos
  have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.A0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hApos := p.A_pos
  omega

theorem B0_pos (p : GoldenZeroSectorCandidate) : 0 < p.B0 := by
  by_contra hpos
  have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.B0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hBpos := p.B_pos
  omega

/-- Natural product identity inherited from the positive integer factors. -/
theorem A0_mul_B0 (p : GoldenZeroSectorCandidate) :
    p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5 := by
  have hprod := p.factor_product
  rw [← p.A0_cast, ← p.B0_cast] at hprod
  exact_mod_cast hprod

/-- Additive natural form of the factor difference, avoiding subtraction. -/
theorem B0_eq_A0_add (p : GoldenZeroSectorCandidate) :
    p.B0 = p.A0 + 8 * p.d ^ 5 := by
  have hdiff := p.factor_difference
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith
  exact_mod_cast hcasts

end GoldenZeroSectorCandidate

/--
Certified output of zero-sector inversion.  It keeps the complete source candidate
and all signs, ownership, factor identities, and positivity facts needed downstream.
-/
structure GoldenZeroSectorInversionPacket where
  source : GoldenZeroSectorCandidate
  H_pos : 0 < goldenFifthSndFactor source.r source.s
  s_neg : source.s < 0
  c_pos : 0 < source.c
  d_pos : 0 < source.d
  s_eq : source.s = -((5 : ℤ) ^ 6 * (source.c : ℤ) ^ 10)
  H_eq : goldenFifthSndFactor source.r source.s = (source.d : ℤ) ^ 10
  a_eq : source.a = source.c * source.d
  coprime_c_d : Nat.Coprime source.c source.d
  five_not_dvd_d : ¬ 5 ∣ source.d
  d_odd : Odd source.d
  discriminant_eq :
    zeroSectorU source.r source.s ^ 2 - zeroSectorW source.d ^ 2 =
      20 * source.s ^ 4
  factor_product :
    source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
  factor_difference :
    source.B0 = source.A0 + 8 * source.d ^ 5
  factor_sum :
    zeroSectorA source.r source.s source.d +
        zeroSectorB source.r source.s source.d =
      2 * zeroSectorU source.r source.s
  square_reconstruction :
    zeroSectorU source.r source.s - 5 * source.s ^ 2 =
      zeroSectorX source.r source.s ^ 2
  W_pos : 0 < zeroSectorW source.d
  A_pos : 0 < zeroSectorA source.r source.s source.d
  A_lt_B :
    zeroSectorA source.r source.s source.d <
      zeroSectorB source.r source.s source.d
  B_pos : 0 < zeroSectorB source.r source.s source.d
  A0_cast : (source.A0 : ℤ) = zeroSectorA source.r source.s source.d
  B0_cast : (source.B0 : ℤ) = zeroSectorB source.r source.s source.d
  A0_pos : 0 < source.A0
  B0_pos : 0 < source.B0

/-- Every raw zero-sector candidate deterministically yields its inversion packet. -/
def goldenZeroSectorInversionPacket (p : GoldenZeroSectorCandidate) :
    GoldenZeroSectorInversionPacket where
  source := p
  H_pos := p.H_pos
  s_neg := p.s_neg
  c_pos := p.c_pos
  d_pos := p.d_pos
  s_eq := p.s_eq_neg_five_pow_mul_tenth
  H_eq := p.H_eq_tenth
  a_eq := p.a_eq_c_mul_d
  coprime_c_d := p.coprime_c_d
  five_not_dvd_d := p.five_not_dvd_d
  d_odd := p.d_odd
  discriminant_eq := p.discriminant_eq
  factor_product := p.A0_mul_B0
  factor_difference := p.B0_eq_A0_add
  factor_sum := p.factor_sum
  square_reconstruction := p.square_reconstruction
  W_pos := p.W_pos
  A_pos := p.A_pos
  A_lt_B := p.A_lt_B
  B_pos := p.B_pos
  A0_cast := p.A0_cast
  B0_cast := p.B0_cast
  A0_pos := p.A0_pos
  B0_pos := p.B0_pos

end DkMath.FLT.Five
