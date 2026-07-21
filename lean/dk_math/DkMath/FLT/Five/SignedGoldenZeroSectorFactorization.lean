/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSectorInversion

/-!
# Exact factor packets after zero-sector inversion

The positive factors `A0` and `B0` are split according to their two-adic
content. The odd branch gives the `(2,2)` allocation; the even branches give
`(8,16)` or `(16,8)`. Each packet retains its source candidate, exact product,
exact difference, coprimality after removing powers of two, and fifth-power
factor data. The odd branch also exposes a modulo-eleven channel, but that
channel is recorded as structure rather than asserted to be a contradiction.
-/

#print "file: DkMath.FLT.Five.SignedGoldenZeroSectorFactorization"

namespace DkMath.FLT.Five

/-- An odd factor cannot share any prime with a second factor once common odd
prime divisors have been excluded. -/
private theorem coprime_of_odd_of_no_common_odd_prime
    {m n : ℕ} (hm : Odd m)
    (hodd : ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) :
    Nat.Coprime m n := by
  apply Nat.coprime_of_dvd
  intro q hq hqm hqn
  by_cases hq2 : q = 2
  · subst q
    have hmEven : Even m := even_iff_two_dvd.mpr hqm
    exact (Nat.not_even_iff_odd.mpr hm) hmEven
  · exact hodd q hq hq2 hqm hqn

private theorem exists_eq_two_mul_odd_of_two_dvd_not_four_dvd
    {n : ℕ} (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    ∃ m : ℕ, n = 2 * m ∧ Odd m := by
  rcases h2 with ⟨m, hm⟩
  refine ⟨m, hm, Nat.not_even_iff_odd.mp ?_⟩
  rw [even_iff_two_dvd]
  intro h2m
  rcases h2m with ⟨k, hk⟩
  apply h4
  refine ⟨k, ?_⟩
  omega

/-- The positive inversion factors have no common odd prime divisor. -/
theorem GoldenZeroSectorInversionPacket.no_common_odd_prime
    (p : GoldenZeroSectorInversionPacket)
    (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hqA : q ∣ p.source.A0) (hqB : q ∣ p.source.B0) : False := by
  have hqDiff : q ∣ 8 * p.source.d ^ 5 := by
    have hqAZ : (q : ℤ) ∣ p.source.A0 := Int.natCast_dvd.mpr hqA
    have hqBZ : (q : ℤ) ∣ p.source.B0 := Int.natCast_dvd.mpr hqB
    have hqDiffZ : (q : ℤ) ∣
        (p.source.B0 : ℤ) - (p.source.A0 : ℤ) :=
      dvd_sub hqBZ hqAZ
    have hdiffZ : (p.source.B0 : ℤ) - (p.source.A0 : ℤ) =
        8 * (p.source.d : ℤ) ^ 5 := by
      have hcast : (p.source.B0 : ℤ) =
          (p.source.A0 : ℤ) + 8 * (p.source.d : ℤ) ^ 5 := by
        exact_mod_cast p.factor_difference
      linarith
    rw [hdiffZ] at hqDiffZ
    exact Int.natCast_dvd.mp hqDiffZ
  have hqd : q ∣ p.source.d := by
    rcases hq.dvd_mul.mp hqDiff with hq8 | hqd5
    · have hq2pow : q ∣ 2 ^ 3 := by simpa using hq8
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqd5
  have hqMass : q ∣ zeroSectorQ p.source.c := by
    have hqProduct : q ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
      rw [← p.factor_product]
      exact dvd_mul_of_dvd_left hqA _
    rcases hq.dvd_mul.mp hqProduct with hq4 | hqQ5
    · have hq2pow : q ∣ 2 ^ 2 := by simpa using hq4
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqQ5
  unfold zeroSectorQ at hqMass
  rcases hq.dvd_mul.mp hqMass with hq5pow | hqcpow
  · have hq5 : q ∣ 5 := hq.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
    exact p.five_not_dvd_d (hqeq ▸ hqd)
  · have hqc : q ∣ p.source.c := hq.dvd_of_dvd_pow hqcpow
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqc hqd) p.coprime_c_d

/-- In the odd-`c` branch, each inversion factor has exactly one factor of two. -/
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 2 * A1 ∧ Odd A1 ∧
      p.source.B0 = 2 * B1 ∧ Odd B1 := by
  have hQodd : Odd (zeroSectorQ p.source.c) := by
    unfold zeroSectorQ
    exact (show Odd (5 ^ 5) by norm_num).mul hc.pow
  have hRhsNotEight : ¬ 8 ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
    intro h8
    rcases h8 with ⟨k, hk⟩
    have h2Q : 2 ∣ zeroSectorQ p.source.c ^ 5 := by
      refine ⟨k, ?_⟩
      omega
    exact hQodd.pow.not_two_dvd_nat h2Q
  have h2Product : 2 ∣ p.source.A0 * p.source.B0 := by
    rw [p.factor_product]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have h2Diff : 2 ∣ 8 * p.source.d ^ 5 := by
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hEven : 2 ∣ p.source.A0 ∧ 2 ∣ p.source.B0 := by
    rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2Product with hA | hB
    · exact ⟨hA, by rw [p.factor_difference]; exact dvd_add hA h2Diff⟩
    · have hsum : 2 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
        simpa [p.factor_difference] using hB
      exact ⟨(Nat.dvd_add_left h2Diff).mp hsum, hB⟩
  have hNotFourA : ¬ 4 ∣ p.source.A0 := by
    intro h4A
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have h4B : 4 ∣ p.source.B0 := by
      rw [p.factor_difference]
      exact dvd_add h4A h4Diff
    have h16Product : 16 ∣ p.source.A0 * p.source.B0 := by
      simpa using Nat.mul_dvd_mul h4A h4B
    have h8Product : 8 ∣ p.source.A0 * p.source.B0 :=
      (by norm_num : 8 ∣ 16).trans h16Product
    rw [p.factor_product] at h8Product
    exact hRhsNotEight h8Product
  have hNotFourB : ¬ 4 ∣ p.source.B0 := by
    intro h4B
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have hsum : 4 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
      simpa [p.factor_difference] using h4B
    have h4A : 4 ∣ p.source.A0 := (Nat.dvd_add_left h4Diff).mp hsum
    exact hNotFourA h4A
  obtain ⟨A1, hA, hAodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.1 hNotFourA
  obtain ⟨B1, hB, hBodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.2 hNotFourB
  exact ⟨A1, B1, hA, hAodd, hB, hBodd⟩

/-- The full fifth-power mass is coprime to the quartic tenth-power base. -/
theorem GoldenZeroSectorInversionPacket.coprime_Q_d
    (p : GoldenZeroSectorInversionPacket) :
    Nat.Coprime (zeroSectorQ p.source.c) p.source.d := by
  have h5d : Nat.Coprime 5 p.source.d :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
  unfold zeroSectorQ
  exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)

/-- Fifth powers modulo eleven are `0`, `1`, or `-1`. -/
theorem fifth_mod_eleven_cases (n : ℕ) :
    n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
  rw [Nat.pow_mod]
  generalize hr : n % 11 = r
  have hlt : r < 11 := by rw [← hr]; omega
  interval_cases r <;> norm_num

/-- The odd factor branch forces its fifth-power offset into the prime eleven. -/
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
  by_contra hd
  have he := fifth_mod_eleven_cases e
  have hd' := fifth_mod_eleven_cases d
  have hf := fifth_mod_eleven_cases f
  have hdmod : d ^ 5 % 11 ≠ 0 := by
    intro hz
    apply hd
    apply (by norm_num : Nat.Prime 11).dvd_of_dvd_pow
    exact Nat.dvd_of_mod_eq_zero hz
  have hm := congrArg (fun n : ℕ => n % 11) h
  omega

/-- The exhaustive two-adic branch label. -/
inductive GoldenZeroSectorFactorBranch
  | odd
  | evenLeftLow
  | evenRightLow
  deriving DecidableEq

/-- Exact factor data in the three two-adic branches.  The enclosing packet
retains the complete inversion source and hence its norm and square reconstruction. -/
inductive GoldenZeroSectorFactorData
    (p : GoldenZeroSectorInversionPacket) : Type
  | odd
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 2 * e ^ 5)
      (B_eq : p.source.B0 = 2 * f ^ 5)
      (ownership : e * f = zeroSectorQ p.source.c)
      (difference : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5)
  | evenLeftLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_even : Even f)
      (A_eq : p.source.A0 = 8 * e ^ 5)
      (B_eq : p.source.B0 = 16 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5)
  | evenRightLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_even : Even e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 16 * e ^ 5)
      (B_eq : p.source.B0 = 8 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5)

/-- Branch label of an exact factor datum. -/
def GoldenZeroSectorFactorData.branch
    {p : GoldenZeroSectorInversionPacket} :
    GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
  | .odd .. => .odd
  | .evenLeftLow .. => .evenLeftLow
  | .evenRightLow .. => .evenRightLow

/-- The odd branch exposes the forced eleven channel and excludes eleven from
every factor owned by `c`. -/
theorem GoldenZeroSectorFactorData.odd_eleven_channel
    {p : GoldenZeroSectorInversionPacket}
    (data : GoldenZeroSectorFactorData p)
    (hbranch : data.branch = .odd) :
    ∃ e f : ℕ,
      11 ∣ p.source.d ∧
      ¬ 11 ∣ p.source.c ∧
      ¬ 11 ∣ e ∧
      ¬ 11 ∣ f ∧
      ¬ 11 ∣ e * f := by
  cases data with
  | odd e f _ _ _ hefD _ _ _ _ _ hdiff =>
      have h11d : 11 ∣ p.source.d :=
        eleven_dvd_d_of_fifth_add_four_fifth hdiff
      have h11c : ¬ 11 ∣ p.source.c := by
        intro h11c
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11c h11d)
          p.coprime_c_d
      have h11ef : ¬ 11 ∣ e * f := by
        intro h11ef
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11ef h11d) hefD
      have h11e : ¬ 11 ∣ e := by
        intro h11e
        exact h11ef (dvd_mul_of_dvd_left h11e f)
      have h11f : ¬ 11 ∣ f := by
        intro h11f
        exact h11ef (dvd_mul_of_dvd_right h11f e)
      exact ⟨e, f, h11d, h11c, h11e, h11f, h11ef⟩
  | evenLeftLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
  | evenRightLow => simp [GoldenZeroSectorFactorData.branch] at hbranch

/-- Complete zero-sector factor packet. -/
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion

private theorem nonempty_odd_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  obtain ⟨A1, B1, hA, hAodd, hB, hBodd⟩ := p.odd_factor_halves hc
  have hcop : Nat.Coprime A1 B1 := by
    apply coprime_of_odd_of_no_common_odd_prime hAodd
    intro q hq hq2 hqA1 hqB1
    apply p.no_common_odd_prime q hq hq2
    · rw [hA]
      exact dvd_mul_of_dvd_right hqA1 2
    · rw [hB]
      exact dvd_mul_of_dvd_right hqB1 2
  have hred : A1 * B1 = zeroSectorQ p.source.c ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
    calc
      4 * (A1 * B1) = p.source.A0 * p.source.B0 := by
        rw [hA, hB]
        ring
      _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
  have hePos : 0 < e := by
    by_contra he0
    have : e = 0 := Nat.eq_zero_of_not_pos he0
    have hpos := p.A0_pos
    rw [hA, he, this] at hpos
    norm_num at hpos
  have hfPos : 0 < f := by
    by_contra hf0
    have : f = 0 := Nat.eq_zero_of_not_pos hf0
    have hpos := p.B0_pos
    rw [hB, hf, this] at hpos
    norm_num at hpos
  have hef : Nat.Coprime e f := by
    have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
      simpa [he, hf] using hcop
    exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
      (dvd_pow_self f (by decide))
  have heodd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
  have hfodd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
  have hownership : e * f = zeroSectorQ p.source.c := by
    apply Nat.pow_left_injective (by decide : 5 ≠ 0)
    calc
      (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
      _ = A1 * B1 := by rw [← he, ← hf]
      _ = zeroSectorQ p.source.c ^ 5 := hred
  have hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5 := by
    have hfactorDifference := p.factor_difference
    rw [hA, hB, he, hf] at hfactorDifference
    omega
  exact ⟨.odd e f hePos hfPos hef (hownership ▸ p.coprime_Q_d)
    heodd hfodd (by rw [hA, he]) (by rw [hB, hf]) hownership hdiff⟩

/-- In the even-`c` branch, both inversion factors contain at least three
factors of two. -/
theorem GoldenZeroSectorInversionPacket.eight_dvd_factors
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0 := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  have hs8 : (8 : ℤ) ∣ p.source.s := by
    refine ⟨-((2 : ℤ) ^ 7 * 5 ^ 6 * (k : ℤ) ^ 10), ?_⟩
    rw [p.s_eq, hk]
    push_cast
    ring
  have hsEven : Even p.source.s :=
    even_iff_two_dvd.mpr ((by norm_num : (2 : ℤ) ∣ 8).trans hs8)
  have hrOdd : Odd p.source.r := by
    rw [← Int.natAbs_odd, ← Nat.not_even_iff_odd]
    intro hrEven
    have hsEvenAbs : Even p.source.s.natAbs := hsEven.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num)
      hrEven.two_dvd hsEvenAbs.two_dvd) p.source.coprime_coords
  rcases hrOdd with ⟨rh, hrh⟩
  rcases hs8 with ⟨st, hst⟩
  let z : ℤ := 2 * rh + 1 + 4 * st
  let u : ℤ := z ^ 2 + 80 * st ^ 2
  let w : ℤ := (p.source.d : ℤ) ^ 5
  have hzOdd : Odd z := by
    dsimp [z]
    exact (odd_two_mul_add_one rh).add_even (even_iff_two_dvd.mpr ⟨2 * st, by ring⟩)
  have huOdd : Odd u := by
    dsimp [u]
    exact hzOdd.pow.add_even (even_iff_two_dvd.mpr ⟨40 * st ^ 2, by ring⟩)
  have hwOdd : Odd w := by
    exact p.source.d_odd.natCast.pow
  have hAform : zeroSectorA p.source.r p.source.s p.source.d =
      4 * (u - w) := by
    simp only [zeroSectorA, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hBform : zeroSectorB p.source.r p.source.s p.source.d =
      4 * (u + w) := by
    simp only [zeroSectorB, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hEvenSub : Even (u - w) := by
    simp [Int.even_sub', huOdd, hwOdd]
  have hEvenAdd : Even (u + w) := huOdd.add_odd hwOdd
  have h8AZ : (8 : ℤ) ∣ zeroSectorA p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenSub with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hAform, ht]
    ring
  have h8BZ : (8 : ℤ) ∣ zeroSectorB p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenAdd with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hBform, ht]
    ring
  constructor
  · apply Int.natCast_dvd.mp
    exact h8AZ
  · apply Int.natCast_dvd.mp
    exact h8BZ

/-- After removing eight, the two even-branch factors have opposite parity. -/
theorem GoldenZeroSectorInversionPacket.even_factor_eighths
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 8 * A1 ∧ p.source.B0 = 8 * B1 ∧
      ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)) := by
  rcases p.eight_dvd_factors hc with ⟨h8A, h8B⟩
  rcases h8A with ⟨A1, hA⟩
  rcases h8B with ⟨B1, hB⟩
  have hdiff : B1 = A1 + p.source.d ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
    calc
      8 * B1 = p.source.B0 := hB.symm
      _ = p.source.A0 + 8 * p.source.d ^ 5 := p.factor_difference
      _ = 8 * (A1 + p.source.d ^ 5) := by rw [hA]; ring
  have hdOdd : Odd (p.source.d ^ 5) := p.source.d_odd.pow
  rcases Nat.even_or_odd A1 with hAeven | hAodd
  · have hBodd : Odd B1 := by rw [hdiff]; exact hAeven.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inr ⟨hAeven, hBodd⟩⟩
  · have hBeven : Even B1 := by rw [hdiff]; exact hAodd.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inl ⟨hAodd, hBeven⟩⟩

private theorem nonempty_even_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  let Q2 : ℕ := 5 ^ 5 * 2 ^ 7 * k ^ 8
  have hQ : zeroSectorQ p.source.c = 2 * Q2 := by
    unfold zeroSectorQ Q2
    rw [hk]
    ring
  have hQ2Even : Even Q2 := by
    rw [even_iff_two_dvd]
    dsimp [Q2]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (by norm_num : 2 ∣ 2 ^ 7) (5 ^ 5)) _
  obtain ⟨A1, B1, hA8, hB8, hparity⟩ := p.even_factor_eighths hc
  rcases hparity with ⟨hAodd, hBeven⟩ | ⟨hAeven, hBodd⟩
  · rcases even_iff_two_dvd.mp hBeven with ⟨B2, hB2⟩
    have hcop : Nat.Coprime A1 B2 := by
      apply coprime_of_odd_of_no_common_odd_prime hAodd
      intro q hq hq2 hqA1 hqB2
      apply p.no_common_odd_prime q hq hq2
      · rw [hA8]
        exact dvd_mul_of_dvd_right hqA1 8
      · rw [hB8, hB2]
        convert dvd_mul_of_dvd_right hqB2 16 using 1
        all_goals ring
    have hred : A1 * B2 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A1 * B2) = p.source.A0 * p.source.B0 := by
          rw [hA8, hB8, hB2]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hB2, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have heOdd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A1 * B2 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have hfEven : Even f := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact (heOdd.not_two_dvd_nat h2e).elim
      · exact even_iff_two_dvd.mpr h2f
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hB8, hB2, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenLeftLow e f hePos hfPos hef hefd heOdd hfEven
      (by rw [hA8, he]) (by rw [hB8, hB2, hf]; ring)
      hownership hdiff⟩
  · rcases even_iff_two_dvd.mp hAeven with ⟨A2, hA2⟩
    have hcop : Nat.Coprime A2 B1 := by
      have hcop' : Nat.Coprime B1 A2 := by
        apply coprime_of_odd_of_no_common_odd_prime hBodd
        intro q hq hq2 hqB1 hqA2
        apply p.no_common_odd_prime q hq hq2
        · rw [hA8, hA2]
          convert dvd_mul_of_dvd_right hqA2 16 using 1
          all_goals ring
        · rw [hB8]
          exact dvd_mul_of_dvd_right hqB1 8
      exact hcop'.symm
    have hred : A2 * B1 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A2 * B1) = p.source.A0 * p.source.B0 := by
          rw [hA8, hA2, hB8]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, hA2, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have hfOdd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A2 * B1 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have heEven : Even e := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact even_iff_two_dvd.mpr h2e
      · exact (hfOdd.not_two_dvd_nat h2f).elim
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hA2, hB8, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenRightLow e f hePos hfPos hef hefd heEven hfOdd
      (by rw [hA8, hA2, he]; ring) (by rw [hB8, hf])
      hownership hdiff⟩

private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc

/-- Chosen exact factor packet attached to an inversion packet. -/
noncomputable def goldenZeroSectorFactorPacket_of_inversion
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)

/-- Every raw zero-sector candidate produces one of the three exact factor branches. -/
theorem nonempty_goldenZeroSectorFactorPacket
    (p : GoldenZeroSectorCandidate) :
    Nonempty GoldenZeroSectorFactorPacket :=
  ⟨goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket p)⟩

/-- Exclusion of every certified exact factor branch. -/
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False

/-- The raw arithmetic contract, repeated here to preserve the acyclic dependency
direction from inversion to factorization. -/
abbrev GoldenZeroSectorFactorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False

/-- Excluding the three exact factor packets excludes every original zero-sector
candidate.  `SignedGoldenClosure` identifies this contract definitionally with its
public zero-sector arithmetic exclusion. -/
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
  rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
  let source := goldenZeroSectorCandidate_of_raw r s a b
    ha hb hab h5b hNorm hProduct hrs c d hsAbs hHAbs
  exact hFactor (goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket source))

end DkMath.FLT.Five
