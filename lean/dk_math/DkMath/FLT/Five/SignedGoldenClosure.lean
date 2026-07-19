/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSector

#print "file: DkMath.FLT.Five.SignedGoldenClosure"

namespace DkMath.FLT.Five

/--
The exact remaining zero-sector Diophantine proposition after the certified
primitive and tenth-power splits.
-/
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
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

/-- The exact quartic/tenth-power proposition is sufficient for the zero sector. -/
theorem signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion := by
  intro u v w p gamma hbeta
  exact hArithmetic gamma.fst gamma.snd
    p.exceptional.powerSplit.a p.exceptional.powerSplit.b
    p.exceptional.powerSplit.a_pos p.exceptional.powerSplit.b_pos
    p.exceptional.powerSplit.coprime_a_b p.five_not_dvd_b
    (p.zeroSector_gamma_norm_eq_or_eq_neg hbeta)
    (p.zeroSector_snd_factor_eq hbeta)
    (p.zeroSector_coprime_coords hbeta)
    (p.zeroSector_tenthPower_split hbeta)

/-- Every primitive packet has a routed gap after possibly swapping its left inputs. -/
theorem CounterexamplePack.branchB_orientation
    {x y z : ℕ} (p : CounterexamplePack x y z) :
    ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x := by
  by_cases hyGap : 5 ∣ z - y
  · right
    intro hxGap
    have hyz : y ≤ z := (right_lt_of_fermat5Equation p.hx p.hEq).le
    have hxz : x ≤ z := by
      have hEqSwap : Fermat5Equation y x z := by
        simpa [Fermat5Equation, Nat.add_comm] using p.hEq
      exact (right_lt_of_fermat5Equation p.hy hEqSwap).le
    have hbody : Body5 (z - y) y = x ^ 5 :=
      body5_eq_fifth_power_of_fermat hyz p.hEq
    have h5xPow : 5 ∣ x ^ 5 := by
      rw [← hbody]
      exact dvd_mul_of_dvd_left hyGap _
    have h5x : 5 ∣ x :=
      (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5xPow
    have h5z : 5 ∣ z := by
      rw [← Nat.sub_add_cancel hxz]
      exact dvd_add hxGap h5x
    have h5y : 5 ∣ y := by
      rcases h5z with ⟨m, hm⟩
      rcases hyGap with ⟨n, hn⟩
      use m - n
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega) h5x h5y) p.hxy
  · exact Or.inl hyGap

/-- Refuters for both routed orientations refute every primitive packet. -/
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False

/-- The unit-times-fifth-power exclusion closes every primitive packet unconditionally. -/
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap

/-- The two exact remaining arithmetic inputs suffice for all primitive packets. -/
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))

/-- Arbitrary positive solutions can be reduced to a primitive counterexample packet. -/
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z' := by
  let d := Nat.gcd x y
  let x' := x / d
  let y' := y / d
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_left y hx
  have hdx : d ∣ x := Nat.gcd_dvd_left x y
  have hdy : d ∣ y := Nat.gcd_dvd_right x y
  have hd5z5 : d ^ 5 ∣ z ^ 5 := by
    have hd5x5 : d ^ 5 ∣ x ^ 5 := pow_dvd_pow_of_dvd hdx 5
    have hd5y5 : d ^ 5 ∣ y ^ 5 := pow_dvd_pow_of_dvd hdy 5
    rw [← hEq]
    exact dvd_add hd5x5 hd5y5
  have hdz : d ∣ z := by
    have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd (a := d ^ 5) (b := z)
      (by decide : 5 ≠ 0)).mp hd5z5
    simpa using hroot
  let z' := z / d
  have hxEq : d * x' = x := Nat.mul_div_cancel' hdx
  have hyEq : d * y' = y := Nat.mul_div_cancel' hdy
  have hzEq : d * z' = z := Nat.mul_div_cancel' hdz
  have hxPos : 0 < x' := Nat.div_pos (Nat.le_of_dvd hx hdx) hdPos
  have hyPos : 0 < y' := Nat.div_pos (Nat.le_of_dvd hy hdy) hdPos
  have hzPos : 0 < z' := Nat.div_pos (Nat.le_of_dvd hz hdz) hdPos
  have hcop : Nat.Coprime x' y' := by
    exact Nat.coprime_div_gcd_div_gcd hdPos
  have hEq' : Fermat5Equation x' y' z' := by
    have hscaled : d ^ 5 * (x' ^ 5 + y' ^ 5) = d ^ 5 * z' ^ 5 := by
      calc
        d ^ 5 * (x' ^ 5 + y' ^ 5) = (d * x') ^ 5 + (d * y') ^ 5 := by ring
        _ = x ^ 5 + y ^ 5 := by rw [hxEq, hyEq]
        _ = z ^ 5 := hEq
        _ = (d * z') ^ 5 := by rw [hzEq]
        _ = d ^ 5 * z' ^ 5 := by ring
    unfold Fermat5Equation
    exact Nat.mul_left_cancel (pow_pos hdPos 5) hscaled
  exact ⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩

/-- A primitive-packet refuter is sufficient for all positive Fermat-five data. -/
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z

theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p

/-- The two exact arithmetic inputs suffice for the full positive target. -/
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)

end DkMath.FLT.Five
