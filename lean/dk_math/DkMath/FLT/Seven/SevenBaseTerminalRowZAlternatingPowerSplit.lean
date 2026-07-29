/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution
import DkMath.FLT.Seven.QuadraticConjugateCoprime

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The positive alternating factor in a sum of seventh powers. -/
def alternatingCyclotomicSeven (x y : ℕ) : ℕ :=
  (x ^ 7 + y ^ 7) / (x + y)

/-- The defining exact factorization of the alternating seventh cyclotomic
factor. -/
theorem add_mul_alternatingCyclotomicSeven (x y : ℕ) :
    (x + y) * alternatingCyclotomicSeven x y = x ^ 7 + y ^ 7 := by
  exact Nat.mul_div_cancel' (by
    simpa using (show Odd 7 by decide).nat_add_dvd_pow_add_pow x y)

/-- The natural alternating factor is the integer seventh cyclotomic kernel
at the signed endpoint pair `(x,-y)`. -/
theorem alternatingCyclotomicSeven_intCast (x y : ℕ) :
    (alternatingCyclotomicSeven x y : ℤ) =
      cyclotomicSeven (x : ℤ) (-(y : ℤ)) := by
  by_cases hsum : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    simp [hx, hy, alternatingCyclotomicSeven, cyclotomicSeven]
  · have hsumInt : ((x + y : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hsum
    apply mul_left_cancel₀ hsumInt
    calc
      ((x + y : ℕ) : ℤ) * (alternatingCyclotomicSeven x y : ℤ) =
          ((x ^ 7 + y ^ 7 : ℕ) : ℤ) := by
            exact_mod_cast add_mul_alternatingCyclotomicSeven x y
      _ = (x : ℤ) ^ 7 - (-(y : ℤ)) ^ 7 := by
            push_cast
            ring
      _ = ((x + y : ℕ) : ℤ) *
          cyclotomicSeven (x : ℤ) (-(y : ℤ)) := by
            simpa only [Int.natCast_add, sub_neg_eq_add] using
              seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven
                (x : ℤ) (-(y : ℤ))

/-- Expansion of the signed cyclotomic kernel around the sum endpoint.  It is
the alternating counterpart of `GN_seven_eq_gap_mul_add_seven_mul_y_pow_six`.
-/
theorem alternatingCyclotomicSeven_sum_expansion (x y : ℕ) :
    cyclotomicSeven (x : ℤ) (-(y : ℤ)) =
      ((x + y : ℕ) : ℤ) *
        (((x + y : ℕ) : ℤ) ^ 5
          - 7 * ((x + y : ℕ) : ℤ) ^ 4 * (y : ℤ)
          + 21 * ((x + y : ℕ) : ℤ) ^ 3 * (y : ℤ) ^ 2
          - 35 * ((x + y : ℕ) : ℤ) ^ 2 * (y : ℤ) ^ 3
          + 35 * ((x + y : ℕ) : ℤ) * (y : ℤ) ^ 4
          - 21 * (y : ℤ) ^ 5) +
        7 * (y : ℤ) ^ 6 := by
  rw [show (x : ℤ) = -(y : ℤ) + ((x + y : ℕ) : ℤ) by push_cast; ring]
  rw [cyclotomicSeven_substitution_expansion]
  ring

/-- A primitive endpoint pair forces the gcd of the sum and alternating
factor to divide seven. -/
theorem gcd_add_alternatingCyclotomicSeven_dvd_seven
    {x y : ℕ} (hcop : Nat.Coprime x y) :
    Nat.gcd (x + y) (alternatingCyclotomicSeven x y) ∣ 7 := by
  let d := Nat.gcd (x + y) (alternatingCyclotomicSeven x y)
  have hdSum : d ∣ x + y := Nat.gcd_dvd_left _ _
  have hdAlt : d ∣ alternatingCyclotomicSeven x y := Nat.gcd_dvd_right _ _
  have hdSumInt : (d : ℤ) ∣ ((x + y : ℕ) : ℤ) :=
    Int.ofNat_dvd.mpr hdSum
  have hdCyclo : (d : ℤ) ∣ cyclotomicSeven (x : ℤ) (-(y : ℤ)) := by
    rw [← alternatingCyclotomicSeven_intCast]
    exact Int.ofNat_dvd.mpr hdAlt
  have hdPrefix : (d : ℤ) ∣
      ((x + y : ℕ) : ℤ) *
        (((x + y : ℕ) : ℤ) ^ 5
          - 7 * ((x + y : ℕ) : ℤ) ^ 4 * (y : ℤ)
          + 21 * ((x + y : ℕ) : ℤ) ^ 3 * (y : ℤ) ^ 2
          - 35 * ((x + y : ℕ) : ℤ) ^ 2 * (y : ℤ) ^ 3
          + 35 * ((x + y : ℕ) : ℤ) * (y : ℤ) ^ 4
          - 21 * (y : ℤ) ^ 5) :=
    dvd_mul_of_dvd_left hdSumInt _
  have hdy6Int : (d : ℤ) ∣ 7 * (y : ℤ) ^ 6 := by
    rw [alternatingCyclotomicSeven_sum_expansion] at hdCyclo
    have h := dvd_sub hdCyclo hdPrefix
    simpa only [add_sub_cancel_left] using h
  have hdy6 : d ∣ 7 * y ^ 6 := by
    exact_mod_cast hdy6Int
  have hcopSumY : Nat.Coprime (x + y) y := by
    exact (Nat.coprime_add_self_left).2 hcop
  have hdy : Nat.Coprime d y := hcopSumY.of_dvd_left hdSum
  exact (hdy.pow_right 6).dvd_of_dvd_mul_right hdy6

/-- On the Row-Z gap channel the gcd is exactly seven. -/
theorem gcd_add_alternatingCyclotomicSeven_eq_seven
    {x y : ℕ} (hcop : Nat.Coprime x y) (h7sum : 7 ∣ x + y) :
    Nat.gcd (x + y) (alternatingCyclotomicSeven x y) = 7 := by
  apply Nat.dvd_antisymm
  · exact gcd_add_alternatingCyclotomicSeven_dvd_seven hcop
  · apply Nat.dvd_gcd h7sum
    have hsumInt : (7 : ℤ) ∣ ((x + y : ℕ) : ℤ) :=
      Int.ofNat_dvd.mpr h7sum
    have hprefix : (7 : ℤ) ∣
        ((x + y : ℕ) : ℤ) *
          (((x + y : ℕ) : ℤ) ^ 5
            - 7 * ((x + y : ℕ) : ℤ) ^ 4 * (y : ℤ)
            + 21 * ((x + y : ℕ) : ℤ) ^ 3 * (y : ℤ) ^ 2
            - 35 * ((x + y : ℕ) : ℤ) ^ 2 * (y : ℤ) ^ 3
            + 35 * ((x + y : ℕ) : ℤ) * (y : ℤ) ^ 4
            - 21 * (y : ℤ) ^ 5) :=
      dvd_mul_of_dvd_left hsumInt _
    have hcyclo : (7 : ℤ) ∣ cyclotomicSeven (x : ℤ) (-(y : ℤ)) := by
      rw [alternatingCyclotomicSeven_sum_expansion]
      exact dvd_add hprefix (dvd_mul_right 7 ((y : ℤ) ^ 6))
    rw [← alternatingCyclotomicSeven_intCast] at hcyclo
    exact Int.ofNat_dvd.mp hcyclo

/-- Row Z makes the alternating sum endpoint divisible by seven. -/
theorem AwaySevenBaseTerminalRowZProfile.seven_dvd_sum
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    7 ∣ x + y := by
  apply Int.ofNat_dvd.mp
  simpa [sub_neg_eq_add] using hz.seven_dvd_signed_gap

/-- The primitive Row-Z sum channel has a seven-unit right endpoint. -/
theorem AwaySevenBaseTerminalRowZProfile.seven_not_dvd_y
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    ¬ 7 ∣ y := by
  intro hy
  have hx : 7 ∣ x := by
    rcases hy with ⟨ky, hky⟩
    rcases hz.seven_dvd_sum with ⟨ks, hks⟩
    refine ⟨ks - ky, ?_⟩
    omega
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx hy) source.hxy

/-- Exact Row-Z factorization through the alternating cyclotomic factor. -/
theorem AwaySevenBaseTerminalRowZProfile.alternating_factor_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (_hz : AwaySevenBaseTerminalRowZProfile terminal) :
    (x + y) * alternatingCyclotomicSeven x y = z ^ 7 := by
  rw [add_mul_alternatingCyclotomicSeven]
  exact source.hEq

/-- The alternating residual contains exactly one factor of seven. -/
theorem AwaySevenBaseTerminalRowZProfile.not_fortyNine_dvd_alternating
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    ¬ 49 ∣ alternatingCyclotomicSeven x y := by
  intro h49
  have hyInt : ¬ (7 : ℤ) ∣ -(y : ℤ) := by
    simpa only [dvd_neg] using
      (show ¬ (7 : ℤ) ∣ (y : ℤ) by
        intro h
        exact hz.seven_not_dvd_y (Int.ofNat_dvd.mp h))
  apply not_fortyNine_dvd_cyclotomicSeven
    hz.seven_dvd_signed_gap hyInt
  rw [← alternatingCyclotomicSeven_intCast]
  exact Int.ofNat_dvd.mpr h49

/-- Exact seventh-power split for the terminal Row-Z alternating factor. -/
structure AwaySevenBaseTerminalRowZAlternatingPowerSplit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) : Type where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  sum_eq : x + y = 7 ^ 6 * a ^ 7
  residual_eq : alternatingCyclotomicSeven x y = 7 * b ^ 7
  distinguished_eq : z = 7 * a * b

/-- Construct the Row-Z alternating power split from the exact gcd-seven
factorization. -/
theorem nonempty_rowZAlternatingPowerSplit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    Nonempty (AwaySevenBaseTerminalRowZAlternatingPowerSplit hz) := by
  let c := (x + y) / 7
  let residual := alternatingCyclotomicSeven x y / 7
  let d := z / 7
  have hfactor := hz.alternating_factor_eq
  have hgcd :
      Nat.gcd (x + y) (alternatingCyclotomicSeven x y) = 7 :=
    gcd_add_alternatingCyclotomicSeven_eq_seven source.hxy hz.seven_dvd_sum
  have h7alt : 7 ∣ alternatingCyclotomicSeven x y := by
    have h := Nat.gcd_dvd_right (x + y) (alternatingCyclotomicSeven x y)
    rw [hgcd] at h
    exact h
  have h7z : 7 ∣ z := by
    rw [hz.2.1]
    exact dvd_mul_right 7 terminal.core.carrier.carrierUnit
  have hc : x + y = 7 * c :=
    (Nat.mul_div_cancel' hz.seven_dvd_sum).symm
  have hres : alternatingCyclotomicSeven x y = 7 * residual :=
    (Nat.mul_div_cancel' h7alt).symm
  have hd : z = 7 * d := (Nat.mul_div_cancel' h7z).symm
  have hcopDiv : Nat.Coprime c residual := by
    have h := Nat.coprime_div_gcd_div_gcd
      (show 0 < Nat.gcd (x + y) (alternatingCyclotomicSeven x y) by
        rw [hgcd]
        norm_num)
    rw [hgcd] at h
    exact h
  have h7cop : Nat.Coprime 7 residual :=
    (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr (by
      intro h7
      apply hz.not_fortyNine_dvd_alternating
      rw [show 49 = 7 * 7 by norm_num, hres]
      exact mul_dvd_mul_left 7 h7)
  have hscaledCop : Nat.Coprime (7 ^ 2 * c) residual :=
    (h7cop.pow_left 2).mul_left hcopDiv
  have hnormalized :
      (7 ^ 2 * c) * residual = (7 * d) ^ 7 := by
    calc
      (7 ^ 2 * c) * residual =
          (7 * c) * (7 * residual) := by ring
      _ = (x + y) * alternatingCyclotomicSeven x y := by
        rw [← hc, ← hres]
      _ = z ^ 7 := hfactor
      _ = (7 * d) ^ 7 := by rw [← hd]
  rcases seventh_power_factor_split hscaledCop hnormalized with
    ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
  have h7A : 7 ∣ A := by
    apply (by norm_num : Nat.Prime 7).dvd_of_dvd_pow
    rw [← hA]
    exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 7 ^ 2) c
  rcases h7A with ⟨a, haA⟩
  have hcExact : c = 7 ^ 5 * a ^ 7 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7 ^ 2)
    calc
      7 ^ 2 * c = A ^ 7 := hA
      _ = (7 * a) ^ 7 := by rw [haA]
      _ = 7 ^ 2 * (7 ^ 5 * a ^ 7) := by ring
  have hsum : x + y = 7 ^ 6 * a ^ 7 := by
    rw [hc, hcExact]
    ring
  have hresidual :
      alternatingCyclotomicSeven x y = 7 * b ^ 7 := by
    rw [hres, hb]
  have hdist : z = 7 * a * b := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    change z ^ 7 = (7 * a * b) ^ 7
    calc
      z ^ 7 = (x + y) * alternatingCyclotomicSeven x y := hfactor.symm
      _ = (7 ^ 6 * a ^ 7) * (7 * b ^ 7) :=
        congrArg₂ (· * ·) hsum hresidual
      _ = (7 * a * b) ^ 7 := by ring
  have haPos : 0 < a := by
    by_contra ha0
    have : a = 0 := by omega
    rw [this] at hsum
    norm_num at hsum
    have hx := source.hx
    omega
  have hbPos : 0 < b := by
    by_contra hb0
    have : b = 0 := by omega
    rw [this] at hresidual
    norm_num at hresidual
    have hAltPos : 0 < alternatingCyclotomicSeven x y := by
      have hz7 : 0 < z ^ 7 := pow_pos source.hz 7
      have hprod :
          0 < (x + y) * alternatingCyclotomicSeven x y := by
        rw [hfactor]
        exact hz7
      exact Nat.pos_of_mul_pos_left hprod
    omega
  have hcoreCoprime : Nat.Coprime (7 ^ 5 * a ^ 7) (b ^ 7) := by
    rw [← hcExact, ← hb]
    exact hcopDiv
  have hpows : Nat.Coprime (a ^ 7) (b ^ 7) :=
    hcoreCoprime.of_dvd_left (dvd_mul_left (a ^ 7) (7 ^ 5))
  have hab : Nat.Coprime a b := by
    apply (Nat.coprime_pow_right_iff (by decide : 0 < 7) a b).mp
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 7) a (b ^ 7)).mp hpows
  exact ⟨{
    a := a
    b := b
    a_pos := haPos
    b_pos := hbPos
    coprime_a_b := hab
    sum_eq := hsum
    residual_eq := hresidual
    distinguished_eq := hdist }⟩

noncomputable def AwaySevenBaseTerminalRowZProfile.alternatingPowerSplit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    AwaySevenBaseTerminalRowZAlternatingPowerSplit hz :=
  Classical.choice (nonempty_rowZAlternatingPowerSplit hz)

end DkMath.FLT.Seven
