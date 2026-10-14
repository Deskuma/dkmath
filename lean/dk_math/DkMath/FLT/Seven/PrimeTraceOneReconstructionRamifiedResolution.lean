/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionChart
import DkMath.FLT.Seven.PrimeTraceOneRamifiedSummitBridge
import DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
import DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore

#print "file: DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolution"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! The following three lemmas are the de-terminalized arithmetic core of the
prescribed-carrier chart.  Their only inputs are a primitive Fermat packet and
the indicated seven-divisibility fact. -/

theorem nonempty_ramified_of_seven_dvd_second
    {x carrier z : ℕ} (source : CounterexamplePack x carrier z)
    (hcarrier : 7 ∣ carrier) :
    Nonempty (RamifiedCoordinateNormalForm carrier x z) := by
  have hcarrier0 : (carrier : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hcarrier
  have hlin := fermat7Equation_modSeven_linear source.hEq
  have hxz : (x : ModSeven) = (z : ModSeven) := by
    rw [hcarrier0] at hlin
    simpa using hlin
  have hxle : x ≤ z :=
    (right_lt_of_fermat7Equation
      (CounterexamplePack.swapXY_for_reconstruction source).hx
      (CounterexamplePack.swapXY_for_reconstruction source).hEq).le
  have hgap : 7 ∣ z - x := by
    apply (Nat.modEq_iff_dvd' hxle).1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hxz
  rcases coordinateCounterexampleRoute_of_pack
      (CounterexamplePack.swapXY_for_reconstruction source) with ⟨route⟩
  cases route with
  | away packet => exact (packet.seven_not_dvd_gap hgap).elim
  | ramified packet => exact ⟨packet⟩

theorem seven_dvd_sum_of_seven_dvd_third
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    7 ∣ x + y := by
  have hz0 : (z : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hz
  have hlin := fermat7Equation_modSeven_linear source.hEq
  rw [hz0] at hlin
  apply (ZMod.natCast_eq_zero_iff _ _).1
  push_cast
  exact hlin

theorem seven_not_dvd_second_of_seven_dvd_sum
    {x y z : ℕ} (source : CounterexamplePack x y z) (hsum : 7 ∣ x + y) :
    ¬ 7 ∣ y := by
  intro hy
  have hx : 7 ∣ x := by
    rcases hy with ⟨ky, hky⟩
    rcases hsum with ⟨ks, hks⟩
    refine ⟨ks - ky, ?_⟩
    omega
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx hy) source.hxy

theorem seven_dvd_signed_gap_of_seven_dvd_third
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    (7 : ℤ) ∣ (x : ℤ) - (-(y : ℤ)) := by
  have hsum := seven_dvd_sum_of_seven_dvd_third source hz
  rcases hsum with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [sub_neg_eq_add]
  exact_mod_cast hk

structure PrescribedCarrierAlternatingPowerSplit
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) : Type where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  sum_eq : x + y = 7 ^ 6 * a ^ 7
  residual_eq : alternatingCyclotomicSeven x y = 7 * b ^ 7
  distinguished_eq : z = 7 * a * b

theorem nonempty_prescribedCarrierAlternatingPowerSplit
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    Nonempty (PrescribedCarrierAlternatingPowerSplit source hz) := by
  let hsum := seven_dvd_sum_of_seven_dvd_third source hz
  let hy0 := seven_not_dvd_second_of_seven_dvd_sum source hsum
  let c := (x + y) / 7
  let residual := alternatingCyclotomicSeven x y / 7
  let d := z / 7
  have hfactor :
      (x + y) * alternatingCyclotomicSeven x y = z ^ 7 := by
    rw [add_mul_alternatingCyclotomicSeven]
    exact source.hEq
  have hgcd :
      Nat.gcd (x + y) (alternatingCyclotomicSeven x y) = 7 :=
    gcd_add_alternatingCyclotomicSeven_eq_seven source.hxy hsum
  have h7alt : 7 ∣ alternatingCyclotomicSeven x y := by
    have h := Nat.gcd_dvd_right (x + y) (alternatingCyclotomicSeven x y)
    rw [hgcd] at h
    exact h
  have hc : x + y = 7 * c :=
    (Nat.mul_div_cancel' hsum).symm
  have hres : alternatingCyclotomicSeven x y = 7 * residual :=
    (Nat.mul_div_cancel' h7alt).symm
  have hd : z = 7 * d := (Nat.mul_div_cancel' hz).symm
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
      have hgap := seven_dvd_signed_gap_of_seven_dvd_third source hz
      have hyInt : ¬ (7 : ℤ) ∣ -(y : ℤ) := by
        simpa only [dvd_neg] using
          (show ¬ (7 : ℤ) ∣ (y : ℤ) by
            intro h
            exact hy0 (Int.ofNat_dvd.mp h))
      apply not_fortyNine_dvd_cyclotomicSeven hgap hyInt
      rw [← alternatingCyclotomicSeven_intCast]
      rw [hres]
      rcases h7 with ⟨k, hk⟩
      refine ⟨(k : ℤ), ?_⟩
      rw [hk]
      norm_num
      ring)
  have hscaledCop : Nat.Coprime (7 ^ 2 * c) residual :=
    (h7cop.pow_left 2).mul_left hcopDiv
  have hnormalized :
      (7 ^ 2 * c) * residual = (7 * d) ^ 7 := by
    calc
      (7 ^ 2 * c) * residual = (7 * c) * (7 * residual) := by ring
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
  have hsumExact : x + y = 7 ^ 6 * a ^ 7 := by
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
        congrArg₂ (· * ·) hsumExact hresidual
      _ = (7 * a * b) ^ 7 := by ring
  have haPos : 0 < a := by
    by_contra ha0
    have : a = 0 := by omega
    rw [this] at hsumExact
    norm_num at hsumExact
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
    sum_eq := hsumExact
    residual_eq := hresidual
    distinguished_eq := hdist }⟩

structure PrescribedCarrierSignedResidualCore
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) : Type where
  powerSplit : PrescribedCarrierAlternatingPowerSplit source hz
  residualCore : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
      sevenAxis * residualCore
  residual_ne_zero : residualCore ≠ 0
  residual_terminal : ¬ sevenAxis ∣ residualCore
  residual_norm_not_seven_dvd : ¬ (7 : ℤ) ∣ tqNorm residualCore
  residual_norm_eq : tqNorm residualCore = (powerSplit.b : ℤ) ^ 7
  residual_norm_pos : 1 ≤ tqNorm residualCore

theorem nonempty_prescribedCarrierSignedResidualCore
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    Nonempty (PrescribedCarrierSignedResidualCore source hz) := by
  let split := Classical.choice
    (nonempty_prescribedCarrierAlternatingPowerSplit source hz)
  have hyInt : ¬ (7 : ℤ) ∣ -(y : ℤ) := by
    simpa only [dvd_neg] using
      (show ¬ (7 : ℤ) ∣ (y : ℤ) by
        intro h
        exact seven_not_dvd_second_of_seven_dvd_sum source
          (seven_dvd_sum_of_seven_dvd_third source hz) (Int.ofNat_dvd.mp h))
  rcases exists_cyclotomicSeven_terminal_core
      (seven_dvd_signed_gap_of_seven_dvd_third source hz) hyInt with
    ⟨core, hcoordinate, hcore0, hterminal, hnorm7, hcycloNorm, hnormPos⟩
  have hAltInt :
      (alternatingCyclotomicSeven x y : ℤ) = 7 * (split.b : ℤ) ^ 7 := by
    exact_mod_cast split.residual_eq
  have hnorm : tqNorm core = (split.b : ℤ) ^ 7 := by
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * tqNorm core = cyclotomicSeven (x : ℤ) (-(y : ℤ)) := hcycloNorm.symm
      _ = (alternatingCyclotomicSeven x y : ℤ) :=
        (alternatingCyclotomicSeven_intCast x y).symm
      _ = 7 * (split.b : ℤ) ^ 7 := hAltInt
  exact ⟨{
    powerSplit := split
    residualCore := core
    coordinate_eq := hcoordinate
    residual_ne_zero := hcore0
    residual_terminal := hterminal
    residual_norm_not_seven_dvd := hnorm7
    residual_norm_eq := hnorm
    residual_norm_pos := hnormPos }⟩

noncomputable def prescribedCarrierSignedResidualCore
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    PrescribedCarrierSignedResidualCore source hz :=
  Classical.choice (nonempty_prescribedCarrierSignedResidualCore source hz)

theorem PrescribedCarrierSignedResidualCore.gcd_conj_isUnit
    {x y z : ℕ} {source : CounterexamplePack x y z} {hz : 7 ∣ z}
    (q : PrescribedCarrierSignedResidualCore source hz) :
    IsUnit (gcd q.residualCore (conj q.residualCore)) := by
  let d := gcd q.residualCore (conj q.residualCore)
  let C := cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ))
  have hdr : d ∣ q.residualCore := gcd_dvd_left _ _
  have hdrc : d ∣ conj q.residualCore := gcd_dvd_right _ _
  have hdC : d ∣ C := by
    dsimp [C]
    rw [q.coordinate_eq]
    exact dvd_mul_of_dvd_right hdr sevenAxis
  have hdConjC : d ∣ conj C := by
    dsimp [C]
    rw [q.coordinate_eq, traceOne_conj_mul, conj_sevenAxis]
    exact dvd_mul_of_dvd_right hdrc (-sevenAxis)
  have hcoords : IsCoprime C.fst C.snd := by
    simpa [C, cyclotomicSevenToTraceOne] using
      (rowZ_signed_cyclotomicSeven_coordinates_isCoprime source.hxy)
  have hdAxis : d ∣ sevenAxis :=
    common_divisor_dvd_sevenAxis_of_coordinate_coprime hcoords hdC hdConjC
  exact isUnit_of_dvd_sevenAxis_of_dvd_terminal
    hdAxis hdr q.residual_terminal

theorem PrescribedCarrierSignedResidualCore.exists_residualCore_eq_seventh_power
    {x y z : ℕ} {source : CounterexamplePack x y z} {hz : 7 ∣ z}
    (q : PrescribedCarrierSignedResidualCore source hz) :
    ∃ root : TraceOneInt (-2), q.residualCore = root ^ 7 := by
  have hmul : q.residualCore * conj q.residualCore =
      (q.powerSplit.b : TraceOneInt (-2)) ^ 7 := by
    rw [traceOne_mul_conj]
    rw [q.residual_norm_eq]
    change ((((q.powerSplit.b : ℤ) ^ 7 : ℤ)) : TraceOneInt (-2)) =
      ((q.powerSplit.b : ℤ) : TraceOneInt (-2)) ^ 7
    exact Int.cast_pow q.powerSplit.b 7
  exact exists_eq_seventh_power_of_coprime_mul_eq_pow
    q.gcd_conj_isUnit hmul

structure PrescribedCarrierRamifiedSummit (carrier : ℕ) : Type where
  summit : PrimitiveRamifiedSummitPacket
  distinguished_eq : summit.distinguished = (carrier : ℤ)

theorem nonempty_prescribedCarrierRamifiedSummit_of_right_chart
    {carrier x z : ℕ} (pack : CounterexamplePack x carrier z)
    (hcarrier : 7 ∣ carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) := by
  rcases nonempty_ramified_of_seven_dvd_second pack hcarrier with ⟨packet⟩
  exact ⟨{
    summit := packet.seventhPower.toPrimitiveRamifiedSummitPacket
    distinguished_eq := rfl }⟩

theorem nonempty_prescribedCarrierRamifiedSummit_of_left_chart
    {carrier x y : ℕ} (source : CounterexamplePack x y carrier)
    (hcarrier : 7 ∣ carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) := by
  let q := prescribedCarrierSignedResidualCore source hcarrier
  let split := q.powerSplit
  let root := Classical.choose q.exists_residualCore_eq_seventh_power
  have hroot : q.residualCore = root ^ 7 :=
    Classical.choose_spec q.exists_residualCore_eq_seventh_power
  exact ⟨{
    summit := {
      endpointLeft := x
      endpointRight := -(y : ℤ)
      distinguished := carrier
      gapRoot := split.a
      residualRoot := split.b
      root := root
      gapRoot_pos := split.a_pos
      residualRoot_pos := split.b_pos
      endpoint_coprime := source.hxy.isCoprime.neg_right
      endpointLeft_ne_zero := by exact_mod_cast source.hx.ne'
      endpointRight_ne_zero := by
        simp only [neg_ne_zero]
        exact_mod_cast source.hy.ne'
      endpointSum_ne_zero := by
        intro hsum
        have hxy : x = y := by
          exact_mod_cast (sub_eq_zero.mp hsum)
        subst y
        have hx1 : x = 1 :=
          Nat.eq_one_of_dvd_coprimes source.hxy dvd_rfl dvd_rfl
        subst x
        have heq := source.hEq
        norm_num [Fermat7Equation] at heq
        by_cases hc1 : carrier = 1
        · simp [hc1] at heq
        · have hcpos := source.hz
          have hc2 : 2 ≤ carrier := by omega
          have hpows : 2 ^ 7 ≤ carrier ^ 7 := Nat.pow_le_pow_left hc2 7
          omega
      coordinate_coprime :=
        rowZ_signed_cyclotomicSeven_coordinates_isCoprime source.hxy
      endpointRight_not_seven_dvd := by
        simpa only [dvd_neg] using
          (show ¬ (7 : ℤ) ∣ (y : ℤ) by
            intro hy
            exact seven_not_dvd_second_of_seven_dvd_sum source
              (seven_dvd_sum_of_seven_dvd_third source hcarrier)
              (Int.ofNat_dvd.mp hy))
      residualRoot_not_seven_dvd := by
        intro hb
        apply q.residual_norm_not_seven_dvd
        rw [q.residual_norm_eq]
        exact dvd_pow (Int.ofNat_dvd.mpr hb) (by norm_num)
      fermat_eq := by
        have h := source.hEq
        unfold Fermat7Equation at h
        nlinarith
      gap_eq := by
        simp only [sub_neg_eq_add]
        exact_mod_cast split.sum_eq
      residual_eq := by
        rw [← alternatingCyclotomicSeven_intCast]
        exact_mod_cast split.residual_eq
      distinguished_eq := by exact_mod_cast split.distinguished_eq
      coordinate_eq := by rw [q.coordinate_eq, hroot]
      root_norm_eq :=
        root_norm_eq_of_residual_power hroot q.residual_norm_eq }
    distinguished_eq := rfl }⟩

theorem nonempty_prescribedCarrierRamifiedSummit_of_fermatChart
    {carrier : ℕ} (h : AwayCarrierFermatChart carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) := by
  cases h with
  | right pack hcarrier =>
      exact nonempty_prescribedCarrierRamifiedSummit_of_right_chart pack hcarrier
  | left pack hcarrier =>
      exact nonempty_prescribedCarrierRamifiedSummit_of_left_chart pack hcarrier
  | sum pack hcarrier hseven =>
      exact (AwayCarrierFermatChart.sum_impossible pack hcarrier hseven).elim

theorem nonempty_prescribedCarrierRamifiedSummit_of_awayCarrierReconstruction
    {carrier : ℕ} (h : AwayCarrierReconstruction carrier) :
    Nonempty (PrescribedCarrierRamifiedSummit carrier) :=
  nonempty_prescribedCarrierRamifiedSummit_of_fermatChart
    ((awayCarrierReconstruction_iff_fermatChart).mp h)

end DkMath.FLT.Seven
