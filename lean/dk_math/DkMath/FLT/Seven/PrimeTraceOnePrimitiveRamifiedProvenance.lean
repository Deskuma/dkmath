/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedResolution
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCompensationRouting

#print "file: DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem not_seven_dvd_x_add_z_of_seven_dvd_second
    {x y z : ℕ} (source : CounterexamplePack x y z) (hy : 7 ∣ y) :
    ¬ 7 ∣ x + z := by
  intro hsum
  have hy0 : (y : ModSeven) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hy
  have hsum0 : (x : ModSeven) + (z : ModSeven) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hsum
  have hlin := fermat7Equation_modSeven_linear source.hEq
  have hxz : (x : ModSeven) = (z : ModSeven) := by
    rw [hy0] at hlin
    simpa using hlin
  have htwo : (2 : ModSeven) ≠ 0 := by decide
  have hprod : (2 : ModSeven) * (x : ModSeven) = 0 := by
    rw [← hxz] at hsum0
    linear_combination hsum0
  have hx0 : (x : ModSeven) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left htwo
  have hx : 7 ∣ x := (ZMod.natCast_eq_zero_iff _ _).1 hx0
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx hy) source.hxy

private theorem not_seven_dvd_x_sub_y_of_seven_dvd_third
    {x y z : ℕ} (source : CounterexamplePack x y z) (hz : 7 ∣ z) :
    ¬ (7 : ℤ) ∣ (x : ℤ) - (y : ℤ) := by
  intro hsub
  have hsum := seven_dvd_sum_of_seven_dvd_third source hz
  have hsum0 : (x : ModSeven) + (y : ModSeven) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hsum
  have hsub0 : (x : ModSeven) - (y : ModSeven) = 0 := by
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hsub
    push_cast at hzero
    exact hzero
  have htwo : (2 : ModSeven) ≠ 0 := by decide
  have hprod : (2 : ModSeven) * (x : ModSeven) = 0 := by
    linear_combination hsum0 + hsub0
  have hx0 : (x : ModSeven) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left htwo
  have hx : 7 ∣ x := (ZMod.natCast_eq_zero_iff _ _).1 hx0
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx hz)
    (coprime_y_z_of_counterexamplePack source.swapXY_for_reconstruction)

/-- The branch-specific data retained by a primitive counterexample after it
has been normalized to the common ramified summit.  Every constructor owns the
same summit that its resolution adapter returns. -/
inductive PrimitiveCounterexampleRamifiedProvenance
    {x y z : ℕ} (source : CounterexamplePack x y z) : Type
  | xCase (seven_dvd : 7 ∣ x) (summit : PrimitiveRamifiedSummitPacket)
      (endpointLeft_eq : summit.endpointLeft = (z : ℤ))
      (endpointRight_eq : summit.endpointRight = (y : ℤ))
      (distinguished_eq : summit.distinguished = (x : ℤ))
      (gap_residual_coprime : Nat.Coprime summit.gapRoot summit.residualRoot)
  | yCase (seven_dvd : 7 ∣ y) (summit : PrimitiveRamifiedSummitPacket)
      (endpointLeft_eq : summit.endpointLeft = (z : ℤ))
      (endpointRight_eq : summit.endpointRight = (x : ℤ))
      (distinguished_eq : summit.distinguished = (y : ℤ))
      (gap_residual_coprime : Nat.Coprime summit.gapRoot summit.residualRoot)
  | zCase (seven_dvd : 7 ∣ z) (summit : PrimitiveRamifiedSummitPacket)
      (endpointLeft_eq : summit.endpointLeft = (x : ℤ))
      (endpointRight_eq : summit.endpointRight = -(y : ℤ))
      (distinguished_eq : summit.distinguished = (z : ℤ))
      (gap_residual_coprime : Nat.Coprime summit.gapRoot summit.residualRoot)

namespace PrimitiveCounterexampleRamifiedProvenance

def summit {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    PrimitiveRamifiedSummitPacket := by
  cases r with
  | xCase _ q _ _ _ _ => exact q
  | yCase _ q _ _ _ _ => exact q
  | zCase _ q _ _ _ _ => exact q

def distinguishedEndpoint {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) : ℕ := by
  cases r with
  | xCase _ _ _ _ _ _ => exact x
  | yCase _ _ _ _ _ _ => exact y
  | zCase _ _ _ _ _ _ => exact z

theorem gap_residual_coprime {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    Nat.Coprime r.summit.gapRoot r.summit.residualRoot := by
  cases r with
  | xCase _ _ _ _ _ hcop => exact hcop
  | yCase _ _ _ _ _ hcop => exact hcop
  | zCase _ _ _ _ _ hcop => exact hcop

def toResolution {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    PrimitiveCounterexampleRamifiedResolution source := by
  cases r with
  | xCase h q _ _ hq _ => exact .xCase h q hq
  | yCase h q _ _ hq _ => exact .yCase h q hq
  | zCase h q _ _ hq _ => exact .zCase h q hq

theorem toResolution_summit {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    r.toResolution.summit = r.summit := by
  cases r <;> rfl

theorem distinguished_padicValNat {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    padicValNat 7 r.distinguishedEndpoint =
      1 + padicValNat 7 r.summit.gapRoot := by
  cases r with
  | xCase _ q _ _ hq _ =>
      dsimp [distinguishedEndpoint, summit]
      calc
        padicValNat 7 x = padicValNat 7 (Int.natAbs q.distinguished) := by
          rw [hq]
          simp
        _ = _ := q.distinguished_padicValNat
  | yCase _ q _ _ hq _ =>
      dsimp [distinguishedEndpoint, summit]
      calc
        padicValNat 7 y = padicValNat 7 (Int.natAbs q.distinguished) := by
          rw [hq]
          simp
        _ = _ := q.distinguished_padicValNat
  | zCase _ q _ _ hq _ =>
      dsimp [distinguishedEndpoint, summit]
      calc
        padicValNat 7 z = padicValNat 7 (Int.natAbs q.distinguished) := by
          rw [hq]
          simp
        _ = _ := q.distinguished_padicValNat

theorem endpointLeft_not_seven_dvd {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ¬ (7 : ℤ) ∣ r.summit.endpointLeft := by
  cases r with
  | xCase hx q hleft _ _ _ =>
      dsimp [summit]
      rw [hleft]
      intro hz
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx
        (Int.ofNat_dvd.mp hz))
        (coprime_y_z_of_counterexamplePack source.swapXY_for_reconstruction)
  | yCase hy q hleft _ _ _ =>
      dsimp [summit]
      rw [hleft]
      intro hz
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hy
        (Int.ofNat_dvd.mp hz))
        (coprime_y_z_of_counterexamplePack source)
  | zCase hz q hleft _ _ _ =>
      dsimp [summit]
      rw [hleft]
      intro hx
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (Int.ofNat_dvd.mp hx)
        hz) (coprime_y_z_of_counterexamplePack source.swapXY_for_reconstruction)

theorem endpointRight_not_seven_dvd {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ¬ (7 : ℤ) ∣ r.summit.endpointRight := by
  cases r with
  | xCase hx q _ hright _ _ =>
      dsimp [summit]
      rw [hright]
      intro hy
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hx
        (Int.ofNat_dvd.mp hy)) source.hxy
  | yCase hy q _ hright _ _ =>
      dsimp [summit]
      rw [hright]
      intro hx
      exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num)
        (Int.ofNat_dvd.mp hx) hy) source.hxy
  | zCase hz q _ hright _ _ =>
      dsimp [summit]
      rw [hright]
      simpa only [dvd_neg] using
        (show ¬ (7 : ℤ) ∣ (y : ℤ) by
          intro hy
          exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num)
            (Int.ofNat_dvd.mp hy) hz)
            (coprime_y_z_of_counterexamplePack source))

theorem endpointSum_not_seven_dvd {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ¬ (7 : ℤ) ∣ r.summit.endpointLeft + r.summit.endpointRight := by
  cases r with
  | xCase hx q hleft hright _ _ =>
      dsimp [summit]
      rw [hleft, hright]
      intro hsum
      apply no_counterexample_of_seven_dvd_y_add_z source
      apply Int.ofNat_dvd.mp
      simpa [Nat.cast_add, add_comm] using hsum
  | yCase hy q hleft hright _ _ =>
      dsimp [summit]
      rw [hleft, hright]
      intro hsum
      apply not_seven_dvd_x_add_z_of_seven_dvd_second source hy
      apply Int.ofNat_dvd.mp
      simpa [Nat.cast_add, add_comm] using hsum
  | zCase hz q hleft hright _ _ =>
      dsimp [summit]
      rw [hleft, hright]
      simpa [sub_eq_add_neg] using
        not_seven_dvd_x_sub_y_of_seven_dvd_third source hz

/-- A counterexample-origin summit is terminalizable only by retaining the
very same common summit in the historical terminal packet. -/
def CounterexampleOriginTerminalizable {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) : Prop :=
  ∃ t : TerminalPrimitiveRamifiedSummitPacket, t.summit = r.summit

theorem terminalizable_iff_gapRoot_not_seven_dvd {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    CounterexampleOriginTerminalizable r ↔ ¬ 7 ∣ r.summit.gapRoot := by
  constructor
  · rintro ⟨t, ht⟩ hgap
    apply t.gapRoot_not_seven_dvd
    simpa [ht] using hgap
  · intro hgap
    refine ⟨{
      summit := r.summit
      carrierUnit := r.summit.gapRoot * r.summit.residualRoot
      carrierUnit_pos := Nat.mul_pos r.summit.gapRoot_pos r.summit.residualRoot_pos
      carrierUnit_not_seven_dvd := ?_
      carrier_eq := rfl
      gap_residual_coprime := r.gap_residual_coprime }, rfl⟩
    intro hcarrier
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hcarrier with
      hroot | hresidual
    · exact hgap hroot
    · exact r.summit.residualRoot_not_seven_dvd hresidual

theorem terminalizable_iff_endpoint_depth_eq_one {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    CounterexampleOriginTerminalizable r ↔
      padicValNat 7 r.distinguishedEndpoint = 1 := by
  rw [terminalizable_iff_gapRoot_not_seven_dvd]
  constructor
  · intro hgap
    have hval : padicValNat 7 r.summit.gapRoot = 0 :=
      padicValNat.eq_zero_of_not_dvd hgap
    have hdepth := r.distinguished_padicValNat
    omega
  · intro hdepth hgap
    have hpositive : 1 ≤ padicValNat 7 r.summit.gapRoot :=
      (@padicValNat_dvd_iff_le 7 inferInstance r.summit.gapRoot 1
        r.summit.gapRoot_pos.ne').mp hgap
    have hval := r.distinguished_padicValNat
    omega

theorem endpoint_depth_eq_one_or_two_le {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    padicValNat 7 r.distinguishedEndpoint = 1 ∨
      2 ≤ padicValNat 7 r.distinguishedEndpoint := by
  have hdiv : 7 ∣ r.distinguishedEndpoint := by
    cases r with
    | xCase h _ _ _ _ _ => exact h
    | yCase h _ _ _ _ _ => exact h
    | zCase h _ _ _ _ _ => exact h
  have hpos : 0 < r.distinguishedEndpoint := by
    cases r with
    | xCase _ _ _ _ _ _ => exact source.hx
    | yCase _ _ _ _ _ _ => exact source.hy
    | zCase _ _ _ _ _ _ => exact source.hz
  have hpositive : 1 ≤ padicValNat 7 r.distinguishedEndpoint :=
    (@padicValNat_dvd_iff_le 7 inferInstance r.distinguishedEndpoint 1
      hpos.ne').mp hdiv
  omega

theorem seven_dvd_gapRoot_of_two_le_endpoint_depth {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (hdepth : 2 ≤ padicValNat 7 r.distinguishedEndpoint) :
    7 ∣ r.summit.gapRoot := by
  have hval := r.distinguished_padicValNat
  have hpositive : 1 ≤ padicValNat 7 r.summit.gapRoot := by omega
  exact (@padicValNat_dvd_iff_le 7 inferInstance r.summit.gapRoot 1
    r.summit.gapRoot_pos.ne').mpr hpositive

theorem not_terminalizable_of_two_le_endpoint_depth {x y z : ℕ}
    {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (hdepth : 2 ≤ padicValNat 7 r.distinguishedEndpoint) :
    ¬ CounterexampleOriginTerminalizable r := by
  intro hterminal
  have hterminalDepth := (r.terminalizable_iff_endpoint_depth_eq_one).1 hterminal
  omega

/-- The depth-one branch reaches the first historical terminal receiver with
no additional reconstruction hypothesis. -/
theorem nonempty_secondCoordinateRouting_of_endpoint_depth_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (hdepth : padicValNat 7 r.distinguishedEndpoint = 1) :
    Nonempty RamifiedSecondCoordinateRoutingPacket := by
  rcases (r.terminalizable_iff_endpoint_depth_eq_one).2 hdepth with ⟨t, _⟩
  exact t.nonempty_secondCoordinateRouting

end PrimitiveCounterexampleRamifiedProvenance

theorem nonempty_primitiveCounterexampleRamifiedProvenance
    {x y z : ℕ} (source : CounterexamplePack x y z) :
    Nonempty (PrimitiveCounterexampleRamifiedProvenance source) := by
  cases primitiveSevenDivisibleEndpoint_of_counterexample source with
  | xOnly hx _ _ =>
      let packet := sevenQuadraticSeventhPowerPacket_of_counterexample source
        (seven_dvd_gap_of_seven_dvd_first source hx)
      exact ⟨.xCase hx packet.toPrimitiveRamifiedSummitPacket rfl rfl rfl
        packet.residual.powerSplit.coprime_a_b⟩
  | yOnly hy _ _ =>
      let packet := Classical.choice (nonempty_ramified_of_seven_dvd_second source hy)
      exact ⟨.yCase hy packet.seventhPower.toPrimitiveRamifiedSummitPacket
        rfl rfl rfl packet.seventhPower.residual.powerSplit.coprime_a_b⟩
  | zOnly hz _ _ =>
      let q := prescribedCarrierSignedResidualCore source hz
      let split := q.powerSplit
      let root := Classical.choose q.exists_residualCore_eq_seventh_power
      have hroot : q.residualCore = root ^ 7 :=
        Classical.choose_spec q.exists_residualCore_eq_seventh_power
      let summit : PrimitiveRamifiedSummitPacket := {
        endpointLeft := x
        endpointRight := -(y : ℤ)
        distinguished := z
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
          have hxy : x = y := by exact_mod_cast (sub_eq_zero.mp hsum)
          subst y
          have hx1 : x = 1 :=
            Nat.eq_one_of_dvd_coprimes source.hxy dvd_rfl dvd_rfl
          subst x
          have heq := source.hEq
          norm_num [Fermat7Equation] at heq
          by_cases hz1 : z = 1
          · simp [hz1] at heq
          · have hzpos := source.hz
            have hz2 : 2 ≤ z := by omega
            have hpows : 2 ^ 7 ≤ z ^ 7 := Nat.pow_le_pow_left hz2 7
            omega
        coordinate_coprime := rowZ_signed_cyclotomicSeven_coordinates_isCoprime source.hxy
        endpointRight_not_seven_dvd := by
          simpa only [dvd_neg] using
            (show ¬ (7 : ℤ) ∣ (y : ℤ) by
              intro hy
              exact seven_not_dvd_second_of_seven_dvd_sum source
                (seven_dvd_sum_of_seven_dvd_third source hz)
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
        root_norm_eq := root_norm_eq_of_residual_power hroot q.residual_norm_eq }
      exact ⟨.zCase hz summit rfl rfl rfl split.coprime_a_b⟩

end DkMath.FLT.Seven
