/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel

#print "file: DkMath.FLT.Seven.PrimeTraceOneReconstructionChart"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- An actual primitive positive FLT7 counterexample whose prescribed carrier
is respectively the second summand, the right-hand side, or the endpoint sum.
The three constructors are intentionally kept distinct: the carrier position
is part of the reconstruction data. -/
inductive AwayCarrierFermatChart (carrier : ℕ) : Prop
  | right {x z : ℕ}
      (pack : CounterexamplePack x carrier z)
      (seven_dvd_carrier : 7 ∣ carrier)
  | left {x y : ℕ}
      (pack : CounterexamplePack x y carrier)
      (seven_dvd_carrier : 7 ∣ carrier)
  | sum {x y z : ℕ}
      (pack : CounterexamplePack x y z)
      (carrier_eq : y + z = carrier)
      (seven_dvd_carrier : 7 ∣ carrier)

namespace CounterexamplePack

/-- Exchange the two positive summands without importing the terminal-row
resolution layer.  This is the structural permutation used by the prescribed
carrier resolution. -/
theorem swapXY_for_reconstruction {x y z : ℕ}
    (source : CounterexamplePack x y z) :
    CounterexamplePack y x z where
  hx := source.hy
  hy := source.hx
  hz := source.hz
  hxy := source.hxy.symm
  hEq := by
    simpa [Fermat7Equation, add_comm] using source.hEq

end CounterexamplePack

/-- A primitive Fermat-seven counterexample cannot have its endpoint sum
divisible by seven.  The proof is entirely finite and residue-theoretic; it
does not use a terminal profile or a carrier reconstruction. -/
theorem no_counterexample_of_seven_dvd_y_add_z
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (hsum7 : 7 ∣ y + z) : False := by
  have hsum0 : (y : ModSeven) + (z : ModSeven) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hsum7
  rcases sevenEndpointResidueSector_of_counterexample source with
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩ |
      ⟨t, ht, hx, hy, hz⟩
  · rw [hy, hz] at hsum0
    have htwo : (2 : ModSeven) ≠ 0 := by decide
    have hprod : (2 : ModSeven) * t = 0 := by
      linear_combination hsum0
    exact ht ((mul_eq_zero.mp hprod).resolve_left htwo)
  · rw [hy, hz] at hsum0
    exact ht (by linear_combination hsum0)
  · rw [hy, hz] at hsum0
    exact ht (by simpa using hsum0)
  · have hx7 : ¬ 7 ∣ x := by
      intro h
      have hx0 : (x : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hx] at hx0
      have htwo : (-2 : ModSeven) ≠ 0 := by decide
      exact ht ((mul_eq_zero.mp hx0).resolve_left htwo)
    have hz7 : ¬ 7 ∣ z := by
      intro h
      have hz0 : (z : ModSeven) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hz] at hz0
      exact ht (neg_eq_zero.mp hz0)
    have hxz7 : ¬ 7 ∣ x + z := by
      intro h
      have hxz0 : (x : ModSeven) + (z : ModSeven) = 0 := by
        rw [← Nat.cast_add]
        exact (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [hx, hz] at hxz0
      have hthree : (-3 : ModSeven) ≠ 0 := by decide
      have hprod : (-3 : ModSeven) * t = 0 := by
        linear_combination hxz0
      exact ht ((mul_eq_zero.mp hprod).resolve_left hthree)
    have hxle : x ≤ z :=
      (right_lt_of_fermat7Equation
        (CounterexamplePack.swapXY_for_reconstruction source).hx
        (CounterexamplePack.swapXY_for_reconstruction source).hEq).le
    have hgap7 : ¬ 7 ∣ z - x := by
      intro hgap
      have hzx : (z : ModSeven) = (x : ModSeven) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).2
          ((Nat.modEq_iff_dvd' hxle).2 hgap).symm
      rw [hz, hx] at hzx
      have ht' : t = 0 := by linear_combination hzx
      exact ht ht'
    rcases coordinateCounterexampleRoute_of_pack
        (CounterexamplePack.swapXY_for_reconstruction source) with ⟨route⟩
    cases route with
    | ramified packet =>
        exact hgap7
          packet.seventhPower.residual.powerSplit.sevenAdic.seven_dvd_gap
    | away packet =>
        have hprod := seven_dvd_endpoint_product_of_away packet
        rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hprod with
          hxz | hxzsum
        · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hxz with
            hx' | hz'
          · exact hx7 hx'
          · exact hz7 hz'
        · exact hxz7 hxzsum

theorem AwayCarrierFermatChart.sum_impossible
    {carrier x y z : ℕ} (pack : CounterexamplePack x y z)
    (carrier_eq : y + z = carrier) (seven_dvd_carrier : 7 ∣ carrier) :
    False := by
  apply no_counterexample_of_seven_dvd_y_add_z pack
  simpa [carrier_eq] using seven_dvd_carrier

theorem awayCarrierReconstruction_to_fermatChart {carrier : ℕ}
    (h : AwayCarrierReconstruction carrier) :
    AwayCarrierFermatChart carrier := by
  rcases h with ⟨x, y, z, route, hroute⟩
  cases route.source with
  | right hy hz hsum hsource =>
      have hycarrier : y = carrier := hsource.symm.trans hroute
      subst y
      exact .right route.normal.counterexample hy
  | left hz hy hsum hsource =>
      have hzcarrier : z = carrier := hsource.symm.trans hroute
      subst z
      exact .left route.normal.counterexample hz
  | sum hsum hy hz hsource =>
      have hsumcarrier : y + z = carrier := hsource.symm.trans hroute
      have hseven : 7 ∣ carrier := by simpa [hsumcarrier] using hsum
      exact .sum route.normal.counterexample hsumcarrier hseven

private theorem not_ramified_right_chart {x z carrier : ℕ}
    (p : RamifiedCoordinateNormalForm x carrier z)
    (hcarrier : 7 ∣ carrier) : False := by
  exact p.seventhPower.residual.powerSplit.sevenAdic.seven_not_dvd_y hcarrier

private theorem not_ramified_left_chart {x y carrier : ℕ}
    (p : RamifiedCoordinateNormalForm x y carrier)
    (hcarrier : 7 ∣ carrier) : False := by
  have hy0 := p.seventhPower.residual.powerSplit.sevenAdic.seven_not_dvd_y
  have hgap := p.seventhPower.residual.powerSplit.sevenAdic.seven_dvd_gap
  have hycarrier :=
    (right_lt_of_fermat7Equation p.seventhPower.residual.powerSplit.sevenAdic.counterexample.hx
      p.seventhPower.residual.powerSplit.sevenAdic.counterexample.hEq).le
  have hsum : 7 ∣ y + (carrier - y) := by
    rw [Nat.add_sub_of_le hycarrier]
    exact hcarrier
  have hy : 7 ∣ y :=
    (Nat.dvd_add_iff_left (k := 7) (m := y) (n := carrier - y) hgap).mpr hsum
  exact hy0 hy

private theorem not_ramified_sum_chart {x y z carrier : ℕ}
    (p : RamifiedCoordinateNormalForm x y z)
    (hcarrier : y + z = carrier) (hseven : 7 ∣ carrier) : False := by
  have hy0 := p.seventhPower.residual.powerSplit.sevenAdic.seven_not_dvd_y
  have hgap := p.seventhPower.residual.powerSplit.sevenAdic.seven_dvd_gap
  have hyz :=
    (right_lt_of_fermat7Equation p.seventhPower.residual.powerSplit.sevenAdic.counterexample.hx
      p.seventhPower.residual.powerSplit.sevenAdic.counterexample.hEq).le
  have hsum : 7 ∣ 2 * y + (z - y) := by
    have hrewrite : 2 * y + (z - y) = y + z := by omega
    rw [hrewrite, hcarrier]
    exact hseven
  have htwo_y : 7 ∣ 2 * y :=
    (Nat.dvd_add_iff_left (k := 7) (m := 2 * y) (n := z - y) hgap).mpr hsum
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp htwo_y with htwo | hy
  · norm_num at htwo
  · exact hy0 hy

private theorem awayCarrierReconstruction_of_right_chart {carrier : ℕ}
    {x z : ℕ} (pack : CounterexamplePack x carrier z)
    (hcarrier : 7 ∣ carrier) :
    AwayCarrierReconstruction carrier := by
  rcases coordinateCounterexampleRoute_of_pack pack with ⟨route⟩
  cases route with
  | ramified p => exact False.elim (not_ramified_right_chart p hcarrier)
  | away p =>
      rcases nonempty_awayValuationTransferPacket p with ⟨q⟩
      cases q.source with
      | right hy hz hsum hmatch =>
          exact ⟨x, carrier, z, q, hmatch⟩
      | left hz hy hsum hmatch => exact False.elim (hy hcarrier)
      | sum hsum hy hz hmatch => exact False.elim (hy hcarrier)

private theorem awayCarrierReconstruction_of_left_chart {carrier : ℕ}
    {x y : ℕ} (pack : CounterexamplePack x y carrier)
    (hcarrier : 7 ∣ carrier) :
    AwayCarrierReconstruction carrier := by
  rcases coordinateCounterexampleRoute_of_pack pack with ⟨route⟩
  cases route with
  | ramified p => exact False.elim (not_ramified_left_chart p hcarrier)
  | away p =>
      rcases nonempty_awayValuationTransferPacket p with ⟨q⟩
      cases q.source with
      | right hy hz hsum hmatch => exact False.elim (hz hcarrier)
      | left hz hy hsum hmatch =>
          exact ⟨x, y, carrier, q, hmatch⟩
      | sum hsum hy hz hmatch => exact False.elim (hz hcarrier)

private theorem awayCarrierReconstruction_of_sum_chart {carrier : ℕ}
    {x y z : ℕ} (pack : CounterexamplePack x y z)
    (hcarrier : y + z = carrier) (hseven : 7 ∣ carrier) :
    AwayCarrierReconstruction carrier := by
  rcases coordinateCounterexampleRoute_of_pack pack with ⟨route⟩
  cases route with
  | ramified p =>
      exact False.elim (not_ramified_sum_chart p hcarrier hseven)
  | away p =>
      rcases nonempty_awayValuationTransferPacket p with ⟨q⟩
      cases q.source with
      | right hy hz hsum hmatch => exact False.elim (hsum (by simpa [hcarrier] using hseven))
      | left hz hy hsum hmatch => exact False.elim (hsum (by simpa [hcarrier] using hseven))
      | sum hsum hy hz hmatch =>
          exact ⟨x, y, z, q, hmatch.trans hcarrier⟩

theorem fermatChart_to_awayCarrierReconstruction {carrier : ℕ}
    (h : AwayCarrierFermatChart carrier) :
    AwayCarrierReconstruction carrier := by
  cases h with
  | right pack hcarrier =>
      exact awayCarrierReconstruction_of_right_chart pack hcarrier
  | left pack hcarrier =>
      exact awayCarrierReconstruction_of_left_chart pack hcarrier
  | sum pack hcarrier hseven =>
      exact awayCarrierReconstruction_of_sum_chart pack hcarrier hseven

theorem awayCarrierReconstruction_iff_fermatChart {carrier : ℕ} :
    AwayCarrierReconstruction carrier ↔ AwayCarrierFermatChart carrier :=
  ⟨awayCarrierReconstruction_to_fermatChart, fermatChart_to_awayCarrierReconstruction⟩

theorem awayCarrierReconstruction_additive_decomposition {carrier : ℕ}
    (h : AwayCarrierReconstruction carrier) :
    (∃ x z, CounterexamplePack x carrier z) ∨
      (∃ x y, CounterexamplePack x y carrier) ∨
      (∃ x y z, CounterexamplePack x y z ∧ y + z = carrier) := by
  rcases awayCarrierReconstruction_to_fermatChart h with hchart
  cases hchart with
  | right pack hseven => exact .inl ⟨_, _, pack⟩
  | left pack hseven => exact .inr (.inl ⟨_, _, pack⟩)
  | sum pack hcarrier hseven => exact .inr (.inr ⟨_, _, _, pack, hcarrier⟩)

theorem AwayCarrierFermatChart.left_bounds {x y carrier : ℕ}
    (pack : CounterexamplePack x y carrier) :
    x < carrier ∧ y < carrier := by
  have hyz := right_lt_of_fermat7Equation pack.hx pack.hEq
  have hxz := right_lt_of_fermat7Equation
    (x := y) (y := x) (z := carrier) pack.hy (by
      simpa [Fermat7Equation, Nat.add_comm] using pack.hEq)
  exact ⟨hxz, hyz⟩

theorem AwayCarrierFermatChart.sum_bounds {x y z carrier : ℕ}
    (pack : CounterexamplePack x y z) (hcarrier : y + z = carrier) :
    x < carrier ∧ y < carrier ∧ z < carrier := by
  have hyz := right_lt_of_fermat7Equation pack.hx pack.hEq
  have hxz := right_lt_of_fermat7Equation
    (x := y) (y := x) (z := z) pack.hy (by
      simpa [Fermat7Equation, Nat.add_comm] using pack.hEq)
  have hypos := pack.hy
  omega

theorem AwayCarrierFermatChart.right_bounds {x carrier z : ℕ}
    (pack : CounterexamplePack x carrier z) :
    carrier < z ∧ x < z := by
  have hyz := right_lt_of_fermat7Equation pack.hx pack.hEq
  have hxz := right_lt_of_fermat7Equation
    (x := carrier) (y := x) (z := z) pack.hy (by
      simpa [Fermat7Equation, Nat.add_comm] using pack.hEq)
  exact ⟨hyz, hxz⟩

theorem AwayValuationTransferPacket.no_fermatChart_at_depth_one
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z)
    (hdepth : padicValNat 7 p.carrier = 1) :
    ¬ AwayCarrierFermatChart (Int.natAbs p.normal.root.snd) := by
  intro hchart
  exact (p.no_reconstruction_at_depth_one hdepth)
    ((awayCarrierReconstruction_iff_fermatChart).mpr hchart)

end DkMath.FLT.Seven
