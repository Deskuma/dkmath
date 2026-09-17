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
