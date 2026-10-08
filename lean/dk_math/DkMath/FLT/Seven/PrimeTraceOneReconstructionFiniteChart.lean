/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionChart

#print "file: DkMath.FLT.Seven.PrimeTraceOneReconstructionFiniteChart"

namespace DkMath.FLT.Seven

/-- A fixed positive summand bounds the other endpoint: the top term of the
geometric quotient gives `z^6 <= carrier^7`. -/
theorem CounterexamplePack.right_sixth_power_bound {x carrier z : ℕ}
    (pack : CounterexamplePack x carrier z) : z ^ 6 ≤ carrier ^ 7 := by
  have hxz := (AwayCarrierFermatChart.right_bounds pack).2
  let s := ∑ i ∈ Finset.range 7, z ^ i * x ^ (7 - 1 - i)
  have hterm : z ^ 6 ≤ s := by
    have h := Finset.single_le_sum (f := fun i => z ^ i * x ^ (7 - 1 - i))
      (fun i _ => Nat.zero_le _) (show 6 ∈ Finset.range 7 by decide)
    simpa [s] using h
  have hmul : s * (z - x) = carrier ^ 7 := by
    have h := geom_sum₂_mul_of_ge hxz.le 7
    change s * (z - x) = z ^ 7 - x ^ 7 at h
    rw [h, ← pack.hEq]
    exact Nat.add_sub_cancel_left _ _
  exact hterm.trans ((Nat.le_mul_of_pos_right s (Nat.sub_pos_of_lt hxz)).trans hmul.le)

/-- Both unknown natural endpoints of a prescribed-summand chart lie in a
finite quadratic window. This bound does not assert that a chart exists. -/
theorem CounterexamplePack.right_quadratic_bound {x carrier z : ℕ}
    (pack : CounterexamplePack x carrier z) : x < z ∧ z ≤ carrier ^ 2 := by
  refine ⟨(AwayCarrierFermatChart.right_bounds pack).2, ?_⟩
  by_contra h
  have hlt : carrier ^ 2 < z := Nat.lt_of_not_ge h
  have hp : (carrier ^ 2) ^ 6 < z ^ 6 :=
    (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mpr hlt
  have hle : carrier ^ 7 ≤ carrier ^ 12 :=
    pow_le_pow_right₀ (Nat.one_le_iff_ne_zero.mpr pack.hy.ne') (by decide)
  rw [← pow_mul] at hp
  norm_num at hp
  exact (not_lt_of_ge (hle.trans' pack.right_sixth_power_bound)) hp

/-- Kernel-decidable finite additive certificate. The first branch places the
carrier in the second summand, the second branch in the right-hand side.
The already excluded endpoint-sum branch is absent. -/
def prescribedCarrierFiniteCharts (carrier : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (carrier ^ 2)).product (Finset.Icc 1 (carrier ^ 2))).filter
    (fun a =>
      (Nat.Coprime a.1 carrier ∧ a.1 ^ 7 + carrier ^ 7 = a.2 ^ 7) ∨
      (Nat.Coprime a.1 a.2 ∧ a.1 ^ 7 + a.2 ^ 7 = carrier ^ 7))

theorem mem_prescribedCarrierFiniteCharts {carrier u v : ℕ} :
    (u, v) ∈ prescribedCarrierFiniteCharts carrier ↔
      (1 ≤ u ∧ u ≤ carrier ^ 2) ∧ (1 ≤ v ∧ v ≤ carrier ^ 2) ∧
        ((Nat.Coprime u carrier ∧ u ^ 7 + carrier ^ 7 = v ^ 7) ∨
          (Nat.Coprime u v ∧ u ^ 7 + v ^ 7 = carrier ^ 7)) := by
  simp [prescribedCarrierFiniteCharts, and_assoc]

/-- Every actual chart gives a bounded additive certificate, including the
previously unbounded prescribed-summand branch. -/
theorem AwayCarrierFermatChart.finiteCharts_nonempty {carrier : ℕ}
    (chart : AwayCarrierFermatChart carrier) :
    (prescribedCarrierFiniteCharts carrier).Nonempty := by
  cases chart with
  | right pack hseven =>
      have hb := pack.right_quadratic_bound
      have hx := pack.hx
      have hz := pack.hz
      exact ⟨(_, _), mem_prescribedCarrierFiniteCharts.mpr
        ⟨by omega, by omega, Or.inl ⟨pack.hxy, pack.hEq⟩⟩⟩
  | left pack hseven =>
      have hb := AwayCarrierFermatChart.left_bounds pack
      have hx := pack.hx
      have hy := pack.hy
      have hc : carrier ≤ carrier ^ 2 := le_self_pow₀
        (Nat.one_le_iff_ne_zero.mpr pack.hz.ne') (by decide)
      exact ⟨(_, _), mem_prescribedCarrierFiniteCharts.mpr
        ⟨by omega, by omega, Or.inr ⟨pack.hxy, pack.hEq⟩⟩⟩
  | sum pack heq hseven =>
      exact (AwayCarrierFermatChart.sum_impossible pack heq hseven).elim

/-- Only positivity and seven-divisibility of the prescribed carrier are
external. Each finite certificate supplies the primitive Fermat packet;
the existing chart bridge supplies the away root and valuation transfer. -/
theorem awayCarrierReconstruction_iff_finiteCharts {carrier : ℕ}
    (hpos : 0 < carrier) (hseven : 7 ∣ carrier) :
    AwayCarrierReconstruction carrier ↔
      (prescribedCarrierFiniteCharts carrier).Nonempty := by
  constructor
  · intro h
    exact (awayCarrierReconstruction_to_fermatChart h).finiteCharts_nonempty
  · rintro ⟨⟨u, v⟩, hm⟩
    rcases mem_prescribedCarrierFiniteCharts.mp hm with ⟨hu, hv, hadd⟩
    apply fermatChart_to_awayCarrierReconstruction
    rcases hadd with ⟨hcoprime, heq⟩ | ⟨hcoprime, heq⟩
    · exact .right ⟨by omega, hpos, by omega, hcoprime, heq⟩ hseven
    · exact .left ⟨by omega, by omega, hpos, hcoprime, heq⟩ hseven

end DkMath.FLT.Seven
