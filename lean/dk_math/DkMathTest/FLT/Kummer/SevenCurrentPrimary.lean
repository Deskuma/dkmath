/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentPrimary

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenRealGN
open DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open DkMath.Lib.Algebra
open SevenCyclotomicDegreeSixInt

namespace DkMathTest.FLT.Kummer.SevenCurrentPrimary

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- A nonunit root too satisfies the Frobenius lift whenever its residue is one.
example (w : C) : (7 : C) ∣ (1 + ramifiedUniformizer * w) ^ 7 - 1 := by
  apply seventh_sub_one_dvd_seven_of_residue_one
  simp

-- Merely being away from lambda is insufficient; the root -1 needs normalization.
example : ¬ (7 : C) ∣ (-1 : C) ^ 7 - 1 := by
  rw [seventh_sub_one_dvd_seven_iff_residue_one]
  norm_num; decide

-- The lift is a global unit, not just a ring element with the desired residue.
example : ∃ t : Cˣ, ramifiedEval (t : C) = 2 :=
  exists_unit_lift_ramifiedEval 2 (by decide)

-- A concrete root can be normalized with the same unit used in the product.
example : ∃ t : Cˣ, ramifiedEval ((t : C) * (-1 : C)) = 1 := by
  apply exists_root_residue_normalizer
  rw [← ramifiedEval_eq_zero_iff_dvd]
  norm_num

-- The previous chapter's AllowedGauge is exactly the subgroup with residue one.
example (t : AllowedGauge) : ramifiedEval (t.val : C) = 1 :=
  (seventh_sub_one_dvd_seven_iff_residue_one _).mp t.property

-- A nonzero local GN source exhibits the root-choice issue without an FLT hypothesis.
private noncomputable def P : PrimaryPacket := packetOfRealUnit (1 : Rˣ)

example : P.source ≠ 0 ∧ RealPrimary P.delta (-P.parameter) ∧
    ¬ RealPrimary (P.delta * (-1 : Cˣ)⁻¹ ^ 7) (-P.parameter) := by
  refine ⟨P.source_ne_zero, P.primary, ?_⟩
  have hf : realGNSource (0 : R) (-1) 1 = (zeta ^ 1 - 1) * ((P.delta : C) * P.gamma ^ 7) := P.factor
  have hu : SevenRealCubicInt.thetaResidue (-1) ≠ 0 := by norm_num
  have hb : ramifiedEval P.gamma = 1 := map_one _
  have hiff := primary_after_root_gauge_iff (by decide : 1 ∈ (Finset.range 7).erase 0)
    P.delta P.gamma (-1) (dvd_zero _) (dvd_zero _) hu hf hb
  change ¬ RealPrimary (P.delta * (-1 : Cˣ)⁻¹ ^ 7) (-(-1 : R))
  rw [hiff]
  norm_num; decide

-- The source equality survives the sign change even though its primary congruence fails.
example : P.source = (zeta ^ 1 - 1) *
    (((P.delta * (-1 : Cˣ)⁻¹ ^ 7 : Cˣ) : C) * (((-1 : Cˣ) : C) * P.gamma) ^ 7) :=
  P.factor.trans (root_unit_gauge_identity _ _ P.delta (-1) 7)

-- The exact feasibility criterion consumes both the weak-depth and away hypotheses.
example {x u : R} {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) (delta : Cˣ) (beta : C)
    (hx : ramifiedUniformizer ^ 2 ∣ ofReal x) (hu : SevenRealCubicInt.thetaResidue u ≠ 0)
    (hb : ¬ ramifiedUniformizer ∣ beta)
    (hf : realGNSource x u i = (zeta ^ i - 1) * ((delta : C) * beta ^ 7))
    (hno : ¬ (7 : C) * (zeta ^ i - 1) ∣ ofReal x) :
    ¬ ∃ t : Cˣ, RealPrimary (delta * t⁻¹ ^ 7) (-u) := by
  rw [exists_primary_root_gauge_iff_gap_divisible hi delta beta hx hu hb hf]
  exact hno

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

-- In the actual current packet the proposed exclusion test is satisfied, for every nontrivial phase.
example (p : DirectRealCubicRootPacket source r) :
    (7 : C) * (zeta ^ 2 - 1) ∣ ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) :=
  current_gap_seven_phase_dvd p (by decide)

-- The actual receiver now feeds the earlier finite-iteration theorem with the same current source.
example (c : CurrentCommonPrimeCyclotomicPacket h q) (ts : List AllowedGauge) :
    ∃ Q : PrimaryPacket, Q.source = currentLinearCarrier c ∧
      snapshot (iterate Q ts) = snapshot Q ∧
      RealPrimary (iterate Q ts).delta (-p.rho) ∧
      Fermat7Equation a b d := by
  obtain ⟨epsilon, beta, _, hext, hFermat⟩ := currentCarrier_primary_packet_receiver c
  obtain ⟨t, Q, _, hu, _, hsource, _, _, _, _⟩ := hext
  refine ⟨Q, hsource, (iterated_invariant_preservation Q ts).1, ?_, hFermat⟩
  rw [← hu]
  exact (iterated_invariant_preservation Q ts).2.1

end DkMathTest.FLT.Kummer.SevenCurrentPrimary
