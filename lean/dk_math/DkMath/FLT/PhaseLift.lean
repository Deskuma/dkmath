/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalDetect
import DkMath.FLT.OctagonCore
import DkMath.FLT.CosmicPetalBridge
import DkMath.FLT.PetalCoreUnit
import DkMath.Units.NPUnit

namespace DkMath.FLT

open DkMath.FLT.PetalDetect

/--
OctagonCore 由来の混合位相点が存在することを入口条件としてまとめる述語。
-/
def HasMixedPhaseWitness : Prop :=
  ∃ p : Point2, isMixedPhasePoint p

lemma hasMixedPhaseWitness_octagonCore : HasMixedPhaseWitness := by
  exact ⟨I, mixedPoint_I⟩

/--
`NPUnit` 側の half-step（`succ` で 1/2 進む）証拠。
-/
def HasNPHalfStepWitness : Prop :=
  ∃ u : DkMath.NP, DkMath.val (DkMath.succ u) = DkMath.val u + (1 / 2 : ℚ)

lemma hasNPHalfStepWitness_npunit : HasNPHalfStepWitness := by
  refine ⟨DkMath.zero, ?_⟩
  simpa using DkMath.val_succ DkMath.zero

/--
判定器で使う位相インフラ（幾何側 witness と単位側 witness の組）。
-/
def HasPhaseUnitInfrastructure : Prop :=
  HasMixedPhaseWitness ∧ HasNPHalfStepWitness

lemma hasPhaseUnitInfrastructure : HasPhaseUnitInfrastructure := by
  exact ⟨hasMixedPhaseWitness_octagonCore, hasNPHalfStepWitness_npunit⟩

/--
`S0_nat c b` の素因子が二乗で刺さらないことをまとめた条件。
-/
def NoSqOnS0 (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ^ 2 ∣ S0_nat c b

/--
phase-03-C の十分条件（skeleton）:
非例外調和点 witness と `NoSqOnS0` の組。
-/
def NonExceptionalHarmonicOnS0 (c b : ℕ) : Prop :=
  (∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) ∧ NoSqOnS0 c b

lemma NoSqOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : NoSqOnS0 c b := by
  exact h.2

/--
`q ∣ (c^3-b^3)` かつ `q ∤ (c-b)` なら `q ∣ S0_nat c b`。
-/
lemma prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff {c b q : ℕ}
    (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_ndvd : ¬ q ∣ c - b) :
    q ∣ S0_nat c b := by
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
    simpa [S0_nat] using hdiff
  have hmul : q ∣ (c - b) * S0_nat c b := by
    simpa [hfact] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

/--
`NoSqOnS0 c b` から `Main` で使う `hS0_not_sq` 形の仮定を作るブリッジ。
-/
lemma hS0_not_sq_of_NoSqOnS0 {c b : ℕ}
    (hNoSq : NoSqOnS0 c b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b := by
  intro q hq hq_dvd hq_ndvd
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hdiff_zero : c - b = 0 := Nat.sub_eq_zero_of_le hcb
    exact hq_ndvd (hdiff_zero ▸ dvd_zero q)
  have hqS0 : q ∣ S0_nat c b :=
    prime_dvd_S0_via_cosmic_bridge hbc hq hq_dvd hq_ndvd
  exact hNoSq hq hqS0

end DkMath.FLT
