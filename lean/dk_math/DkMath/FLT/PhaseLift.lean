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
def PrimitiveOnS0 (c b q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b

/--
`PrimitiveOnS0` な素数は `S0` を二乗では持ち上げない。
-/
def NonLiftableS0 (c b q : ℕ) : Prop :=
  PrimitiveOnS0 c b q → ¬ q ^ 2 ∣ S0_nat c b

/--
phase-04 の集約条件:
- `S0` を割る素数はすべて primitive 条件を満たす
- その primitive 素数はすべて non-liftable
-/
def AllNonLiftableOnS0 (c b : ℕ) : Prop :=
  (∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ∣ c - b)
    ∧ ∀ q : ℕ, NonLiftableS0 c b q

/--
`q = 3` を除いた素因子では `c-b` を割らない、という support 条件。
`q = 3` は別途 `¬ 3 ∣ S0_nat c b` などで扱う。
-/
def S0PrimeSupportExceptThree (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → q ≠ 3 → ¬ q ∣ c - b

/--
`c,b` がともに `mod 3` で非零、かつ同値類が異なるなら `3 ∤ S0_nat c b`。
-/
lemma not_three_dvd_S0_of_mod3_separated {c b : ℕ}
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    ¬ 3 ∣ S0_nat c b := by
  have hc_lt : c % 3 < 3 := Nat.mod_lt _ (by decide)
  have hb_lt : b % 3 < 3 := Nat.mod_lt _ (by decide)
  have hc_cases : c % 3 = 1 ∨ c % 3 = 2 := by omega
  have hb_cases : b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hc_cases with hc1 | hc2
  · rcases hb_cases with hb1 | hb2
    · exfalso
      exact hsep (by simp [hc1, hb1])
    · intro h3S0
      have hc_mod1 : c ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hc1
      have hb_mod2 : b ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hb2
      have hS0_mod_const : S0_nat c b ≡ (1 ^ 2 + 1 * 2 + 2 ^ 2) [MOD 3] := by
        unfold S0_nat
        exact ((hc_mod1.pow 2).add (hc_mod1.mul hb_mod2)).add (hb_mod2.pow 2)
      have hconst : ((1 ^ 2 + 1 * 2 + 2 ^ 2 : ℕ) ≡ 1 [MOD 3]) := by decide
      have hS0_mod1 : S0_nat c b ≡ 1 [MOD 3] := hS0_mod_const.trans hconst
      have hS0_mod0 : S0_nat c b ≡ 0 [MOD 3] := h3S0.modEq_zero_nat
      have h10 : (1 : ℕ) ≡ 0 [MOD 3] := hS0_mod1.symm.trans hS0_mod0
      norm_num [Nat.ModEq] at h10
  · rcases hb_cases with hb1 | hb2
    · intro h3S0
      have hc_mod2 : c ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hc2
      have hb_mod1 : b ≡ 1 [MOD 3] := by simpa [Nat.ModEq] using hb1
      have hS0_mod_const : S0_nat c b ≡ (2 ^ 2 + 2 * 1 + 1 ^ 2) [MOD 3] := by
        unfold S0_nat
        exact ((hc_mod2.pow 2).add (hc_mod2.mul hb_mod1)).add (hb_mod1.pow 2)
      have hconst : ((2 ^ 2 + 2 * 1 + 1 ^ 2 : ℕ) ≡ 1 [MOD 3]) := by decide
      have hS0_mod1 : S0_nat c b ≡ 1 [MOD 3] := hS0_mod_const.trans hconst
      have hS0_mod0 : S0_nat c b ≡ 0 [MOD 3] := h3S0.modEq_zero_nat
      have h10 : (1 : ℕ) ≡ 0 [MOD 3] := hS0_mod1.symm.trans hS0_mod0
      norm_num [Nat.ModEq] at h10
    · exfalso
      exact hsep (by simp [hc2, hb2])

/--
`q = 3` 例外を除去できると、通常の support 条件へ戻せる。
-/
lemma allPrimeSupport_of_exceptThree {c b : ℕ}
    (hSupp : S0PrimeSupportExceptThree c b)
    (h3free : ¬ 3 ∣ S0_nat c b) :
    ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ∣ c - b := by
  intro q hq hqS0
  by_cases hq3 : q = 3
  · intro hqdiff
    have h3S0 : 3 ∣ S0_nat c b := by simpa [hq3] using hqS0
    exact h3free h3S0
  · exact hSupp hq hqS0 hq3

/--
phase-04 補助集約:
`q=3` 例外分離版の support + non-liftable + `3` 非出現 から
`AllNonLiftableOnS0` を構成する。
-/
def AllNonLiftableOnS0ExceptThree (c b : ℕ) : Prop :=
  S0PrimeSupportExceptThree c b ∧ (∀ q : ℕ, NonLiftableS0 c b q) ∧ ¬ 3 ∣ S0_nat c b

lemma AllNonLiftableOnS0_of_exceptThree {c b : ℕ}
    (h : AllNonLiftableOnS0ExceptThree c b) : AllNonLiftableOnS0 c b := by
  rcases h with ⟨hSuppEx3, hNonLift, h3free⟩
  refine ⟨allPrimeSupport_of_exceptThree hSuppEx3 h3free, hNonLift⟩

/--
`mod 3` 分離条件から `3` 例外を自動で埋めて
`AllNonLiftableOnS0` へ接続する補助補題。
-/
lemma AllNonLiftableOnS0_of_exceptThree_mod3_separated {c b : ℕ}
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    AllNonLiftableOnS0 c b := by
  have h3free : ¬ 3 ∣ S0_nat c b :=
    not_three_dvd_S0_of_mod3_separated hc_nz hb_nz hsep
  exact AllNonLiftableOnS0_of_exceptThree ⟨hSuppEx3, hNonLift, h3free⟩

lemma NoSqOnS0_of_AllNonLiftableOnS0 {c b : ℕ}
    (hAll : AllNonLiftableOnS0 c b) : NoSqOnS0 c b := by
  intro q hq hqS0
  rcases hAll with ⟨hprimSupport, hnonlift⟩
  have hq_ndvd : ¬ q ∣ c - b := hprimSupport hq hqS0
  have hprim : PrimitiveOnS0 c b q := ⟨hq, hqS0, hq_ndvd⟩
  exact hnonlift q hprim

/--
phase-03-C の十分条件（phase-04 更新）:
非例外調和点 witness と `AllNonLiftableOnS0` の組。
-/
def NonExceptionalHarmonicOnS0 (c b : ℕ) : Prop :=
  (∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) ∧ AllNonLiftableOnS0 c b

lemma AllNonLiftableOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : AllNonLiftableOnS0 c b := by
  exact h.2

lemma NoSqOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : NoSqOnS0 c b := by
  exact NoSqOnS0_of_AllNonLiftableOnS0 (AllNonLiftableOnS0_of_nonExceptionalHarmonic h)

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
