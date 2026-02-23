/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalDetect
import DkMath.FLT.OctagonCore
import DkMath.FLT.CosmicPetalBridge
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.FLT.PetalCoreUnit
import DkMath.Units.NPUnit
import DkMath.NumberTheory.GcdNext
import DkMath.ABC.PadicValNat

namespace DkMath.FLT

open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.GcdNext

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
phase-06: `Main` の入口仮定を圧縮するための入力束。
`NoSqOnS0` ルートで必要な幾何・数論条件をまとめる。
-/
structure Phase6NoSqInput (c b : ℕ) where
  hbc : b < c
  hcb_coprime : Nat.Coprime c b
  hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u
  hNoSq : NoSqOnS0 c b
  hc_nz : c % 3 ≠ 0
  hb_nz : b % 3 ≠ 0
  hsep : c % 3 ≠ b % 3

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
`q ≠ 3` かつ `q ∣ S0(c,b)` と `gcd(c,b)=1` なら `q ∤ (c-b)`。
（`b ≤ c` を仮定）
-/
lemma prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three {c b q : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (hq : Nat.Prime q)
    (hqS0 : q ∣ S0_nat c b)
    (hq_ne3 : q ≠ 3) :
    ¬ q ∣ c - b := by
  intro hq_sub
  have hcb_mod : c ≡ b [MOD q] := by
    exact ((Nat.modEq_iff_dvd' hbc).2 hq_sub).symm
  have hS0_mod3b2 : S0_nat c b ≡ 3 * b ^ 2 [MOD q] := by
    have h1 : S0_nat c b ≡ b ^ 2 + b * b + b ^ 2 [MOD q] := by
      unfold S0_nat
      exact ((hcb_mod.pow 2).add (hcb_mod.mul Nat.ModEq.rfl)).add Nat.ModEq.rfl
    have h2 : b ^ 2 + b * b + b ^ 2 = 3 * b ^ 2 := by
      ring
    exact h2 ▸ h1
  have hS0_mod0 : S0_nat c b ≡ 0 [MOD q] := hqS0.modEq_zero_nat
  have h3b2_mod0 : 3 * b ^ 2 ≡ 0 [MOD q] := hS0_mod3b2.symm.trans hS0_mod0
  have hq_3b2 : q ∣ 3 * b ^ 2 := Nat.modEq_zero_iff_dvd.mp h3b2_mod0
  rcases hq.dvd_mul.mp hq_3b2 with hq_three | hq_b2
  · have hq_eq_three : q = 3 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hq_three
    exact hq_ne3 hq_eq_three
  · have hq_b : q ∣ b := hq.dvd_of_dvd_pow hq_b2
    have hb_mod0 : b ≡ 0 [MOD q] := hq_b.modEq_zero_nat
    have hc_mod0 : c ≡ 0 [MOD q] := hcb_mod.trans hb_mod0
    have hq_c : q ∣ c := Nat.modEq_zero_iff_dvd.mp hc_mod0
    have hq_gcd : q ∣ Nat.gcd c b := Nat.dvd_gcd hq_c hq_b
    have hq_one : q ∣ 1 := by simpa [hcop.gcd_eq_one] using hq_gcd
    exact hq.not_dvd_one hq_one

/--
`hSuppEx3` の自動生成ブリッジ:
`b ≤ c` と `gcd(c,b)=1` から `S0PrimeSupportExceptThree c b` を得る。
-/
lemma s0PrimeSupportExceptThree_of_coprime {c b : ℕ}
    (hbc : b ≤ c) (hcop : Nat.Coprime c b) :
    S0PrimeSupportExceptThree c b := by
  intro q hq hqS0 hq_ne3
  exact prime_not_dvd_sub_of_prime_dvd_S0_coprime_ne_three hbc hcop hq hqS0 hq_ne3

lemma phase6_s0PrimeSupportExceptThree {c b : ℕ}
    (h : Phase6NoSqInput c b) :
    S0PrimeSupportExceptThree c b := by
  exact s0PrimeSupportExceptThree_of_coprime h.hbc.le h.hcb_coprime

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
`NoSqOnS0` から `q` 全域の non-liftable 条件を得る。
-/
lemma nonLiftableS0_all_of_NoSqOnS0 {c b : ℕ}
    (hNoSq : NoSqOnS0 c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q hprim
  exact hNoSq hprim.1 hprim.2.1

/--
`NoSqOnS0` と support 条件から `AllNonLiftableOnS0` を作る。
-/
lemma AllNonLiftableOnS0_of_NoSqOnS0_support {c b : ℕ}
    (hSupport : ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → ¬ q ∣ c - b)
    (hNoSq : NoSqOnS0 c b) :
    AllNonLiftableOnS0 c b := by
  exact ⟨hSupport, nonLiftableS0_all_of_NoSqOnS0 hNoSq⟩

/--
phase-03-C の十分条件（phase-04 更新）:
非例外調和点 witness と `AllNonLiftableOnS0` の組。
-/
def NonExceptionalHarmonicOnS0 (c b : ℕ) : Prop :=
  (∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) ∧ AllNonLiftableOnS0 c b

lemma AllNonLiftableOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : AllNonLiftableOnS0 c b := by
  exact h.2

lemma nonExceptionalHarmonicOnS0_of_allNonLiftable {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hAll : AllNonLiftableOnS0 c b) :
    NonExceptionalHarmonicOnS0 c b := by
  exact ⟨hHarm, hAll⟩

/--
Harmonic witness と `mod 3` 分離条件つき `ExceptThree` 構成から
`NonExceptionalHarmonicOnS0` を作る phase-04 入口補題。
-/
lemma nonExceptionalHarmonicOnS0_of_exceptThree_mod3_separated {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    NonExceptionalHarmonicOnS0 c b := by
  have hAll : AllNonLiftableOnS0 c b :=
    AllNonLiftableOnS0_of_exceptThree_mod3_separated hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact nonExceptionalHarmonicOnS0_of_allNonLiftable hHarm hAll

lemma NoSqOnS0_of_nonExceptionalHarmonic {c b : ℕ}
    (h : NonExceptionalHarmonicOnS0 c b) : NoSqOnS0 c b := by
  exact NoSqOnS0_of_AllNonLiftableOnS0 (AllNonLiftableOnS0_of_nonExceptionalHarmonic h)

/--
`ExceptThree` の phase-04 入口条件から直接 `NoSqOnS0` を得る。
-/
lemma NoSqOnS0_of_exceptThree_mod3_separated_harmonic {c b : ℕ}
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_nonExceptionalHarmonic
    (nonExceptionalHarmonicOnS0_of_exceptThree_mod3_separated
      hHarm hSuppEx3 hNonLift hc_nz hb_nz hsep)

/--
`a^3 + b^3 = c^3` から `c^3 - b^3 = a^3` を得る。
-/
lemma cube_sub_eq_of_add_eq {a b c : ℕ} (h : a ^ 3 + b ^ 3 = c ^ 3) :
    c ^ 3 - b ^ 3 = a ^ 3 := by
  rw [← h]
  omega

/--
`gcd(a,b)=1` かつ `a^3+b^3=c^3` なら `gcd(c,b)=1`。
-/
lemma coprime_cb_of_eq {a b c : ℕ}
    (hab : Nat.Coprime a b) (h : a ^ 3 + b ^ 3 = c ^ 3) :
    Nat.Coprime c b := by
  by_contra hnot
  have hgcd_ne : Nat.gcd c b ≠ 1 := by
    intro hg
    apply hnot
    exact (Nat.coprime_iff_gcd_eq_one).2 hg
  obtain ⟨p, hp, hp_dvd_g⟩ := Nat.exists_prime_and_dvd hgcd_ne
  have hp_dvd_c : p ∣ c := dvd_trans hp_dvd_g (Nat.gcd_dvd_left c b)
  have hp_dvd_b : p ∣ b := dvd_trans hp_dvd_g (Nat.gcd_dvd_right c b)
  have hp_dvd_c3 : p ∣ c ^ 3 := dvd_trans hp_dvd_c (dvd_pow_self c (by decide : 3 ≠ 0))
  have hp_dvd_b3 : p ∣ b ^ 3 := dvd_trans hp_dvd_b (dvd_pow_self b (by decide : 3 ≠ 0))
  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq h
  have hp_dvd_sub : p ∣ c ^ 3 - b ^ 3 := Nat.dvd_sub hp_dvd_c3 hp_dvd_b3
  have hp_dvd_a3 : p ∣ a ^ 3 := by simpa [hsub] using hp_dvd_sub
  have hp_dvd_a : p ∣ a := hp.dvd_of_dvd_pow hp_dvd_a3
  have hp_dvd_gab : p ∣ Nat.gcd a b := Nat.dvd_gcd hp_dvd_a hp_dvd_b
  have : p ∣ 1 := by simpa [hab.gcd_eq_one] using hp_dvd_gab
  exact hp.not_dvd_one this

/--
`3 ∣ (c-b)` 分岐専用:
`b < c`, `0 < b`, `Nat.Coprime c b`, `3 ∣ c-b` から
`q ∣ (c^3-b^3)` かつ `q ∤ (c-b)` を満たす素数 `q` が存在する。
-/
lemma exists_prime_factor_cube_diff_of_three_dvd_sub {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) (h3 : 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  rcases h3 with ⟨k, hk⟩
  have hdiff_pos : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hk_pos : 0 < k := by
    have : 0 < 3 * k := by simpa [hk] using hdiff_pos
    exact Nat.pos_of_mul_pos_left this
  have hc_eq : c = 3 * k + b := by
    calc
      c = (c - b) + b := (Nat.sub_add_cancel hbc.le).symm
      _ = 3 * k + b := by simp only [hk]
  let m : ℕ := 3 * k ^ 2 + 3 * k * b + b ^ 2
  have hm_gt1 : 1 < m := by
    have hk2_pos : 0 < k ^ 2 := by positivity
    have hb2_pos : 0 < b ^ 2 := by positivity
    dsimp [m]
    omega
  obtain ⟨q, hq, hq_dvd_m⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hm_gt1)
  have h3_ndvd_b : ¬ 3 ∣ b := by
    intro h3b
    have h3c : 3 ∣ c := by
      have : 3 ∣ (c - b) + b := dvd_add (by exact ⟨k, hk⟩) h3b
      simpa [Nat.sub_add_cancel hbc.le] using this
    have h3gcd : 3 ∣ Nat.gcd c b := Nat.dvd_gcd h3c h3b
    have h3one : 3 ∣ 1 := by
      simp only [hcop.gcd_eq_one, Nat.dvd_one, OfNat.ofNat_ne_one] at h3gcd
    exact Nat.prime_three.not_dvd_one h3one
  have h3_ndvd_m : ¬ 3 ∣ m := by
    intro h3m
    have h3_dvd_t1 : 3 ∣ 3 * k ^ 2 := by
      simp only [dvd_mul_right]
    have h3_dvd_t2 : 3 ∣ 3 * k * b := by
      have : 3 ∣ 3 * k := by
        simp only [dvd_mul_right]
      exact dvd_mul_of_dvd_left this b
    have h3_dvd_sum12 : 3 ∣ 3 * k ^ 2 + 3 * k * b := dvd_add h3_dvd_t1 h3_dvd_t2
    have hm_eq : m = (3 * k ^ 2 + 3 * k * b) + b ^ 2 := by
      rfl
    have h3_dvd_b2 : 3 ∣ b ^ 2 := by
      exact (Nat.dvd_add_right h3_dvd_sum12).1 (by simpa [hm_eq] using h3m)
    have h3b : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow h3_dvd_b2
    exact h3_ndvd_b h3b
  have hq_ndvd_three : ¬ q ∣ 3 := by
    intro hq3
    have hq_eq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hq3
    exact h3_ndvd_m (hq_eq3 ▸ hq_dvd_m)
  have hq_ndvd_k : ¬ q ∣ k := by
    intro hqk
    have hm_eq : m = k * (3 * k + 3 * b) + b ^ 2 := by
      dsimp [m]
      ring
    have hq_dvd_prod : q ∣ k * (3 * k + 3 * b) := dvd_mul_of_dvd_left hqk _
    have hq_dvd_b2 : q ∣ b ^ 2 := by
      exact (Nat.dvd_add_right hq_dvd_prod).1 (by simpa [hm_eq] using hq_dvd_m)
    have hq_dvd_b : q ∣ b := hq.dvd_of_dvd_pow hq_dvd_b2
    have hq_dvd_c : q ∣ c := by
      have hq_dvd_3k : q ∣ 3 * k := dvd_mul_of_dvd_right hqk 3
      have : q ∣ 3 * k + b := dvd_add hq_dvd_3k hq_dvd_b
      simpa [hc_eq] using this
    have : q ∣ Nat.gcd c b := Nat.dvd_gcd hq_dvd_c hq_dvd_b
    have : q ∣ 1 := by simpa [hcop.gcd_eq_one] using this
    exact hq.not_dvd_one this
  have hq_ndvd_diff : ¬ q ∣ c - b := by
    intro hqd
    have hq_dvd_3k : q ∣ 3 * k := by simpa [hk] using hqd
    rcases hq.dvd_mul.mp hq_dvd_3k with hq3 | hqk
    · exact hq_ndvd_three hq3
    · exact hq_ndvd_k hqk
  have hS0 : S0_nat c b = 3 * m := by
    unfold S0_nat
    dsimp [m]
    rw [hc_eq]
    ring
  have hq_dvd_S0 : q ∣ S0_nat c b := by
    have : q ∣ 3 * m := dvd_mul_of_dvd_right hq_dvd_m 3
    simpa [hS0] using this
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
    simpa [S0_nat] using hdiff
  have hq_dvd_diff : q ∣ c ^ 3 - b ^ 3 := by
    rw [hfact]
    exact dvd_mul_of_dvd_right hq_dvd_S0 (c - b)
  exact ⟨q, hq, hq_dvd_diff, hq_ndvd_diff⟩

/--
`¬ 3 ∣ (c-b)` 分岐専用:
Zsigmondy の原始素因子存在をそのまま `d=3` に適用する。
-/
lemma exists_prime_factor_cube_diff_of_not_three_dvd_sub {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  exact DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_prime
    Nat.prime_three (by norm_num : 3 ≤ 3) hbc hb hcop h3

lemma exists_primitive_prime_factor_d3 {a b : ℕ}
    (hab : Nat.Coprime a b) (hb : 0 < b) (ha : b < a)
    (hpnd : ¬ 3 ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a ^ 3 - b ^ 3 ∧ ¬ q ∣ a - b := by
  exact exists_prime_factor_cube_diff_of_not_three_dvd_sub ha hb hab hpnd

/--
`c > b` かつ `gcd(c,b)=1` のとき、
`q ∣ (c^3-b^3)` かつ `q ∤ (c-b)` を満たす素数 `q` が存在。
`3 ∣ (c-b)` / `¬ 3 ∣ (c-b)` の両分岐を内包した共通補題。
-/
lemma exists_prime_factor_cube_diff {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ c ^ 3 - b ^ 3 ∧ ¬ q ∣ c - b := by
  by_cases h3 : 3 ∣ c - b
  · exact exists_prime_factor_cube_diff_of_three_dvd_sub hbc hb hcop h3
  · exact exists_prime_factor_cube_diff_of_not_three_dvd_sub hbc hb hcop h3

/--
`d=3` の標準因数分解:
`c^3 - b^3 = (c-b) * S0_nat c b`。
-/
lemma cube_sub_eq_mul_sub_S0 {c b : ℕ} (hbc : b < c) :
    c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  simpa [S0_nat] using hdiff

/--
`q ∣ (c^3-b^3)` かつ `q ∤ (c-b)` なら `q ∣ S0_nat c b`。
-/
lemma prime_dvd_S0_of_dvd_cube_sub_not_dvd_diff {c b q : ℕ}
    (hbc : b < c)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ c ^ 3 - b ^ 3)
    (hq_ndvd : ¬ q ∣ c - b) :
    q ∣ S0_nat c b := by
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b :=
    cube_sub_eq_mul_sub_S0 hbc
  have hmul : q ∣ (c - b) * S0_nat c b := by
    simpa [hfact] using hq_dvd
  exact (hq.dvd_mul.mp hmul).resolve_left hq_ndvd

/--
一般 `two_gap_xy_factor`（Nat `dvd` 版）から得る d=3 橋補題:
`x=c-b, y=b` とおくと `(c-b)*b` は
`c^3 - (c-b)^3 - b^3` を割る。
-/
lemma two_gap_xy_dvd_cube_bridge {c b : ℕ}
    (hbc : b ≤ c) :
    (c - b) * b ∣ c ^ 3 - (c - b) ^ 3 - b ^ 3 := by
  have hdiv :
      (c - b) * b ∣ (((c - b) + b) ^ (1 + 2) - (c - b) ^ (1 + 2) - b ^ (1 + 2)) :=
    DkMath.CosmicFormulaBinom.two_gap_xy_factor_nat_dvd 1 (c - b) b
  simpa [Nat.sub_add_cancel hbc] using hdiv

/--
`¬ q² ∣ S0(a,b)` をそのまま返す薄いラッパー。
-/
lemma S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb {a b q : ℕ}
    (_ha_pos : 0 < a) (_hb_pos : 0 < b)
    (_hab_coprime : Nat.Coprime a b)
    (_hq : Nat.Prime q)
    (_hS0_dvd : q ∣ S0_nat a b)
    (_hq_not_apb : ¬ q ∣ a + b)
    (hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b) :
    ¬ q ^ 2 ∣ S0_nat a b := by
  exact hq_not_sq

/--
`q ∣ c` なら `3 ≤ padicValNat q (c^3)`。
-/
lemma padicValNat_lower_bound_of_dvd_d3 {c q : ℕ}
    (hc_pos : 0 < c)
    (hq : Nat.Prime q)
    (hq_dvd_c : q ∣ c) :
    3 ≤ padicValNat q (c ^ 3) := by
  have h_c_ne : c ≠ 0 := Nat.ne_of_gt hc_pos
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_c_ge_1 : 1 ≤ padicValNat q c := by
    have h_ne_zero : padicValNat q c ≠ 0 := by
      intro h
      have : ¬ q ∣ c := by
        rcases padicValNat.eq_zero_iff.mp h with hq1 | hc0 | hqndvd
        · exact (hq.ne_one hq1).elim
        · exact (h_c_ne hc0).elim
        · exact hqndvd
      exact this hq_dvd_c
    omega
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c :=
    padicValNat.pow (n := 3) h_c_ne
  rw [h_val_pow]
  omega

/--
`q ∣ (a^3-b^3)` かつ `q ∤ (a-b)` と `¬ q² ∣ S0(a,b)` から
`padicValNat q (a^3-b^3) ≤ 1`。
-/
lemma padicValNat_upper_bound_d3 {a b q : ℕ}
    (hab_lt : b < a)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ a ^ 3 - b ^ 3)
    (hq_ndiv_diff : ¬ q ∣ a - b)
    (hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  have hS0_dvd : q ∣ S0_nat a b :=
    prime_dvd_S0_via_cosmic_bridge hab_lt hq hq_dvd hq_ndiv_diff
  have h_fact : a ^ 3 - b ^ 3 = (a - b) * S0_nat a b :=
    cube_sub_eq_mul_sub_S0 hab_lt
  have hpadic_bound : padicValNat q (S0_nat a b) ≤ 1 :=
    padicValNat_le_one_of_not_sq_dvd a b q ha_pos hb_pos hq hq_not_sq
  have ha_minus_b_ne_zero : a - b ≠ 0 := Nat.sub_ne_zero_of_lt hab_lt
  have hS0_ne_zero : S0_nat a b ≠ 0 := by
    unfold S0_nat
    have ha2_pos : 0 < a ^ 2 := by positivity
    have hab_pos : 0 < a * b := by positivity
    have hb2_pos : 0 < b ^ 2 := by positivity
    omega
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_diff_zero : padicValNat q (a - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_ndiv_diff
  have h_val_mult : padicValNat q (a ^ 3 - b ^ 3) =
      padicValNat q (a - b) + padicValNat q (S0_nat a b) :=
    congrArg (padicValNat q) h_fact ▸ padicValNat.mul ha_minus_b_ne_zero hS0_ne_zero
  calc padicValNat q (a ^ 3 - b ^ 3)
      = padicValNat q (a - b) + padicValNat q (S0_nat a b) := h_val_mult
    _ = padicValNat q (S0_nat a b) := by simp [h_val_diff_zero]
    _ ≤ 1 := hpadic_bound

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
