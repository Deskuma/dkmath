/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitHeight

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitGapHeight"

namespace DkMath.FLT.Seven

noncomputable section

open NumberField
open NumberField.InfinitePlace
open SevenRealCubicInt

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! ## One real embedding and its integral-model evaluation -/

noncomputable def chosenComplexEmbedding :
    SevenRealCubic.Field →+* ℂ :=
  Classical.choice (inferInstance : Nonempty (SevenRealCubic.Field →+* ℂ))

noncomputable def realEmbedding : SevenRealCubic.Field →+* ℝ :=
  ComplexEmbedding.IsReal.embedding
    (SevenRealCubic.isTotallyReal.complexEmbedding_isReal
      chosenComplexEmbedding)

noncomputable def realEval : SevenRealCubicInt →+* ℝ :=
  realEmbedding.comp
    (algebraMap (𝓞 SevenRealCubic.Field) SevenRealCubic.Field) |>.comp
    SevenRealCubic.modelToRingOfIntegers

@[simp] theorem realEval_ofInt (z : ℤ) :
    realEval (SevenRealCubicInt.ofInt z) = z := by
  simp [realEval, realEmbedding]

theorem realEval_cyclic_norm (x : SevenRealCubicInt) :
    realEval x * realEval (rotateEquiv x) *
        realEval (rotateEquiv (rotateEquiv x)) =
      (norm x : ℝ) := by
  have h := congrArg realEval
    (mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm x)
  simpa only [map_mul, map_intCast] using h

theorem realEval_seventhQuotient (x y : SevenRealCubicInt) :
    realEval (seventhQuotient x y) = H7 (realEval x) (realEval y) := by
  simp [seventhQuotient, H7]

theorem realEval_directOrbitGap (x : SevenRealCubicInt) :
    realEval (rotateEquiv x - x) =
      realEval (rotateEquiv x) - realEval x := by
  simp only [map_sub]

theorem realEval_directOrbitGap_hom (x : SevenRealCubicInt) :
    realEval (rotateHom x - x) =
      realEval (rotateHom x) - realEval x := by
  simpa only [rotateEquiv_apply] using realEval_directOrbitGap x

/-! ## Norm identities used by the gap-height comparison -/

theorem gapHeight_norm_orbitUnit01 : norm orbitUnit01 = 1 := by
  rw [orbitUnit01, pairAxisUnit_one]
  norm_num [SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
    SevenRealCubicInt.norm, alpha, alphaAddOneInv,
    thetaSevenUnit, eisensteinAxisUnitInv, mul, pow_succ]

def gapHeight_orbitW (a : ℕ) : SevenRealCubicInt :=
  eisensteinAxis ^ 5 * thetaSevenUnit *
    (a : SevenRealCubicInt) ^ 2

theorem gapHeight_norm_orbitW (a : ℕ) :
    norm (gapHeight_orbitW a) = 7 ^ 5 * (a : ℤ) ^ 6 := by
  have hu : norm thetaSevenUnit = -1 := by
    norm_num [thetaSevenUnit, SevenRealCubicInt.norm,
      eisensteinAxisUnitInv, mul, pow_succ]
  simp only [gapHeight_orbitW, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, norm_eisensteinAxis, hu]
  have ha : norm (a : SevenRealCubicInt) = (a : ℤ) ^ 3 := by
    exact norm_intCast a
  rw [ha]
  ring

theorem gapHeight_natAbs_norm_unit (u : SevenRealCubicIntˣ) :
    Int.natAbs (norm (u : SevenRealCubicInt)) = 1 := by
  have hmul :
      (u : SevenRealCubicInt) * (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
    simp
  have hnorm_one : norm (1 : SevenRealCubicInt) = 1 := by
    norm_num [SevenRealCubicInt.norm]
  have hnorm :
      norm (u : SevenRealCubicInt) *
          norm (↑(u⁻¹) : SevenRealCubicInt) = 1 := by
    simpa only [SevenRealCubicInt.norm_mul, norm_intCast, one_pow,
      hnorm_one] using congrArg norm hmul
  have hunitNorm : IsUnit (norm (u : SevenRealCubicInt)) :=
    IsUnit.of_mul_eq_one (norm (↑(u⁻¹) : SevenRealCubicInt)) hnorm
  exact Int.natAbs_of_isUnit hunitNorm

theorem rotate_seventhQuotient (x y : SevenRealCubicInt) :
    rotateEquiv (seventhQuotient x y) =
      seventhQuotient (rotateEquiv x) (rotateEquiv y) := by
  simp [seventhQuotient]

theorem realEval_gap_height_norm_inequality
    (x : SevenRealCubicInt) :
    (norm (rotateEquiv x - x) : ℝ) ^ 6 ≤
      64 ^ 3 * (norm (seventhQuotient (rotateEquiv x) x) : ℝ) := by
  let d₀ : ℝ := realEval (rotateEquiv x - x)
  let d₁ : ℝ := realEval (rotateEquiv (rotateEquiv x - x))
  let d₂ : ℝ := realEval (rotateEquiv (rotateEquiv (rotateEquiv x - x)))
  let h₀ : ℝ := realEval (seventhQuotient (rotateEquiv x) x)
  let h₁ : ℝ := realEval (rotateEquiv (seventhQuotient (rotateEquiv x) x))
  let h₂ : ℝ := realEval
    (rotateEquiv (rotateEquiv (seventhQuotient (rotateEquiv x) x)))
  have hd₀ : d₀ ^ 6 ≤ 64 * h₀ := by
    dsimp [d₀, h₀]
    rw [realEval_directOrbitGap_hom, realEval_seventhQuotient]
    simpa only [rotateEquiv_apply] using
      realH7_ge_gap (realEval (rotateHom x)) (realEval x)
  have hd₁ : d₁ ^ 6 ≤ 64 * h₁ := by
    have hd : rotateEquiv (rotateEquiv x - x) =
        rotateEquiv (rotateEquiv x) - rotateEquiv x := by
      simp only [map_sub]
    have hh : rotateEquiv (seventhQuotient (rotateEquiv x) x) =
        seventhQuotient (rotateEquiv (rotateEquiv x)) (rotateEquiv x) := by
      exact rotate_seventhQuotient _ _
    dsimp [d₁, h₁]
    change (realEval (rotateEquiv (rotateEquiv x - x))) ^ 6 ≤
      64 * realEval (rotateEquiv (seventhQuotient (rotateEquiv x) x))
    rw [hd, hh]
    simp only [map_sub]
    simpa only [realEval_seventhQuotient, rotateEquiv_apply] using
      realH7_ge_gap (realEval (rotateHom (rotateHom x)))
        (realEval (rotateHom x))
  have hd₂ : d₂ ^ 6 ≤ 64 * h₂ := by
    have hd : rotateEquiv (rotateEquiv (rotateEquiv x - x)) =
        x - rotateEquiv (rotateEquiv x) := by
      rw [show rotateEquiv (rotateEquiv (rotateEquiv x - x)) =
        rotateEquiv (rotateEquiv (rotateEquiv x)) -
          rotateEquiv (rotateEquiv x) by simp only [map_sub]]
      rw [rotateEquiv_three]
    have hh : rotateEquiv (rotateEquiv (seventhQuotient (rotateEquiv x) x)) =
        seventhQuotient x (rotateEquiv (rotateEquiv x)) := by
      rw [rotate_seventhQuotient, rotate_seventhQuotient, rotateEquiv_three]
    dsimp [d₂, h₂]
    change (realEval (rotateEquiv (rotateEquiv (rotateEquiv x - x)))) ^ 6 ≤
      64 * realEval (rotateEquiv (rotateEquiv
        (seventhQuotient (rotateEquiv x) x)))
    rw [hd, hh]
    simp only [map_sub]
    simpa only [realEval_seventhQuotient, rotateEquiv_apply] using
      realH7_ge_gap (realEval x) (realEval (rotateHom (rotateHom x)))
  have hnonneg₀ : 0 ≤ 64 * h₀ := by
    exact le_trans (by positivity : 0 ≤ d₀ ^ 6) hd₀
  have hnonneg₁ : 0 ≤ 64 * h₁ := by
    exact le_trans (by positivity : 0 ≤ d₁ ^ 6) hd₁
  have hnonneg₂ : 0 ≤ 64 * h₂ := by
    exact le_trans (by positivity : 0 ≤ d₂ ^ 6) hd₂
  have hprod₀₁ : d₀ ^ 6 * d₁ ^ 6 ≤ (64 * h₀) * (64 * h₁) := by
    exact mul_le_mul hd₀ hd₁ (by positivity) hnonneg₀
  have hprod : d₀ ^ 6 * d₁ ^ 6 * d₂ ^ 6 ≤
      (64 * h₀) * (64 * h₁) * (64 * h₂) := by  -- maxHeartbeats
    exact mul_le_mul hprod₀₁ hd₂ (by positivity) (by positivity)
  have hgap : d₀ * d₁ * d₂ = (norm (rotateEquiv x - x) : ℝ) := by
    dsimp [d₀, d₁, d₂]
    have h := realEval_cyclic_norm (rotateEquiv x - x)
    simpa only [map_sub, rotateEquiv_apply, rotateHom_three] using h
  have hquot : h₀ * h₁ * h₂ =
      (norm (seventhQuotient (rotateEquiv x) x) : ℝ) := by
    dsimp [h₀, h₁, h₂]
    have h := realEval_cyclic_norm
      (seventhQuotient (rotateEquiv x) x)
    simpa only [map_sub, rotateEquiv_apply] using h
  rw [← hgap, ← hquot]
  nlinarith [hprod]

theorem directOrbit_norm_product_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    norm (directOrbitGap p) * norm (directOrbitQuotient p) =
      7 ^ 35 * (r.summit.gapRoot : ℤ) ^ 42 := by
  rw [← SevenRealCubicInt.norm_mul, directOrbit_gap_mul_quotient,
    SevenRealCubicInt.norm_mul, gapHeight_norm_orbitUnit01,
    SevenRealCubicInt.norm_pow]
  have hw :
      eisensteinAxis ^ 5 * thetaSevenUnit *
          (r.summit.gapRoot : SevenRealCubicInt) ^ 2 =
        gapHeight_orbitW r.summit.gapRoot := rfl
  rw [hw, gapHeight_norm_orbitW]
  ring

theorem directOrbit_norms_pos
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    0 < norm (directOrbitGap p) ∧ 0 < norm (directOrbitQuotient p) := by
  have hineq := realEval_gap_height_norm_inequality p.rho
  have hquot_nonneg_real :
      0 ≤ (norm (directOrbitQuotient p) : ℝ) := by
    have hnonneg : 0 ≤ (norm (rotateEquiv p.rho - p.rho) : ℝ) ^ 6 := by
      positivity
    simpa only [directOrbitGap, directOrbitQuotient] using
      (show 0 ≤ (norm (seventhQuotient (rotateEquiv p.rho) p.rho) : ℝ) by
        nlinarith [hineq, hnonneg])
  have hquot_nonneg : 0 ≤ norm (directOrbitQuotient p) := by
    exact_mod_cast hquot_nonneg_real
  have hgapRoot_pos : 0 < (r.summit.gapRoot : ℤ) := by
    exact_mod_cast r.summit.gapRoot_pos
  have hprod_pos :
      0 < norm (directOrbitGap p) * norm (directOrbitQuotient p) := by
    rw [directOrbit_norm_product_eq p]
    positivity
  have hquot_pos : 0 < norm (directOrbitQuotient p) := by
    rcases lt_or_eq_of_le hquot_nonneg with h | h
    · exact h
    · rw [h.symm] at hprod_pos
      nlinarith
  have hgap_pos : 0 < norm (directOrbitGap p) := by
    by_contra h
    have hle : norm (directOrbitGap p) ≤ 0 := le_of_not_gt h
    nlinarith
  exact ⟨hgap_pos, hquot_pos⟩

theorem gapHeight_natAbs_norm_eisensteinAxis_pow (n : ℕ) :
    Int.natAbs (norm (eisensteinAxis ^ n)) = 7 ^ n := by
  rw [SevenRealCubicInt.norm_pow, norm_eisensteinAxis,
    Int.natAbs_pow]
  have h7 : Int.natAbs (-7 : ℤ) = 7 := by norm_num
  rw [h7]

theorem gapHeight_natAbs_norm_gapCore_eq
    {u : SevenRealCubicIntˣ} {g : SevenRealCubicInt} :
    Int.natAbs (norm ((u : SevenRealCubicInt) * g ^ 7)) =
      Int.natAbs (norm g) ^ 7 := by
  rw [SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
    Int.natAbs_mul, gapHeight_natAbs_norm_unit, one_mul,
    Int.natAbs_pow]

theorem directOrbit_natAbs_norm_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (s : DirectOrbitPowerSplitPacket p) :
    Int.natAbs (norm (directOrbitGap p)) =
      7 ^ (32 + 42 * s.gapSplit.k) *
        Int.natAbs (norm s.gapRoot) ^ 7 := by
  rw [s.gap_eq, SevenRealCubicInt.norm_mul, Int.natAbs_mul,
    gapHeight_natAbs_norm_eisensteinAxis_pow]
  rw [s.gapCore_eq, SevenRealCubicInt.norm_mul,
    SevenRealCubicInt.norm_pow, Int.natAbs_mul,
    gapHeight_natAbs_norm_unit, one_mul, Int.natAbs_pow]

theorem directOrbit_natAbs_norm_product_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Int.natAbs (norm (directOrbitGap p)) *
        Int.natAbs (norm (directOrbitQuotient p)) =
      7 ^ 35 * r.summit.gapRoot ^ 42 := by
  have hpos := directOrbit_norms_pos p
  have h := directOrbit_norm_product_eq p
  have hgap :
      (Int.natAbs (norm (directOrbitGap p)) : ℤ) =
        norm (directOrbitGap p) :=
    Int.natAbs_of_nonneg (le_of_lt hpos.1)
  have hquot :
      (Int.natAbs (norm (directOrbitQuotient p)) : ℤ) =
        norm (directOrbitQuotient p) :=
    Int.natAbs_of_nonneg (le_of_lt hpos.2)
  have hi :
      (Int.natAbs (norm (directOrbitGap p)) : ℤ) *
          Int.natAbs (norm (directOrbitQuotient p)) =
        7 ^ 35 * (r.summit.gapRoot : ℤ) ^ 42 := by
    rw [hgap, hquot]
    exact h
  exact_mod_cast hi

theorem directOrbit_natAbs_norm_gap_inequality
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Int.natAbs (norm (directOrbitGap p)) ^ 6 ≤
      64 ^ 3 * Int.natAbs (norm (directOrbitQuotient p)) := by
  have hpos := directOrbit_norms_pos p
  have h := realEval_gap_height_norm_inequality p.rho
  have hgap :
      (Int.natAbs (norm (directOrbitGap p)) : ℝ) =
        (norm (directOrbitGap p) : ℝ) := by
    have hnonnegR :
        (0 : ℝ) ≤ (norm (directOrbitGap p) : ℝ) := by
      exact_mod_cast (le_of_lt hpos.1)
    simp only [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hnonnegR]
  have hquot :
      (Int.natAbs (norm (directOrbitQuotient p)) : ℝ) =
        (norm (directOrbitQuotient p) : ℝ) := by
    have hnonnegR :
        (0 : ℝ) ≤ (norm (directOrbitQuotient p) : ℝ) := by
      exact_mod_cast (le_of_lt hpos.2)
    simp only [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hnonnegR]
  have hi :
      (Int.natAbs (norm (directOrbitGap p)) : ℝ) ^ 6 ≤
        64 ^ 3 * Int.natAbs (norm (directOrbitQuotient p)) := by
    rw [hgap, hquot]
    simpa only [directOrbitGap, directOrbitQuotient] using h
  exact_mod_cast hi

theorem directOrbit_gapHeight_power_inequality
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Int.natAbs (norm (directOrbitGap p)) ^ 7 ≤
      64 ^ 3 * (7 ^ 35 * r.summit.gapRoot ^ 42) := by
  let d : ℕ := Int.natAbs (norm (directOrbitGap p))
  let q : ℕ := Int.natAbs (norm (directOrbitQuotient p))
  have hi := directOrbit_natAbs_norm_gap_inequality p
  have hp := directOrbit_natAbs_norm_product_eq p
  have hm := Nat.mul_le_mul_right d hi
  dsimp [d, q] at hm ⊢
  calc
    Int.natAbs (norm (directOrbitGap p)) ^ 7 =
        Int.natAbs (norm (directOrbitGap p)) ^ 6 *
          Int.natAbs (norm (directOrbitGap p)) := by ring
    _ ≤ (64 ^ 3 * Int.natAbs (norm (directOrbitQuotient p))) *
          Int.natAbs (norm (directOrbitGap p)) := hm
    _ = 64 ^ 3 *
          (Int.natAbs (norm (directOrbitGap p)) *
            Int.natAbs (norm (directOrbitQuotient p))) := by ring
    _ = 64 ^ 3 * (7 ^ 35 * r.summit.gapRoot ^ 42) := by rw [hp]

theorem directOrbit_gapRoot_norm_pos
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (s : DirectOrbitPowerSplitPacket p) :
    0 < Int.natAbs (norm s.gapRoot) := by
  have hnorm_gap := directOrbit_norms_pos p
  have hcore_ne : norm s.gapCore ≠ 0 := by
    intro hzero
    apply (ne_of_gt hnorm_gap.1)
    rw [s.gap_eq, SevenRealCubicInt.norm_mul, hzero, mul_zero]
  have hunit_ne : norm (s.gapUnit : SevenRealCubicInt) ≠ 0 := by
    intro hzero
    have hu := gapHeight_natAbs_norm_unit s.gapUnit
    rw [hzero] at hu
    norm_num at hu
  have hroot_ne : norm s.gapRoot ≠ 0 := by
    intro hzero
    apply hcore_ne
    rw [s.gapCore_eq, SevenRealCubicInt.norm_mul,
      SevenRealCubicInt.norm_pow, hzero]
    simp
  exact Int.natAbs_pos.mpr hroot_ne

theorem directOrbit_gapRoot_norm_lt
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (s : DirectOrbitPowerSplitPacket p) :
    Int.natAbs (norm s.gapRoot) < s.gapSplit.a := by
  let g : ℕ := Int.natAbs (norm s.gapRoot)
  let a : ℕ := s.gapSplit.a
  let e : ℕ := 32 + 42 * s.gapSplit.k
  have hg : 0 < g := by
    exact directOrbit_gapRoot_norm_pos p s
  have ha : 0 < a := s.gapSplit.a_pos
  have hD : Int.natAbs (norm (directOrbitGap p)) = 7 ^ e * g ^ 7 := by
    exact directOrbit_natAbs_norm_eq p s
  have hroot : r.summit.gapRoot = 7 ^ s.gapSplit.k * a :=
    s.gapSplit.gap_eq
  have hraw := directOrbit_gapHeight_power_inequality p
  have hbase : 64 ^ 3 < 7 ^ 7 := by norm_num
  have hexp : 7 ≤ 189 + 252 * s.gapSplit.k := by omega
  have hpow : 7 ^ 7 ≤ 7 ^ (189 + 252 * s.gapSplit.k) := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have ha7 : 1 ≤ a ^ 7 := Nat.one_le_pow 7 a ha
  have hextra : 64 ^ 3 <
      7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7 := by
    calc
      64 ^ 3 < 7 ^ 7 := hbase
      _ ≤ 7 ^ (189 + 252 * s.gapSplit.k) := hpow
      _ = 7 ^ (189 + 252 * s.gapSplit.k) * 1 := by simp
      _ ≤ 7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7 :=
        Nat.mul_le_mul_left _ ha7
  by_contra hnot
  have hAG : a ≤ g := by omega
  have hpowAG : a ^ 7 ≤ g ^ 7 := Nat.pow_le_pow_left hAG 7
  have hL : 7 ^ e * a ^ 7 ≤
      Int.natAbs (norm (directOrbitGap p)) := by
    rw [hD]
    exact Nat.mul_le_mul_left _ hpowAG
  have hL7 := Nat.pow_le_pow_left hL 7
  have hfactor :
      (7 ^ e * a ^ 7) ^ 7 =
        (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) *
          (7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7) := by
    simp only [e]
    simp only [Nat.mul_pow]
    ring_nf
  have hupper :
      Int.natAbs (norm (directOrbitGap p)) ^ 7 ≤
        64 ^ 3 * (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) := by
    simpa only [hroot] using hraw
  have hcombined :
      (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) *
          (7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7) ≤
        64 ^ 3 * (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) := by
    rw [← hfactor]
    exact hL7.trans hupper
  have hfactor_pos :
      0 < 7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42 := by
    positivity
  have hstrict :
      64 ^ 3 * (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) <
        (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) *
          (7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7) := by
    calc
      64 ^ 3 * (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) =
          (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) * 64 ^ 3 := by
            rw [Nat.mul_comm]
      _ = 64 ^ 3 * (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) := by
            rw [Nat.mul_comm]
      _ < 7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7 *
          (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) :=
        Nat.mul_lt_mul_of_pos_right hextra hfactor_pos
      _ = (7 ^ 35 * (7 ^ s.gapSplit.k * a) ^ 42) *
          (7 ^ (189 + 252 * s.gapSplit.k) * a ^ 7) := by
            rw [Nat.mul_comm]
  exact (Nat.not_lt_of_ge hcombined hstrict)

/-! ## The smaller-norm packet -/

structure DirectOrbitSmallerNormPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (base : DirectRealCubicRootPacket source r) where
  powerSplit : DirectOrbitPowerSplitPacket base
  normRoot : ℕ
  normRoot_eq : normRoot = Int.natAbs (norm powerSplit.gapRoot)
  normRoot_pos : 0 < normRoot
  normRoot_lt : normRoot < powerSplit.gapSplit.a
  gapSplit_a_le_gapRoot : powerSplit.gapSplit.a ≤ r.summit.gapRoot

theorem directOrbitSmallerNormPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    Nonempty (DirectOrbitSmallerNormPacket p) := by
  let s := directOrbitPowerSplit p
  let g := Int.natAbs (norm s.gapRoot)
  have hg : 0 < g := directOrbit_gapRoot_norm_pos p s
  have hga : g < s.gapSplit.a := directOrbit_gapRoot_norm_lt p s
  have hA : s.gapSplit.a ≤ r.summit.gapRoot := by
    rw [s.gapSplit.gap_eq]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  exact ⟨{
    powerSplit := s
    normRoot := g
    normRoot_eq := rfl
    normRoot_pos := hg
    normRoot_lt := hga
    gapSplit_a_le_gapRoot := hA }⟩

end
end DkMath.FLT.Seven
