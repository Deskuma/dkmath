/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.GoldenDivisibility
import DkMath.FLT.Five.SignedSquareGoldenExceptional

#print "file: DkMath.FLT.Five.SignedGoldenRamifierStripped"

namespace DkMath.FLT.Five

/-- The exceptional packet after removing the unique visible ramifier `tau`. -/
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  exceptional : SignedSquareGoldenExceptionalPacket u v w
  alpha : GoldenInt
  beta : GoldenInt
  k : ℤ
  alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
  linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
  alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
  beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
  beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
  beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
  five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
  five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
  tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma

private theorem five_not_dvd_powerSplit_b
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    ¬ 5 ∣ p.powerSplit.b := by
  intro h5b
  have h25 : 25 ∣ p.powerSplit.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [p.powerSplit.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [p.powerSplit.fiveAdic.residual_mod_twentyFive] at hzero
  omega

private theorem nonempty_signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    Nonempty (SignedGoldenRamifierStrippedPacket u v w) := by
  let A : ℤ := 2 * p.M + p.N
  have hAeq : A ^ 2 = 5 * (p.N ^ 2 + 4 * (p.powerSplit.b : ℤ) ^ 5) := by
    dsimp [A]
    nlinarith [p.discriminant_five_eq]
  have h5sq : (5 : ℤ) ∣ A ^ 2 := ⟨_, hAeq⟩
  have h5A : (5 : ℤ) ∣ A :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5sq
  rcases exists_goldenTau_factor_of_five_dvd h5A with
    ⟨k, beta, hk, hbeta, halpha⟩
  let alpha : GoldenInt := ⟨p.M, p.N⟩
  have hnormAlpha : goldenNorm alpha = 5 * (p.powerSplit.b : ℤ) ^ 5 := by
    simpa [alpha, goldenNorm_eq_GoldenNorm] using p.golden_eq
  have hnormBeta : goldenNorm beta = (p.powerSplit.b : ℤ) ^ 5 := by
    have hmul := goldenNorm_mul goldenTau beta
    rw [goldenNorm_tau] at hmul
    have : 5 * goldenNorm beta = 5 * (p.powerSplit.b : ℤ) ^ 5 := by
      calc
        5 * goldenNorm beta = goldenNorm (goldenMul goldenTau beta) := hmul.symm
        _ = goldenNorm alpha := by
          change goldenNorm (goldenMul goldenTau beta) =
            goldenNorm (⟨p.M, p.N⟩ : GoldenInt)
          exact congrArg goldenNorm halpha.symm
        _ = 5 * (p.powerSplit.b : ℤ) ^ 5 := hnormAlpha
    omega
  have hsndMul : 5 * beta.snd = -(p.M - 2 * p.N) := by
    rw [hbeta]
    simp
    omega
  have hsnd :
      beta.snd = -(5 : ℤ) ^ 7 * (p.powerSplit.a : ℤ) ^ 10 := by
    apply (mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0))
    calc
      5 * beta.snd = -(p.M - 2 * p.N) := hsndMul
      _ = -((5 : ℤ) ^ 8 * (p.powerSplit.a : ℤ) ^ 10) := by
        rw [p.tenth_boundary]
      _ = 5 * (-(5 : ℤ) ^ 7 * (p.powerSplit.a : ℤ) ^ 10) := by ring
  have h5b : ¬ 5 ∣ p.powerSplit.b := five_not_dvd_powerSplit_b p
  have h5norm : ¬ (5 : ℤ) ∣ goldenNorm beta := by
    intro h
    rw [hnormBeta] at h
    have hbZ : (5 : ℤ) ∣ (p.powerSplit.b : ℤ) :=
      (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h
    have hb : 5 ∣ p.powerSplit.b := by exact_mod_cast hbZ
    exact h5b hb
  have htau : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma := by
    rintro ⟨gamma, hgamma⟩
    apply h5norm
    use goldenNorm gamma
    rw [hgamma, goldenNorm_mul, goldenNorm_tau]
  exact ⟨{
    exceptional := p
    alpha := alpha
    beta := beta
    k := k
    alpha_eq := rfl
    linear_eq := hk
    alpha_eq_tau_mul := halpha
    beta_eq := hbeta
    beta_norm := hnormBeta
    beta_snd := hsnd
    five_not_dvd_b := h5b
    five_not_dvd_beta_norm := h5norm
    tau_not_dvd_beta := htau }⟩

/-- Chosen ramifier-stripped packet from the square-golden exceptional packet. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)

/-- Chosen ramifier-stripped packet from the exact five-adic power split. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_exceptional
    (signedSquareGoldenExceptionalPacket_of_powerSplit s)

/-- Chosen ramifier-stripped packet directly from a signed normal form. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)

/-- Remaining kernel after the visible golden ramifier has been removed. -/
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False

/-- A refuter for all stripped packets closes both signed orientations. -/
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)

/-- The stripped core also closes every routed Branch-B counterexample pack. -/
theorem branchB_false_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch

/--
The exact next algebraic contract: every stripped exceptional element is a
fifth power up to a golden unit.  Establishing this requires the missing
factorization/coprimality and unit-classification layer; it is not assumed here.
-/
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)

end DkMath.FLT.Five
