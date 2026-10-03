/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimeShellHensel
import DkMath.FLT.Seven.SevenRealCubicCurrentPhaseCorrectedCarrier
import Mathlib.Tactic.NormNum

#print "file: DkMathTest.FLT.CompleteSupportDRCBridgeAudit"

/-!
# Residue and Hensel boundaries in the complete-support audit

The scalar shell calibration has a simple nontrivial seventh-root residue at
exact depth one. It isolates the root-of-unity and finite Hensel hypotheses;
it does not construct a current FLT7 packet or a Fermat counterexample.
Current neutral residue addresses separately exclude the ramified prime.
-/

namespace DkMathTest.FLT.CompleteSupportDRCBridgeAudit

open DkMath.NumberTheory DkMath.CosmicFormula

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- The simple degree-seven shell seed has exact depth one at 29. -/
theorem degree_seven_shell_exact_depth_one :
    (29 : ℤ) ∣ GTail 7 1 15 1 ∧ ¬ (29 : ℤ) ^ 2 ∣ GTail 7 1 15 1 := by
  norm_num [GTail, Finset.sum_range_succ, Nat.choose]

/-- The same seed supplies every positive depth, including depths not divisible by seven. -/
theorem degree_seven_shell_all_exact_depths {k : ℕ} (hk : 1 ≤ k) :
    ∃ g : ℤ, (29 : ℤ) ^ k ∣ GTail 7 1 g 1 ∧
      ¬ (29 : ℤ) ^ (k + 1) ∣ GTail 7 1 g 1 := by
  apply exists_primeShell_exact_depth (by decide) (by decide) (by decide) hk 1 15
  · norm_num
  · exact degree_seven_shell_exact_depth_one.1

/-- The depth-one seed has the nonzero derivative required by finite Hensel. -/
theorem degree_seven_shell_depth_one_simple :
    ¬ (29 : ℤ) ∣ (primeShellPolynomial 7 1).derivative.eval 15 := by
  apply primeShell_derivative_not_dvd (by decide) (by decide) (by decide) 1 15
  · norm_num
  · exact degree_seven_shell_exact_depth_one.1

/-- Its normalized ratio is the nontrivial seventh root 16 modulo 29. -/
theorem degree_seven_shell_root_of_unity :
    ((15 + 1 : ZMod 29) / (1 : ZMod 29)) ^ 7 = 1 ∧
      (15 + 1 : ZMod 29) / (1 : ZMod 29) ≠ 1 := by
  exact (primeShell_dvd_iff_rootOfUnity (by decide : Nat.Prime 7)
    (by decide : 29 ≠ 7) 1 15 (by norm_num)).mp degree_seven_shell_exact_depth_one.1

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubic

/-- Frobenius rules out any neutral nontrivial seventh-root address at 7. -/
theorem current_address_excludes_ramified_prime
    {q : ℕ} (a : CurrentMuSevenResidueAddress q) : q ≠ 7 := by
  intro hq
  subst q
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply a.ratio_ne_one
  apply Units.val_injective
  have ht := congrArg Units.val a.ratio_pow_seven
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, ZMod.pow_card] using ht

/-- The stronger current common-prime packet records the same exclusion. -/
theorem current_packet_excludes_ramified_prime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (c : CurrentCommonPrimeCyclotomicPacket h q) : q ≠ 7 := c.residue.q_ne_seven

#print axioms degree_seven_shell_exact_depth_one
#print axioms degree_seven_shell_all_exact_depths
#print axioms degree_seven_shell_depth_one_simple
#print axioms degree_seven_shell_root_of_unity
#print axioms current_address_excludes_ramified_prime
#print axioms current_packet_excludes_ramified_prime

end DkMathTest.FLT.CompleteSupportDRCBridgeAudit
