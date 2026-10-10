/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicPrimeAddress
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicLinearPrimeAddress

#print "file: DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress"

namespace DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.CosmicFormula
open SevenCyclotomicDegreeSixInt

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local notation "K11" => seventhRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide)
local notation "K35" => seventhRootKernel (35 : ZMod 43) (by decide) (by decide) (by decide)
local notation "E11" => evalCyclotomicFromSeventhRoot (11 : ZMod 43)
  (by decide) (by decide) (by decide)
local notation "E35" => evalCyclotomicFromSeventhRoot (35 : ZMod 43)
  (by decide) (by decide) (by decide)

example : (11 : ZMod 43) ^ 2 = 35 ∧ (11 : ZMod 43) ^ 7 = 1 ∧
    (35 : ZMod 43) ^ 7 = 1 ∧ (11 : ZMod 43) ≠ 0 ∧ (35 : ZMod 43) ≠ 0 ∧
    (11 : ZMod 43) ≠ 1 ∧ (35 : ZMod 43) ≠ 1 ∧ (11 : ZMod 43) ≠ 35 := by decide
example : E11 zeta = 11 ∧ E35 zeta = 35 :=
  ⟨evalCyclotomicFromSeventhRoot_zeta _ _ _ _, evalCyclotomicFromSeventhRoot_zeta _ _ _ _⟩
example : Function.Surjective E11 := evalCyclotomicFromSeventhRoot_surjective _ _ _ _
example : (K11).IsMaximal ∧ (K35).IsMaximal :=
  ⟨seventhRootKernel_isMaximal _ _ _ _, seventhRootKernel_isMaximal _ _ _ _⟩
example : (K11).IsPrime ∧ (K35).IsPrime :=
  ⟨seventhRootKernel_isPrime _ _ _ _, seventhRootKernel_isPrime _ _ _ _⟩
example : Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring) K11 =
    Ideal.span ({(43 : ℤ)} : Set ℤ) := seventhRootKernel_comap_intCast _ _ _ _
example : Ideal.comap ofReal K35 =
    RingHom.ker (evalRealFromSeventhRoot (35 : ZMod 43) (by decide) (by decide) (by decide)) :=
  seventhRootKernel_comap_ofReal _ _ _ _
example : Submodule.cardQuot K11 = 43 ∧ Submodule.cardQuot K35 = 43 :=
  ⟨seventhRootKernel_cardQuot _ _ _ _, seventhRootKernel_cardQuot _ _ _ _⟩

private theorem ratio11 : gtailSevenTailRatio 43 9 4 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (9 : ZMod 43) ≠ 0)).mpr
  decide

example : gtailCyclotomicLinearFactor 9 4 ∈ K11 := by
  rw [mem_seventhRootKernel_iff, evalCyclotomic_linearFactor_eq_zero_iff _ _ _ _ 9 4 (by decide)]
  exact ratio11.symm
example : gtailCyclotomicLinearFactor 9 4 ∉ K35 := by
  rw [mem_seventhRootKernel_iff, evalCyclotomic_linearFactor_eq_zero_iff _ _ _ _ 9 4 (by decide),
    ratio11]
  decide
example : (13 : ZMod 43) - 35 * 9 ≠ 0 := by decide
example : E35 (ofReal (13 : SevenRealCubicInt) - zeta * ofReal (9 : SevenRealCubicInt)) ≠ 0 := by
  have h13 : evalRealFromSeventhRoot (35 : ZMod 43) (by decide) (by decide) (by decide)
      (13 : SevenRealCubicInt) = 13 := map_natCast _ 13
  have h9 : evalRealFromSeventhRoot (35 : ZMod 43) (by decide) (by decide) (by decide)
      (9 : SevenRealCubicInt) = 9 := map_natCast _ 9
  simp only [map_sub, map_mul, evalCyclotomicFromSeventhRoot_zeta,
    evalCyclotomicFromSeventhRoot_ofReal]
  rw [h13, h9]
  decide
example : zeta - ofReal (11 : SevenRealCubicInt) ∈ K11 ∧
    zeta - ofReal (11 : SevenRealCubicInt) ∉ K35 :=
  seventhRootKernel_separating_element (11 : ZMod 43) 35
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : K11 ≠ K35 := seventhRootKernel_ne _ _
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : gtailCyclotomicLinearFactor 9 4 ∈
      seventhRootKernel (gtailSevenTailRatio 43 9 4)
        (gtailSevenTailRatio_ne_zero (by decide) (by decide))
        (gtailSevenTailRatio_pow_seven (by decide) (by decide))
        (gtailSevenTailRatio_ne_one (by decide) (by decide)) ∧
    gtailCyclotomicLinearFactor 9 4 ∉ K35 := by
  apply gtailCyclotomicLinearFactor_unique_address 9 4
    (by decide) (by decide) (by decide) 35 (by decide) (by decide) (by decide)
  rw [ratio11]
  decide

-- Satisfiable congruences do not assert the Fermat equation or a signed packet.
example : (43 : ℕ) ∣ 5 ^ 2 + 5 * 8 + 8 ^ 2 ∧ 43 ∣ GTail 7 1 4 9 := by decide
example : gtailSevenResidueRoot 43 5 8 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (8 : ZMod 43) ≠ 0)).mpr
  decide
example : ¬ Fermat7Equation 5 8 9 := by
  unfold Fermat7Equation
  decide
example : (13 : ℕ) ∣ 13 ∧ ¬ (13 : ℕ) ∣ GTail 7 1 13 30 := by decide
example : gtailSevenTailRatio 13 30 13 = 1 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (30 : ZMod 13) ≠ 0)).mpr
  decide
example : ramifiedEval zeta = (1 : ZMod 7) := ramifiedEval_zeta

-- Without the endpoint unit, the zero factor can lie in both distinct kernels.
example : gtailCyclotomicLinearFactor 0 0 ∈ K11 ∧ gtailCyclotomicLinearFactor 0 0 ∈ K35 := by
  simp [gtailCyclotomicLinearFactor]

-- Optional comparison on an actually supplied old address, not a constructed packet.
example {p : RamifiedSignedRootRoutingPacket} {q : ℕ} [Fact (Nat.Prime q)]
    (a : RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress p q)
    (hr0 : (a.quotientAddress.ratio : ZMod q) ≠ 0)
    (hr7 : (a.quotientAddress.ratio : ZMod q) ^ 7 = 1)
    (hr1 : (a.quotientAddress.ratio : ZMod q) ≠ 1) :
    evalCyclotomicFromSeventhRoot (a.quotientAddress.ratio : ZMod q) hr0 hr7 hr1 = a.eval := by
  have hb : seventhRootBeta (a.quotientAddress.ratio : ZMod q) = a.quotientAddress.beta := by
    dsimp only [seventhRootBeta, RamifiedSignedRootDepthPacket.QuotientPrimeMuSevenAddress.beta]
  ext x
  change
    ((x.re.fst : ZMod q) + (x.re.snd : ZMod q) *
        seventhRootBeta (a.quotientAddress.ratio : ZMod q) +
      (x.re.thd : ZMod q) * seventhRootBeta (a.quotientAddress.ratio : ZMod q) ^ 2) +
      (a.quotientAddress.ratio : ZMod q) *
        ((x.im.fst : ZMod q) + (x.im.snd : ZMod q) *
            seventhRootBeta (a.quotientAddress.ratio : ZMod q) +
          (x.im.thd : ZMod q) * seventhRootBeta (a.quotientAddress.ratio : ZMod q) ^ 2) =
      ((x.re.fst : ZMod q) + (x.re.snd : ZMod q) * a.quotientAddress.beta +
        (x.re.thd : ZMod q) * a.quotientAddress.beta ^ 2) +
      (a.quotientAddress.ratio : ZMod q) *
        ((x.im.fst : ZMod q) + (x.im.snd : ZMod q) * a.quotientAddress.beta +
          (x.im.thd : ZMod q) * a.quotientAddress.beta ^ 2)
  rw [hb]

#print axioms DkMath.FLT.Seven.seventhRootKernel
#print axioms DkMath.FLT.Seven.mem_seventhRootKernel_iff
#print axioms DkMath.FLT.Seven.evalCyclotomicFromSeventhRoot_surjective
#print axioms DkMath.FLT.Seven.seventhRootKernel_isMaximal
#print axioms DkMath.FLT.Seven.seventhRootKernel_isPrime
#print axioms DkMath.FLT.Seven.seventhRootKernel_comap_ofReal
#print axioms DkMath.FLT.Seven.seventhRootKernel_comap_intCast
#print axioms DkMath.FLT.Seven.seventhRootKernel_cardQuot
#print axioms DkMath.FLT.Seven.evalCyclotomic_linearFactor_eq_zero_iff
#print axioms DkMath.FLT.Seven.seventhRootKernel_separating_element
#print axioms DkMath.FLT.Seven.seventhRootKernel_ne
#print axioms DkMath.FLT.Seven.gtailCyclotomicLinearFactor_unique_address

end DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress
