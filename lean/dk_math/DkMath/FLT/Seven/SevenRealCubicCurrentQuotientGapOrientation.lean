/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentCoefficientPhaseCollapse
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentQuotientGapOrientation"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

/-! The quotient-side prime and the oriented gap prime are kept as two
    independently evaluated addresses. -/

theorem currentCommonPrime_quotient_ne_oriented_gap
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    a.Q ≠ b.P := by
  letI : a.Q.IsPrime := a.Q_prime
  intro hQP
  have hquot_mem : modelEquivRingOfIntegers
      h.squareRefinement.quotientSquareRoot ∈ a.Q := by
    have hz : algebraMap O a.Q.ResidueField
        (modelEquivRingOfIntegers h.squareRefinement.quotientSquareRoot) = 0 := by
      simpa [a.evalReal_formula, directOrbitCommonPrimeEval] using
        congrArg a.evalEquiv.symm a.quotientRoot_zero
    exact Ideal.algebraMap_residueField_eq_zero.mp hz
  have hgap_mem : modelEquivRingOfIntegers
      h.squareRefinement.gapSquareRoot ∈ a.Q := by
    rw [hQP]
    exact b.gap_mem
  have hquot_le : Ideal.span
      ({modelEquivRingOfIntegers h.squareRefinement.quotientSquareRoot} :
        Set O) ≤ a.Q :=
    (Ideal.span_singleton_le_iff_mem a.Q).mpr hquot_mem
  have hgap_le : Ideal.span
      ({modelEquivRingOfIntegers h.squareRefinement.gapSquareRoot} :
        Set O) ≤ a.Q :=
    (Ideal.span_singleton_le_iff_mem a.Q).mpr hgap_mem
  have htop : (⊤ : Ideal O) ≤ a.Q := by
    rw [← (directOrbitSquareRefinement_squareRoots_isCoprime_ringOfIntegers
      h.squareRefinement).sup_eq]
    exact sup_le hgap_le hquot_le
  exact a.Q_prime.ne_top (top_unique htop)

theorem currentCommonPrime_quotient_oriented_gap_orbit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    a.Q = (directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P ∨
      a.Q = (directOrbitGaloisSigma : Gal(Field / ℚ)) ^ 2 • b.P := by
  exact directOrbitGalois_distinct_prime_address
    b.P_prime a.Q_prime b.P_liesOver a.Q_liesOver
    (currentCommonPrime_quotient_ne_oriented_gap a b).symm

end SevenRealCubic
end
end DkMath.FLT.Seven
