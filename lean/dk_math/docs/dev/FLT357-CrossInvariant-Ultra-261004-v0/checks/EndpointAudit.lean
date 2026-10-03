import DkMath.FLT.Three
import DkMath.FLT.Five
import DkMath.FLT.Five.TraceOneBridge
import DkMath.FLT.Prime
import DkMath.FLT.Seven.CurrentCarrierNormalizedPower
import DkMath.FLT.Seven.SevenRealCubicUnitClass
import DkMath.NumberTheory.TraceOneDiscriminantAxis

/- Test-only source/axiom audit for Instruction 001. Imported proof holes do
   not establish a dependency: the named endpoints are checked separately. -/

#check DkMath.FLT.Three.fermatThree_no_positive_solution
#print axioms DkMath.FLT.Three.fermatThree_no_positive_solution
#print axioms DkMath.FLT.Three.exists_unit_mul_cube_of_coprime_mul_eq_cube
#print axioms DkMath.FLT.Three.exists_smaller_primitiveCubicPack
#check DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type
#check DkMath.FLT.Three.lib_eisensteinCoord_eq_FLT3_coord

#check DkMath.FLT.Five.flt5Target
#print axioms DkMath.FLT.Five.flt5Target
#print axioms DkMath.FLT.Five.goldenCoprimeFactorOfFifthPower
#print axioms DkMath.FLT.Five.goldenUnitClassesModFifth
#print axioms DkMath.FLT.Five.GoldenZeroSectorDescentPacket.strictDescent
#print axioms DkMath.FLT.Five.goldenZeroSectorDescentPacket_false
#check DkMath.FLT.Five.goldenTraceOneRingEquiv

#check DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
#print axioms DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power
#print axioms DkMath.FLT.Seven.SevenRealCubic.unitClassProjectiveLog_bijective
#print axioms DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero

#check DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
#print axioms DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
#check DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow
#print axioms DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow

namespace FLT357CrossInvariantAudit

open DkMath.NumberTheory.TraceOneQuadratic

/-- The p=3 discriminant axis and production ramifier differ by tau. -/
theorem three_ramifier_normalization :
    discrAxis (-1) = DkMath.FLT.Three.eisensteinTau *
      DkMath.FLT.Three.eisensteinRamifier := by
  rw [discrAxis_eq]
  change (⟨-1, 2⟩ : TraceOneInt (-1)) = ⟨0, 1⟩ * (1 + ⟨0, 1⟩)
  decide

/-- The p=5 production ramifier maps to phi times the generic axis. -/
theorem five_ramifier_normalization :
    DkMath.FLT.Five.goldenTraceOneRingEquiv DkMath.FLT.Five.goldenTau =
      tau 1 * discrAxis 1 := by
  rw [discrAxis_eq]
  change (⟨2, 1⟩ : TraceOneInt 1) = ⟨0, 1⟩ * ⟨-1, 2⟩
  decide

#print axioms three_ramifier_normalization
#print axioms five_ramifier_normalization

end FLT357CrossInvariantAudit
