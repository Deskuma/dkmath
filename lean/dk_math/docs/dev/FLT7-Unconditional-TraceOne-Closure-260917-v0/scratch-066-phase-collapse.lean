import DkMath.FLT.Seven.SevenRealCubicCurrentQuotientGapOrientation

namespace DkMath.FLT.Seven.SevenRealCubic

open SevenRealCubicInt
open scoped NumberField Pointwise

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f0 h.squareRefinement.gapSquareRoot = 0 ∧
      a.f1 (rotateEquiv h.squareRefinement.gapSquareRoot) = 0 ∧
      a.f2 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) = 0 := by
  exact ⟨a.gap_zero, a.f1_gap_rotate_zero, a.f2_gap_rotate2_zero⟩

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) *
        a.f1 (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) *
        a.f2 (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) =
      a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) ^ 3 := by
  exact currentCommonPrime_transported_rhs_product a

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    a.Q = (directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P ∨
      a.Q = (directOrbitGaloisSigma : Gal(Field / ℚ)) ^ 2 • b.P := by
  exact currentCommonPrime_quotient_oriented_gap_orbit a b

end DkMath.FLT.Seven.SevenRealCubic

#print axioms DkMath.FLT.Seven.SevenRealCubic.currentCoefficientRatio0_squareRefinement_rotate
#print axioms DkMath.FLT.Seven.SevenRealCubic.currentCommonPrime_fourteen_phase_collapse
#print axioms DkMath.FLT.Seven.SevenRealCubic.currentCommonPrime_quotient_ne_oriented_gap
#print axioms DkMath.FLT.Seven.SevenRealCubic.currentCommonPrime_quotient_oriented_gap_orbit
