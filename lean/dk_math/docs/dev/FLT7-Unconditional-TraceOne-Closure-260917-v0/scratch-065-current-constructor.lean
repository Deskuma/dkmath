import DkMath.FLT.Seven.SevenRealCubicCurrentCommonPrimePacket
import DkMath.FLT.Seven.SevenRealCubicCurrentOrientedGapTransport
import DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicFourteen
import DkMath.FLT.Seven.SevenRealCubicCurrentCoefficientRatios

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

namespace SevenRealCubic

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentCommonPrimeResiduePacket h q) :=
  currentCommonPrime_residuePacket h q hq hqc

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentCommonPrimeCyclotomicPacket h q) :=
  currentCommonPrime_cyclotomicAddress h q hq hqc

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentOrientedGapPrimeTransport h q) :=
  currentOrientedGapPrimeTransport h q hq hqc

example {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f1 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot)) ≠ 0 :=
  a.f1_gap_rotate2_ne_zero

example {K : Type*} [_root_.Field K]
    {c0 c1 c2 r0 r1 r2 : K}
    (hc1 : c1 ≠ 0) (hr2 : r2 ≠ 0)
    (hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0)
    (hr0 : r0 = 0) :
    (r1 / r2) ^ 14 = -c2 / c1 :=
  three_zero_index_fourteen_zero hc1 hr2 hEq hr0

example {R : Type*} [CommRing R] (c0 c1 c2 : Rˣ) :
    currentCoefficientRatio0 c0 c1 c2 *
        currentCoefficientRatio1 c0 c1 c2 *
        currentCoefficientRatio2 c0 c1 c2 = -1 :=
  currentCoefficientRatio_product c0 c1 c2

#print axioms currentCommonPrime_residuePacket
#print axioms currentCommonPrime_cyclotomicAddress
#print axioms currentOrientedGapPrimeTransport
#print axioms CurrentOrientedGapPrimeTransport.f1_gap_rotate2_ne_zero
#print axioms three_zero_index_fourteen_zero
#print axioms currentCoefficientRatio_product

end SevenRealCubic
end
end DkMath.FLT.Seven
