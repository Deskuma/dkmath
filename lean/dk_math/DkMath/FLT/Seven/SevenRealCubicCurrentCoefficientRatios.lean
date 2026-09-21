import DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicFourteen

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenRealCubic

/-! The three coefficient-ratio units and their exact cyclic product. -/

def currentCoefficientRatio0 {R : Type*} [CommRing R]
    (_c0 c1 c2 : Rˣ) : Rˣ := -c2 / c1

def currentCoefficientRatio1 {R : Type*} [CommRing R]
    (c0 _c1 c2 : Rˣ) : Rˣ := -c0 / c2

def currentCoefficientRatio2 {R : Type*} [CommRing R]
    (c0 c1 _c2 : Rˣ) : Rˣ := -c1 / c0

theorem currentCoefficientRatio_product {R : Type*} [CommRing R]
    (c0 c1 c2 : Rˣ) :
    currentCoefficientRatio0 c0 c1 c2 *
        currentCoefficientRatio1 c0 c1 c2 *
        currentCoefficientRatio2 c0 c1 c2 = -1 := by
  simp only [currentCoefficientRatio0, currentCoefficientRatio1,
    currentCoefficientRatio2]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end SevenRealCubic
end
end DkMath.FLT.Seven
