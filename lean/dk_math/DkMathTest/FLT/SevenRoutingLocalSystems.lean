import DkMath.FLT.Seven

open DkMath.FLT.Seven

example (t s : ℤ) :
    seventhPowerSndLeftCubic (t * s) s = s ^ 3 * leftCubicNormalized t :=
  leftCubic_scale t s

example (t s : ℤ) :
    seventhPowerSndRightCubic (t * s) s = s ^ 3 * rightCubicNormalized t :=
  rightCubic_scale t s

example (t s : ℤ) :
    leftFstCorrection (t * s) s = s ^ 2 * leftCorrectionNormalized t :=
  leftCorrection_scale t s

example (t s : ℤ) :
    rightFstCorrection (t * s) s = s ^ 2 * rightCorrectionNormalized t :=
  rightCorrection_scale t s

example (t : ℤ) :
    (60 * t - 88) * leftCubicNormalized t +
      (-6 * t ^ 2 + 22 * t - 19) * leftCorrectionNormalized t = 7 :=
  left_cubic_correction_bezout t

example (t : ℤ) :
    (60 * t + 148) * rightCubicNormalized t +
      (-6 * t ^ 2 - 34 * t - 47) * rightCorrectionNormalized t = 7 :=
  right_cubic_correction_bezout t

example {q : ℕ} [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (h : leftCubicNormalizedZMod t = 0) :
    leftCorrectionNormalizedZMod t ≠ 0 :=
  leftCorrection_ne_zero_of_leftCubic_eq_zero hq7 t h

example {q : ℕ} [Fact (Nat.Prime q)] (hq7 : q ≠ 7) (t : ZMod q)
    (h : rightCubicNormalizedZMod t = 0) :
    rightCorrectionNormalizedZMod t ≠ 0 :=
  rightCorrection_ne_zero_of_rightCubic_eq_zero hq7 t h

#print axioms left_cubic_correction_bezout
#print axioms right_cubic_correction_bezout
#print axioms leftCorrection_ne_zero_of_leftCubic_eq_zero
#print axioms rightCorrection_ne_zero_of_rightCubic_eq_zero
