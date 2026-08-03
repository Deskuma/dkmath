import DkMath.RH.CFBRC.CriticalMirrorZeroBridge

#print "file: DkMathTest.RH.CFBRCCriticalMirrorZeroBridge"

namespace DkMathTest.RH.CFBRCCriticalMirrorZeroBridge

open DkMath.RH.CFBRCProjection

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  nontrivialRiemannZetaZero_mem_openCriticalStrip hs

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (criticalMirror s) = 0 :=
  riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero hs

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (criticalMirror s) :=
  criticalMirror_nontrivialRiemannZetaZero hs

end DkMathTest.RH.CFBRCCriticalMirrorZeroBridge
