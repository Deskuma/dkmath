import DkMath.RH.CFBRC.EtaCriticalMirrorWeightPressure

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorWeightPressure"

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorWeightPressure

open DkMath.RH.CFBRCProjection

example {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    {m : ℕ} (hm : 0 < m) :
    1 < ‖etaCriticalMirrorTermWeight s m‖ :=
  one_lt_norm_etaCriticalMirrorTermWeight_of_half_lt_re hre hm

example {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    {m : ℕ} (hm : 0 < m) :
    ‖etaCriticalMirrorTermWeight s m‖ < 1 :=
  norm_etaCriticalMirrorTermWeight_lt_one_of_re_lt_half hre hm

example (s : ℂ) {m : ℕ} (hm : 0 < m) :
    ‖etaCriticalMirrorTermWeight s m‖ = 1 ↔
      s.re = (1 : ℝ) / 2 :=
  norm_etaCriticalMirrorTermWeight_eq_one_iff_re_eq_half s hm

example (s : ℂ) {m : ℕ} (hm : 0 < m) :
    (s.re < (1 : ℝ) / 2 ∧ ‖etaCriticalMirrorTermWeight s m‖ < 1) ∨
    (s.re = (1 : ℝ) / 2 ∧ ‖etaCriticalMirrorTermWeight s m‖ = 1) ∨
    ((1 : ℝ) / 2 < s.re ∧ 1 < ‖etaCriticalMirrorTermWeight s m‖) :=
  etaCriticalMirrorTermWeight_pressure_trichotomy s hm

end DkMathTest.RH.CFBRCEtaCriticalMirrorWeightPressure
