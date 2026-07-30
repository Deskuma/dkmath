import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example (u v : ℤ) :
    ((⟨u, v⟩ : TraceOneInt (-2)) ^ 7).fst = seventhPowerFst u v :=
  traceOne_pow_seven_fst u v

example (u v : ℤ) :
    ((⟨u, v⟩ : TraceOneInt (-2)) ^ 7).snd = seventhPowerSnd u v :=
  traceOne_pow_seven_snd u v

example (u v : ℤ) :
    seventhPowerSnd u v = 7 * v * seventhPowerSndCore u v :=
  seventhPowerSnd_eq_seven_mul u v

example (u v : ℤ) :
    (seventhPowerSndCore u v : ZMod 7) =
      ((u : ZMod 7) ^ 2 + (u : ZMod 7) * (v : ZMod 7) +
        2 * (v : ZMod 7) ^ 2) ^ 3 :=
  seventhPowerSndCore_mod_seven u v

example (u v : ℤ) :
    (seventhPowerFst u v : ZMod 7) = (u : ZMod 7) + 4 * (v : ZMod 7) :=
  seventhPowerFst_mod_seven u v

example (u v : ℤ) : (seventhPowerSnd u v : ZMod 7) = 0 :=
  seventhPowerSnd_mod_seven u v

example (u v : ℤ) :
    (ramifiedSeventhFst u v : ZMod 7) = -((u : ZMod 7) + 4 * (v : ZMod 7)) :=
  ramifiedSeventhFst_mod_seven u v

example (u v : ℤ) :
    (ramifiedSeventhSnd u v : ZMod 7) = 2 * ((u : ZMod 7) + 4 * (v : ZMod 7)) :=
  ramifiedSeventhSnd_mod_seven u v

#print axioms traceOne_pow_seven_eq
#print axioms seventhPowerSndCore_mod_seven
#print axioms fortyNine_dvd_seventhPowerSnd_iff
#print axioms sevenAxis_mul_pow_seven_eq
