/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.TraceOneDiscriminantAxis
import DkMath.FLT.ThreeTraceOneBridge
import DkMath.FLT.Five.TraceOneBridge
import DkMath.FLT.Seven.AxisDepth

#print "file: DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility"

namespace DkMathTest.FLT.Prime

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

private theorem packet7 : PrimeDiscriminantPacket 7 (-2) :=
  { prime := by norm_num
    discr_natAbs := by norm_num [discr] }

private theorem packet3 : PrimeDiscriminantPacket 3 (-1) :=
  { prime := by norm_num
    discr_natAbs := by norm_num [discr] }

private theorem packet5 : PrimeDiscriminantPacket 5 1 :=
  { prime := by norm_num
    discr_natAbs := by norm_num [discr] }

example : discr (-2) = -7 := by norm_num [discr]

example : Int.natAbs (discr (-2)) = 7 := by norm_num [discr]

example : discrAxis (-2) = sevenAxis := by
  rw [discrAxis_eq, sevenAxis_eq]

example (x : TraceOneInt (-2)) :
    discrAxis (-2) ∣ x ↔ 7 ∣ Int.natAbs (norm x) := by
  exact packet7.discrAxis_dvd_iff_prime_dvd_natAbs_norm x

example (n : ℕ) (x : TraceOneInt (-2)) :
    discrAxis (-2) ^ n ∣ x ↔ 7 ^ n ∣ Int.natAbs (norm x) := by
  exact packet7.discrAxis_pow_dvd_iff_pow_prime_dvd_natAbs_norm n x

example {x : TraceOneInt (-2)} (hx : norm x ≠ 0) (n : ℕ) :
    discrAxis (-2) ^ n ∣ x ↔ n ≤ discrAxisDepth 7 x := by
  exact packet7.discrAxis_pow_dvd_iff_le_depth hx n

example (x : TraceOneInt (-2)) :
    discrAxisDepth 7 x = sevenAxisDepth x := by
  rfl

example (n : ℕ) :
    discrAxisDepth 7 (discrAxis (-2) ^ n) = n := by
  exact packet7.discrAxisDepth_discrAxis_pow n

example : discr (-1) = -3 := by norm_num [discr]

example : discr 1 = 5 := by norm_num [discr]

example : Int.natAbs (discr (-1)) = 3 := by norm_num [discr]

example : Int.natAbs (discr 1) = 5 := by norm_num [discr]

example (x : TraceOneInt (-1)) :
    (3 : ℤ) ∣ norm x ↔ (3 : ℤ) ∣ trace x := by
  exact packet3.norm_dvd_iff_trace_dvd x

example (x : TraceOneInt 1) :
    (5 : ℤ) ∣ norm x ↔ (5 : ℤ) ∣ trace x := by
  exact packet5.norm_dvd_iff_trace_dvd x

example (x : TraceOneInt (-2)) :
    (7 : ℤ) ∣ norm x ↔ (7 : ℤ) ∣ trace x := by
  exact packet7.norm_dvd_iff_trace_dvd x

/-! ## Discriminant-form normalization of the existing three samples -/

example (a b : ℕ) :
    4 * (DkMath.FLT.PetalDetect.S0_nat a b : ℤ) =
      trace (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1)) ^ 2 -
        discr (-1) * (b : ℤ) ^ 2 := by
  rw [DkMath.FLT.S0_nat_eq_traceOneNorm_negOne]
  exact four_mul_traceOneNorm_eq_discriminant
    (⟨(a : ℤ), (b : ℤ)⟩ : TraceOneInt (-1))

example (x : DkMath.FLT.Five.GoldenInt) :
    4 * DkMath.FLT.Five.goldenNorm x =
      trace (DkMath.FLT.Five.goldenToTraceOne x) ^ 2 -
        discr 1 * (DkMath.FLT.Five.goldenToTraceOne x).snd ^ 2 := by
  rw [DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one]
  exact four_mul_traceOneNorm_eq_discriminant
    (DkMath.FLT.Five.goldenToTraceOne x)

example (z y : ℤ) :
    4 * DkMath.FLT.Seven.cyclotomicSeven z y =
      trace (DkMath.FLT.Seven.cyclotomicSevenToTraceOne z y) ^ 2 -
        discr (-2) *
          (DkMath.FLT.Seven.cyclotomicSevenToTraceOne z y).snd ^ 2 := by
  rw [DkMath.FLT.Seven.cyclotomicSeven_eq_traceOneNorm_negTwo]
  exact four_mul_traceOneNorm_eq_discriminant
    (DkMath.FLT.Seven.cyclotomicSevenToTraceOne z y)

-- Existing concrete surfaces remain available as separate, small-family APIs.
#check DkMath.FLT.S0_nat_eq_traceOneNorm_negOne
#check DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one
#check DkMath.FLT.Seven.cyclotomicSeven_eq_traceOneNorm_negTwo
#check DkMath.FLT.Seven.sevenAxis_pow_dvd_iff_pow_seven_dvd_norm
#check DkMath.FLT.Seven.sevenAxis_pow_dvd_iff_le_sevenAxisDepth

end DkMathTest.FLT.Prime
