/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionLoadedCore

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionDirectChartObstruction"

namespace DkMath.FLT.Seven

namespace RamifiedSignedRootDepthPacket

/-- The signed seventh-power difference has an exact visible factor
`7^5`.  This is the integer obstruction at the direct-chart boundary:
the remaining two factors are both prime to seven. -/
theorem signedRoot_seventhPowerDifference_eq
    (p : RamifiedSignedRootDepthPacket) :
    p.signedRightRoot ^ 7 - p.signedLeftRoot ^ 7 =
      7 ^ 5 * p.gapRoot * p.quotientRoot := by
  calc
    p.signedRightRoot ^ 7 - p.signedLeftRoot ^ 7 =
        (p.signedRightRoot - p.signedLeftRoot) *
          signedSeventhQuotient
            p.signedRightRoot p.signedLeftRoot :=
      signed_pow_seven_sub_factorization _ _
    _ = (7 ^ 4 * p.gapRoot) * (7 * p.quotientRoot) := by
      rw [p.signedGap_eq, p.signedQuotient_eq]
    _ = 7 ^ 5 * p.gapRoot * p.quotientRoot := by ring

/-- The exact factor `7^5` cannot be strengthened to `7^6`, because both
the normalized gap root and quotient root are prime to seven. -/
theorem sevenPowSix_not_dvd_signedRoot_seventhPowerDifference
    (p : RamifiedSignedRootDepthPacket) :
    ¬ (7 ^ 6 : ℤ) ∣
      p.signedRightRoot ^ 7 - p.signedLeftRoot ^ 7 := by
  intro hdiv
  rw [p.signedRoot_seventhPowerDifference_eq] at hdiv
  rcases hdiv with ⟨k, hk⟩
  have hcancel :
      p.gapRoot * p.quotientRoot = 7 * k := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 5 : ℤ) ≠ 0)
    calc
      7 ^ 5 * (p.gapRoot * p.quotientRoot) =
          7 ^ 5 * p.gapRoot * p.quotientRoot := by ring
      _ = 7 ^ 6 * k := hk
      _ = 7 ^ 5 * (7 * k) := by ring
  have hseven :
      (7 : ℤ) ∣ p.gapRoot * p.quotientRoot :=
    ⟨k, hcancel⟩
  rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp hseven with
    hgap | hquotient
  · exact p.gapRoot_not_seven_dvd hgap
  · exact p.quotientRoot_not_seven_dvd hquotient

/-- Consequently the signed-root seventh-power difference is not itself
an integer seventh power.  If seven divided a seventh root, its seventh
power would contain `7^7`, contradicting the exact depth-five result. -/
theorem not_exists_signedRoot_seventhPowerDifference_eq_pow
    (p : RamifiedSignedRootDepthPacket) :
    ¬ ∃ c : ℤ,
      p.signedRightRoot ^ 7 - p.signedLeftRoot ^ 7 = c ^ 7 := by
  rintro ⟨c, hc⟩
  have hsevenGap :
      (7 : ℤ) ∣
        p.signedRightRoot ^ 7 - p.signedLeftRoot ^ 7 := by
    rw [p.signedRoot_seventhPowerDifference_eq]
    exact ⟨7 ^ 4 * p.gapRoot * p.quotientRoot, by ring⟩
  have hsevenPow : (7 : ℤ) ∣ c ^ 7 := by
    rw [← hc]
    exact hsevenGap
  have hsevenC : (7 : ℤ) ∣ c :=
    (show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow hsevenPow
  rcases hsevenC with ⟨d, hd⟩
  apply p.sevenPowSix_not_dvd_signedRoot_seventhPowerDifference
  rw [hc, hd]
  exact ⟨7 * d ^ 7, by ring⟩

/-- The most direct primitive signed-chart candidate,
`(signedRightRoot, -signedLeftRoot, c)`, is impossible for every integer
right-hand coordinate.  Coprimality of the two roots is already available;
it is the Fermat equation itself that fails at exact seven-adic depth five. -/
theorem no_direct_signedFermatSevenChart
    (p : RamifiedSignedRootDepthPacket) :
    ¬ ∃ c : ℤ,
      SignedFermatSevenChart
        p.signedRightRoot (-p.signedLeftRoot) c := by
  rintro ⟨c, chart⟩
  apply p.not_exists_signedRoot_seventhPowerDifference_eq_pow
  refine ⟨c, ?_⟩
  have heq := chart.equation
  have hneg :
      (-p.signedLeftRoot) ^ 7 =
        -(p.signedLeftRoot ^ 7) := by ring
  rw [hneg] at heq
  simpa [sub_eq_add_neg] using heq

end RamifiedSignedRootDepthPacket


end DkMath.FLT.Seven
