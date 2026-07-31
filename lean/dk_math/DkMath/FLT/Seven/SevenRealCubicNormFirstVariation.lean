/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedSignedRootDepth

#print "file: DkMath.FLT.Seven.SevenRealCubicNormFirstVariation"

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenRealCubicInt

/-- Explicit quotient of the norm first variation by `7^4`. -/
def normFirstVariationCoefficient
    (x core : SevenRealCubicInt) : ℤ :=
  -x.fst ^ 2 * core.fst - x.fst ^ 2 * core.thd -
  2 * x.fst * x.snd * core.fst +
  x.fst * x.snd * core.snd -
  x.fst * x.snd * core.thd -
  5 * x.fst * x.thd * core.fst +
  x.fst * x.thd * core.snd -
  3 * x.fst * x.thd * core.thd +
  x.snd ^ 2 * core.snd -
  x.snd * x.thd * core.fst +
  2 * x.snd * x.thd * core.snd -
  x.snd * x.thd * core.thd +
  2 * x.thd ^ 2 * core.fst * (-1) -
  x.thd ^ 2 * core.thd +
  343 *
    (2 * x.fst * core.fst ^ 2 +
      x.fst * core.fst * core.snd +
      5 * x.fst * core.fst * core.thd -
      x.fst * core.snd ^ 2 +
      2 * x.fst * core.thd ^ 2 +
      3 * x.snd * core.fst ^ 2 -
      x.snd * core.fst * core.snd +
      3 * x.snd * core.fst * core.thd -
      2 * x.snd * core.snd ^ 2 -
      x.snd * core.snd * core.thd +
      x.snd * core.thd ^ 2 +
      7 * x.thd * core.fst ^ 2 -
      x.thd * core.fst * core.snd +
      8 * x.thd * core.fst * core.thd -
      3 * x.thd * core.snd ^ 2 +
      x.thd * core.snd * core.thd +
      2 * x.thd * core.thd ^ 2) -
  117649 * norm core

def sevenCubeAxisPerturbation
    (core : SevenRealCubicInt) : SevenRealCubicInt :=
  ⟨343 * (-3 * core.fst - core.thd),
    343 * (core.fst - 3 * core.snd + core.thd),
    343 * (core.snd - core.thd)⟩

set_option maxHeartbeats 800000 in
-- Normalizing the cubic-order multiplication by the scalar `7^3` is large.
set_option maxRecDepth 100000 in
theorem seven_cube_axis_mul_eq_perturbation
    (core : SevenRealCubicInt) :
    7 ^ 3 * eisensteinAxis * core =
      sevenCubeAxisPerturbation core := by
  rcases core with ⟨d, e, f⟩
  have h343 : (343 : SevenRealCubicInt) = ofInt 343 := by
    apply ext
    · exact fst_natCast 343
    · exact snd_natCast 343
    · exact thd_natCast 343
  have hseven : (7 : SevenRealCubicInt) ^ 3 = ofInt 343 := by
    calc
      (7 : SevenRealCubicInt) ^ 3 = 343 := by norm_num
      _ = ofInt 343 := h343
  rw [hseven]
  ext <;>
    norm_num [sevenCubeAxisPerturbation, eisensteinAxis] <;> ring

/- Coordinate proof of the `theta`-direction norm first variation. -/
set_option maxHeartbeats 800000 in
-- The explicit cubic expansion is deliberately checked by normalization.
set_option maxRecDepth 100000 in
theorem norm_add_seven_cube_axis_mul
    (x core : SevenRealCubicInt) :
    norm (x + 7 ^ 3 * eisensteinAxis * core) - norm x =
      7 ^ 4 * normFirstVariationCoefficient x core := by
  rw [seven_cube_axis_mul_eq_perturbation]
  rcases x with ⟨a, b, c⟩
  rcases core with ⟨d, e, f⟩
  norm_num [norm, normFirstVariationCoefficient,
    sevenCubeAxisPerturbation]
  ring

end SevenRealCubicInt

namespace RamifiedRealCubicDepthLedgerPacket

open SevenRealCubicInt

/-- Theta depth ten is precisely a `7^3*theta` perturbation. -/
theorem exists_normVariationCore
    (p : RamifiedRealCubicDepthLedgerPacket) :
    ∃ core : SevenRealCubicInt,
      p.exactPower.rightRoot =
        p.exactPower.leftRoot +
          7 ^ 3 * eisensteinAxis * core := by
  let u : SevenRealCubicIntˣ := thetaSevenUnit_isUnit.unit
  let core : SevenRealCubicInt :=
    ((u⁻¹ ^ 3 : SevenRealCubicIntˣ) : SevenRealCubicInt) *
      p.gapCore
  have hu :
      (u : SevenRealCubicInt) = thetaSevenUnit :=
    thetaSevenUnit_isUnit.unit_spec
  have hinv :
      ((u : SevenRealCubicInt) ^ 3) *
          (((u⁻¹ ^ 3 : SevenRealCubicIntˣ) :
            SevenRealCubicInt)) = 1 := by
    exact congrArg
      (fun v : SevenRealCubicIntˣ => (v : SevenRealCubicInt))
      (by group : u ^ 3 * u⁻¹ ^ 3 = 1)
  refine ⟨core, ?_⟩
  have hgap :
      p.exactPower.rightRoot - p.exactPower.leftRoot =
        eisensteinAxis ^ 10 * p.gapCore := by
    rw [← p.rootGap_def, p.rootGap_eq]
  have hgap' :
    p.exactPower.rightRoot - p.exactPower.leftRoot =
        7 ^ 3 * eisensteinAxis * core := by
    calc
      _ = eisensteinAxis ^ 10 * p.gapCore := hgap
      _ = 7 ^ 3 * eisensteinAxis * core := by
        dsimp [core]
        rw [show (7 : SevenRealCubicInt) =
            eisensteinAxis ^ 3 * (u : SevenRealCubicInt) by
          rw [hu]
          exact seven_eq_eisensteinAxis_cube_mul_unit]
        rw [show
          (eisensteinAxis ^ 3 * (u : SevenRealCubicInt)) ^ 3 =
            eisensteinAxis ^ 9 * (u : SevenRealCubicInt) ^ 3 by ring]
        calc
          eisensteinAxis ^ 10 * p.gapCore =
              eisensteinAxis ^ 10 *
                ((u : SevenRealCubicInt) ^ 3 *
                  ((u⁻¹ ^ 3 : SevenRealCubicIntˣ) :
                    SevenRealCubicInt)) * p.gapCore := by
            rw [hinv, mul_one]
          _ = _ := by
            rw [Units.val_pow_eq_pow_val]
            ring
  calc
    p.exactPower.rightRoot =
        (p.exactPower.rightRoot -
          p.exactPower.leftRoot) +
          p.exactPower.leftRoot := by abel
    _ = 7 ^ 3 * eisensteinAxis * core +
        p.exactPower.leftRoot := by rw [hgap']
    _ = _ := by abel

end RamifiedRealCubicDepthLedgerPacket

/-- FUSION-001B: the coordinate first variation and the independent signed
integer route identify the same depth-four leading coefficient. -/
structure RamifiedNormFirstVariationPacket : Type where
  signedDepth : RamifiedSignedRootDepthPacket
  variationCore : SevenRealCubicInt
  algebraicGap_eq :
    signedDepth.balanced.axisDrop.depthLedger.exactPower.rightRoot =
      signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot +
        7 ^ 3 * SevenRealCubicInt.eisensteinAxis * variationCore
  normGap_eq :
    SevenRealCubicInt.norm
          signedDepth.balanced.axisDrop.depthLedger.exactPower.rightRoot -
        SevenRealCubicInt.norm
          signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot =
      7 ^ 4 *
        SevenRealCubicInt.normFirstVariationCoefficient
          signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot
          variationCore
  coefficient_eq_gapRoot :
    SevenRealCubicInt.normFirstVariationCoefficient
        signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot
        variationCore =
      signedDepth.gapRoot

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt

theorem nonempty_normFirstVariation
    (p : RamifiedSignedRootDepthPacket) :
    Nonempty RamifiedNormFirstVariationPacket := by
  let ledger := p.balanced.axisDrop.depthLedger
  rcases ledger.exists_normVariationCore with ⟨core, hcore⟩
  have hvariation :=
    norm_add_seven_cube_axis_mul
      ledger.exactPower.leftRoot core
  rw [← hcore] at hvariation
  have hsigned :
      norm ledger.exactPower.rightRoot -
          norm ledger.exactPower.leftRoot =
        7 ^ 4 * p.gapRoot := by
    rw [ledger.exactPower.norm_leftRoot_eq_signedRoot,
      ledger.exactPower.norm_rightRoot_eq_signedRoot,
      ← p.signedLeftRoot_eq, ← p.signedRightRoot_eq,
      p.signedGap_eq]
  have hcoefficient :
      normFirstVariationCoefficient
          ledger.exactPower.leftRoot core =
        p.gapRoot := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 4 : ℤ) ≠ 0)
    exact hvariation.symm.trans hsigned
  exact ⟨{
    signedDepth := p
    variationCore := core
    algebraicGap_eq := hcore
    normGap_eq := hvariation
    coefficient_eq_gapRoot := hcoefficient }⟩

end RamifiedSignedRootDepthPacket


end

end DkMath.FLT.Seven
