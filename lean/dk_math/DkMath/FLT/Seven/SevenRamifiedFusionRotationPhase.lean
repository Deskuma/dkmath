/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclicBridge

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRotationPhase"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 2000
set_option linter.style.longLine false

namespace SevenRealCubicInt

/-- Rotation sends the ramified parameter `theta` to
`theta * (theta + 4)`.  The second factor is a theta-adic unit. -/
theorem rotateEquiv_eisensteinAxis :
    rotateEquiv eisensteinAxis =
      eisensteinAxis ^ 2 + 4 * eisensteinAxis := by
  have hfour : (4 : SevenRealCubicInt) = ofInt 4 := by
    apply ext
    · exact fst_natCast 4
    · exact snd_natCast 4
    · exact thd_natCast 4
  rw [hfour]
  ext <;>
    norm_num [rotateEquiv, rotateHom, eisensteinAxis, mul, pow_two]

/-- Rotation acts trivially on the residue field at `theta`. -/
theorem thetaResidue_rotateEquiv (x : SevenRealCubicInt) :
    thetaResidue (rotateEquiv x) = thetaResidue x := by
  rcases x with ⟨a, b, c⟩
  simp only [thetaResidue, rotateEquiv, rotateHom, Int.reduceNeg, neg_mul,
    RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, OneHom.toFun_eq_coe, OneHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, thetaConstModSeven,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_neg]
  rw [show (9 : ZMod 7) = 2 by decide]
  ring_nf
  rw [show (5 : ZMod 7) = -2 by decide,
    show (4 : ZMod 7) = -3 by decide]
  ring

@[simp] theorem thetaResidue_eisensteinAxis_add_four :
    thetaResidue (eisensteinAxis + 4) = 4 := by
  have hfour : (4 : SevenRealCubicInt) = ofInt 4 := by
    apply ext
    · exact fst_natCast 4
    · exact snd_natCast 4
    · exact thd_natCast 4
  rw [hfour, map_add]
  norm_num [thetaResidue, thetaConstModSeven, eisensteinAxis]

/-- At exact theta depth ten, rotation multiplies the residual core by
`4^10 = 4` in `ZMod 7`. -/
theorem rotate_depthTen_thetaResidue
    {g rotatedCore : SevenRealCubicInt}
    (h :
      rotateEquiv (eisensteinAxis ^ 10 * g) =
        eisensteinAxis ^ 10 * rotatedCore) :
    thetaResidue rotatedCore =
      4 * thetaResidue g := by
  have hfactor :
      eisensteinAxis ^ 10 *
          ((eisensteinAxis + 4) ^ 10 * rotateEquiv g) =
        eisensteinAxis ^ 10 * rotatedCore := by
    calc
      _ = (eisensteinAxis * (eisensteinAxis + 4)) ^ 10 *
          rotateEquiv g := by ring
      _ = rotateEquiv (eisensteinAxis ^ 10 * g) := by
        rw [map_mul, map_pow, rotateEquiv_eisensteinAxis]
        congr 2
      _ = _ := h
  have hcore :
      (eisensteinAxis + 4) ^ 10 * rotateEquiv g = rotatedCore := by
    exact mul_left_cancel₀ (pow_ne_zero 10 eisensteinAxis_prime.ne_zero) hfactor
  have hr := congrArg thetaResidue hcore
  rw [map_mul, map_pow, thetaResidue_eisensteinAxis_add_four,
    thetaResidue_rotateEquiv] at hr
  norm_num at hr
  exact hr.symm

/-- The canonical residual core obtained after one real-cubic rotation. -/
def rotateDepthTenCore (g : SevenRealCubicInt) : SevenRealCubicInt :=
  (eisensteinAxis + 4) ^ 10 * rotateEquiv g

theorem rotate_depthTen_eq
    (g : SevenRealCubicInt) :
    rotateEquiv (eisensteinAxis ^ 10 * g) =
      eisensteinAxis ^ 10 * rotateDepthTenCore g := by
  calc
    _ = (eisensteinAxis * (eisensteinAxis + 4)) ^ 10 *
        rotateEquiv g := by
      rw [map_mul, map_pow, rotateEquiv_eisensteinAxis]
      congr 2
    _ = _ := by
      simp only [rotateDepthTenCore]
      ring

theorem rotateDepthTenCore_thetaResidue
    (g : SevenRealCubicInt) :
    thetaResidue (rotateDepthTenCore g) = 4 * thetaResidue g :=
  rotate_depthTen_thetaResidue (rotate_depthTen_eq g)

end SevenRealCubicInt

namespace RamifiedPairedThetaRootJetPacket

/-- The signed residual amplitude `m` before projectivizing by the nonzero
coefficient `a`. -/
def rotationAmplitude
    (p : RamifiedPairedThetaRootJetPacket) : ZMod 7 :=
  p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot

/-- The three residual leading coefficients encountered around the order-three
real-cubic rotation orbit.  This packet records residues only; it does not
identify a routing column or reconstruct a source-plane chart. -/
structure RotatedGapCoreResiduePacket
    (p : RamifiedPairedThetaRootJetPacket) where
  core0 : SevenRealCubicInt
  core1 : SevenRealCubicInt
  core2 : SevenRealCubicInt
  core0_eq :
    core0 = p.signedDepth.balanced.axisDrop.depthLedger.gapCore
  core1_eq : core1 = SevenRealCubicInt.rotateDepthTenCore core0
  core2_eq : core2 = SevenRealCubicInt.rotateDepthTenCore core1
  residue0 :
    SevenRealCubicInt.thetaResidue core0 = -2 * p.rotationAmplitude
  residue1 :
    SevenRealCubicInt.thetaResidue core1 = -p.rotationAmplitude
  residue2 :
    SevenRealCubicInt.thetaResidue core2 = 3 * p.rotationAmplitude

/-- The three cores as an explicitly indexed order-three family. -/
def RotatedGapCoreResiduePacket.coreAt
    {p : RamifiedPairedThetaRootJetPacket}
    (r : RotatedGapCoreResiduePacket p) (i : Fin 3) :
    SevenRealCubicInt :=
  Fin.cases r.core0
    (fun j : Fin 2 =>
      Fin.cases r.core1 (fun _ : Fin 1 => r.core2) j) i

/-- Expected leading residue at each of the three rotation positions. -/
def rotationResidueAt
    (p : RamifiedPairedThetaRootJetPacket) (i : Fin 3) : ZMod 7 :=
  Fin.cases (-2 * p.rotationAmplitude)
    (fun j : Fin 2 =>
      Fin.cases (-p.rotationAmplitude)
        (fun _ : Fin 1 => 3 * p.rotationAmplitude) j) i

theorem RotatedGapCoreResiduePacket.thetaResidue_coreAt
    {p : RamifiedPairedThetaRootJetPacket}
    (r : RotatedGapCoreResiduePacket p) (i : Fin 3) :
    SevenRealCubicInt.thetaResidue (r.coreAt i) =
      rotationResidueAt p i := by
  fin_cases i
  · exact r.residue0
  · exact r.residue1
  · exact r.residue2

/-- The paired root gap canonically supplies all three rotation residues
`-2*m`, `-m`, and `3*m`. -/
def rotatedGapCoreResidues
    (p : RamifiedPairedThetaRootJetPacket) :
    RotatedGapCoreResiduePacket p where
  core0 := p.signedDepth.balanced.axisDrop.depthLedger.gapCore
  core1 := SevenRealCubicInt.rotateDepthTenCore
    p.signedDepth.balanced.axisDrop.depthLedger.gapCore
  core2 := SevenRealCubicInt.rotateDepthTenCore
    (SevenRealCubicInt.rotateDepthTenCore
      p.signedDepth.balanced.axisDrop.depthLedger.gapCore)
  core0_eq := rfl
  core1_eq := rfl
  core2_eq := rfl
  residue0 := by
    simpa [rotationAmplitude] using p.gapCore_thetaResidue_eq
  residue1 := by
    rw [SevenRealCubicInt.rotateDepthTenCore_thetaResidue,
      p.gapCore_thetaResidue_eq]
    simp [rotationAmplitude]
    ring_nf
    rw [show (8 : ZMod 7) = 1 by decide, mul_one]
  residue2 := by
    rw [SevenRealCubicInt.rotateDepthTenCore_thetaResidue,
      SevenRealCubicInt.rotateDepthTenCore_thetaResidue,
      p.gapCore_thetaResidue_eq]
    simp [rotationAmplitude]
    ring_nf
    rw [show (32 : ZMod 7) = 4 by decide]
    rw [show (4 : ZMod 7) = -3 by decide]
    ring

end RamifiedPairedThetaRootJetPacket


end

end DkMath.FLT.Seven
