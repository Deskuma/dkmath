/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentQuotientReal

#print "file: DkMath.FLT.Kummer.SevenCurrentCorrectionPower"

/-! # 六補正項の共通七乗主イデアル
同じ小ノルムパケットの根から Gamma を構成し、六位相の係数を単元として残す。
相対単元は位相だけで決まり、共通根のノルムの減少は主張しない。
-/
namespace DkMath.FLT.Kummer.SevenRealGN

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open SevenCyclotomicDegreeSixInt

noncomputable section

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

/-- 同じ S の gapRoot を使う共通根。lambda^9 を含み、小さい高さは保証しない。 -/
def correctionCommonRoot (S : DirectOrbitSmallerNormPacket p) : C :=
  ramifiedUniformizer ^ 9 * ofReal
    (SevenRealCubicInt.eisensteinAxis ^ (6 * S.powerSplit.gapSplit.k) *
      S.powerSplit.gapRoot)

/-- 七乗に吸収しない係数を、六つの実際の単元として記録する。 -/
def correctionPhaseUnit (S : DirectOrbitSmallerNormPacket p) (i : Fin 6) : Cˣ :=
  zetaUnit ^ 3 * (phaseRootTwist i)⁻¹ *
    Units.map ofReal.toMonoidHom S.powerSplit.gapUnit

/-- 全六補正項は同じ明示的な根の七乗の単元倍。 -/
theorem correction_common_root_factor (F : CurrentPhaseSeventhFamily p)
    (S : DirectOrbitSmallerNormPacket p) (i : Fin 6) :
    F.root i ^ 7 + ofReal p.rho =
      (correctionPhaseUnit S i : C) * correctionCommonRoot S ^ 7 := by
  change _ = (zeta ^ 3 * (↑((phaseRootTwist i)⁻¹) : C) *
    ofReal (S.powerSplit.gapUnit : R)) *
    (ramifiedUniformizer ^ 9 * ofReal
      (SevenRealCubicInt.eisensteinAxis ^ (6 * S.powerSplit.gapSplit.k) *
        S.powerSplit.gapRoot)) ^ 7
  obtain ⟨w, hg, hw⟩ := exists_common_phase_root_correction F
  rw [hw i, (common_quotient_smaller_packet hg S).1]
  simp only [map_mul, map_pow, mul_pow, ← pow_mul]
  have he : (6 * S.powerSplit.gapSplit.k) * 7 = 42 * S.powerSplit.gapSplit.k := by omega
  rw [he]
  ring

/-- 因子表示を主イデアルへ送る。単元が消え、共通の七乗主イデアルが残る。 -/
theorem correction_common_root_ideal (F : CurrentPhaseSeventhFamily p)
    (S : DirectOrbitSmallerNormPacket p) (i : Fin 6) :
    Ideal.span ({F.root i ^ 7 + ofReal p.rho} : Set C) =
      Ideal.span ({correctionCommonRoot S} : Set C) ^ 7 := by
  rw [correction_common_root_factor F S i,
    Ideal.span_singleton_mul_left_unit (correctionPhaseUnit S i).isUnit,
    Ideal.span_singleton_pow]

/-- 相対係数から実三次単元、根、深度が消える。等式は単元群そのもので成立する。 -/
theorem correction_phase_unit_ratio (S : DirectOrbitSmallerNormPacket p) (i j : Fin 6) :
    correctionPhaseUnit S i * (correctionPhaseUnit S j)⁻¹ =
      phaseRootTwist j * (phaseRootTwist i)⁻¹ := by
  simp [correctionPhaseUnit, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- 共通根の絶対ノルム。実三次部分のノルムは平方として寄与する。 -/
theorem correction_common_root_norm (S : DirectOrbitSmallerNormPacket p) :
    Int.natAbs (cyclotomicNormHom (correctionCommonRoot S)) =
      7 ^ (9 + 12 * S.powerSplit.gapSplit.k) * S.normRoot ^ 2 := by
  simp only [correctionCommonRoot, map_mul, map_pow,
    cyclotomicNormHom_ramifiedUniformizer, cyclotomicNormHom_ofReal_square,
    Int.natAbs_mul, Int.natAbs_pow]
  rw [SevenRealCubicInt.norm_eisensteinAxis, ← S.normRoot_eq]
  change 7 ^ 9 * ((7 ^ 2) ^ (6 * S.powerSplit.gapSplit.k) * S.normRoot ^ 2) = _
  rw [← pow_mul]
  have he : 2 * (6 * S.powerSplit.gapSplit.k) = 12 * S.powerSplit.gapSplit.k := by omega
  rw [he, pow_add]
  ring

/-- 共通根は非零のノルムを持つ。これは高さの上界を与えない。 -/
theorem correction_common_root_norm_pos (S : DirectOrbitSmallerNormPacket p) :
    0 < Int.natAbs (cyclotomicNormHom (correctionCommonRoot S)) := by
  rw [correction_common_root_norm S]
  have := S.normRoot_pos
  positivity

/-- 補正ノルムは同じ自然数の完全七乗である。 -/
theorem correction_norm_seventh (F : CurrentPhaseSeventhFamily p)
    (S : DirectOrbitSmallerNormPacket p) (i : Fin 6) :
    Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
      (7 ^ (9 + 12 * S.powerSplit.gapSplit.k) * S.normRoot ^ 2) ^ 7 := by
  rw [correction_common_root_factor F S i, map_mul, map_pow,
    Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_of_isUnit ((correctionPhaseUnit S i).isUnit.map cyclotomicNormHom),
    one_mul, correction_common_root_norm S]

/-- 固定した F,S の共通根、単元、因子表示、イデアル冪と相対係数を同じデータで保存する。 -/
structure CurrentCorrectionPowerPacket (F : CurrentPhaseSeventhFamily p)
    (S : DirectOrbitSmallerNormPacket p) where
  commonRoot : C
  phaseUnit : Fin 6 → Cˣ
  commonRoot_eq : commonRoot = correctionCommonRoot S
  phaseUnit_eq : ∀ i, phaseUnit i = correctionPhaseUnit S i
  factor : ∀ i, F.root i ^ 7 + ofReal p.rho = (phaseUnit i : C) * commonRoot ^ 7
  ideal : ∀ i, Ideal.span ({F.root i ^ 7 + ofReal p.rho} : Set C) =
    Ideal.span ({commonRoot} : Set C) ^ 7
  ratio : ∀ i j, phaseUnit i * (phaseUnit j)⁻¹ = phaseRootTwist j * (phaseRootTwist i)⁻¹
  norm : Int.natAbs (cyclotomicNormHom commonRoot) =
    7 ^ (9 + 12 * S.powerSplit.gapSplit.k) * S.normRoot ^ 2
  norm_pos : 0 < Int.natAbs (cyclotomicNormHom commonRoot)
  correctionNorm : ∀ i, Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
    (7 ^ (9 + 12 * S.powerSplit.gapSplit.k) * S.normRoot ^ 2) ^ 7

/-- 選択に依存しない明示的な構成。S の小さい根を別の証人に交換しない。 -/
def currentCorrectionPowerPacket (F : CurrentPhaseSeventhFamily p)
    (S : DirectOrbitSmallerNormPacket p) : CurrentCorrectionPowerPacket F S where
  commonRoot := correctionCommonRoot S
  phaseUnit := correctionPhaseUnit S
  commonRoot_eq := rfl
  phaseUnit_eq _ := rfl
  factor := correction_common_root_factor F S
  ideal := correction_common_root_ideal F S
  ratio := correction_phase_unit_ratio S
  norm := correction_common_root_norm S
  norm_pos := correction_common_root_norm_pos S
  correctionNorm := correction_norm_seventh F S

end
end DkMath.FLT.Kummer.SevenRealGN
