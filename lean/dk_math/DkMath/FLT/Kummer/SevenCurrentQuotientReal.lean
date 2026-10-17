/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentRootDepth
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitGapHeight

#print "file: DkMath.FLT.Kummer.SevenCurrentQuotientReal"

/-! # 共通商の実三次構造
根自身は六次環に保ち、補正商だけを実三次 gap の商へ接続する。
以下は保存等式であり、次の反例状態の再構成ではない。
-/
namespace DkMath.FLT.Kummer.SevenRealGN

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification
open SevenCyclotomicDegreeSixInt

noncomputable section

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}

private theorem inv32 : zetaInv ^ 32 = zeta ^ 3 := by
  rw [zetaInv_eq_pow_six, ← pow_mul]
  rw [show 6 * 32 = 7 * 27 + 3 by decide, pow_add, pow_mul, zeta_pow_seven]
  simp

/-- 実三次商から共通商を直接構成する。 -/
theorem common_quotient_real_spec (v : R)
    (hv : directOrbitGap p = SevenRealCubicInt.eisensteinAxis ^ 32 * v) :
    ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * (zeta ^ 3 * ofReal v) := by
  change ofReal (directOrbitGap p) = _
  rw [hv, map_mul, map_pow, ofReal_eisensteinAxis_eq, ← inv32]
  ring

/-- 非零な分岐因子を消去し、任意の共通商を同じ実三次商に同定する。 -/
theorem common_quotient_eq_real {w : C}
    (hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * w) (v : R)
    (hv : directOrbitGap p = SevenRealCubicInt.eisensteinAxis ^ 32 * v) :
    w = zeta ^ 3 * ofReal v := by
  exact mul_left_cancel₀ (pow_ne_zero _ ramifiedUniformizer_ne_zero)
    (hg.symm.trans (common_quotient_real_spec v hv))

/-- 共通商は共役で ζ 倍される。根自身の実性は要求しない。 -/
theorem common_quotient_star {w : C}
    (hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * w) : star w = zeta * w := by
  obtain ⟨v, hv⟩ := directOrbit_gap_axis_pow32_dvd p
  rw [common_quotient_eq_real hg v hv]
  have hs : star zeta = zetaInv := by ext <;> simp [zeta, zetaInv]
  simp only [star_mul, star_pow, hs, star_ofReal]
  rw [zetaInv_eq_pow_six, ← pow_mul]
  have he : zeta ^ 18 = zeta ^ 4 := by
    rw [show 18 = 7 * 2 + 4 by decide, pow_add, pow_mul, zeta_pow_seven]
    simp
  rw [he]
  ring

/-- 実三次像の六次ノルムは三次ノルムの平方。 -/
theorem cyclotomicNormHom_ofReal_square (v : R) :
    cyclotomicNormHom (ofReal v) = SevenRealCubicInt.norm v ^ 2 := by
  change SevenRealCubicInt.norm (QuadraticAlgebra.norm (algebraMap R C v)) = _
  rw [QuadraticAlgebra.norm_algebraMap, SevenRealCubicInt.norm_pow]

/-- ζ のノルムは1。 -/
theorem cyclotomicNormHom_zeta_one : cyclotomicNormHom zeta = 1 := by
  have hz : QuadraticAlgebra.norm zeta = 1 := by
    ext <;> norm_num [QuadraticAlgebra.norm_def, zeta, SevenRealCubicInt.mul]
  rw [cyclotomicNormHom_apply, hz]
  norm_num [SevenRealCubicInt.norm]

/-- 位相を除いた共通商のノルムは整数平方。 -/
theorem common_quotient_norm_square {w : C}
    (hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * w) (v : R)
    (hv : directOrbitGap p = SevenRealCubicInt.eisensteinAxis ^ 32 * v) :
    cyclotomicNormHom w = SevenRealCubicInt.norm v ^ 2 := by
  rw [common_quotient_eq_real hg v hv, map_mul, map_pow,
    cyclotomicNormHom_zeta_one, cyclotomicNormHom_ofReal_square, one_pow, one_mul]

/-- 六位相すべてに同じ M を使う。63は正確な付値ではなく下界である。 -/
theorem phase_root_correction_norm_seven_square (F : CurrentPhaseSeventhFamily p) :
    ∃ M : ℕ, ∀ i : Fin 6,
      Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) = 7 * M ^ 2 := by
  obtain ⟨w, hg, _, hn⟩ := exists_common_phase_root_correction_norm F
  obtain ⟨v, hv⟩ := directOrbit_gap_axis_pow32_dvd p
  refine ⟨7 ^ 31 * (SevenRealCubicInt.norm v).natAbs, fun i => ?_⟩
  rw [hn i, common_quotient_norm_square hg v hv, Int.natAbs_pow]
  ring

/-- 既存の小ノルムパケットの同じ gapRoot から実三次商を作る。 -/
theorem smaller_packet_real_quotient (S : DirectOrbitSmallerNormPacket p) :
    directOrbitGap p = SevenRealCubicInt.eisensteinAxis ^ 32 *
      (SevenRealCubicInt.eisensteinAxis ^ (42 * S.powerSplit.gapSplit.k) *
        (S.powerSplit.gapUnit : R) * S.powerSplit.gapRoot ^ 7) := by
  rw [S.powerSplit.gap_eq, S.powerSplit.gapCore_eq, pow_add]
  ring

/-- 保存商と小さい根を同じ証人上で結ぶ。再入可能な新反例はまだ構成しない。 -/
theorem common_quotient_smaller_packet {w : C}
    (hg : ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho) =
      ramifiedUniformizer ^ 64 * w) (S : DirectOrbitSmallerNormPacket p) :
    w = zeta ^ 3 * ofReal (SevenRealCubicInt.eisensteinAxis ^ (42 * S.powerSplit.gapSplit.k) *
      (S.powerSplit.gapUnit : R) * S.powerSplit.gapRoot ^ 7) ∧
    S.normRoot = (SevenRealCubicInt.norm S.powerSplit.gapRoot).natAbs ∧
    0 < S.normRoot ∧ S.normRoot < S.powerSplit.gapSplit.a :=
  ⟨common_quotient_eq_real hg _ (smaller_packet_real_quotient S),
    S.normRoot_eq, S.normRoot_pos, S.normRoot_lt⟩
/-- 同じ小ノルムパケットが六つすべての補正ノルムを決める。
M の選択と小さい根の選択を別々の存在証明にしない。 -/
theorem phase_root_correction_norm_smaller_packet
    (F : CurrentPhaseSeventhFamily p) (S : DirectOrbitSmallerNormPacket p)
    (i : Fin 6) :
    Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) =
      7 * (7 ^ 31 * (7 ^ (42 * S.powerSplit.gapSplit.k) * S.normRoot ^ 7)) ^ 2 := by
  obtain ⟨w, hg, _, hn⟩ := exists_common_phase_root_correction_norm F
  rw [hn i, common_quotient_norm_square hg _ (smaller_packet_real_quotient S),
    Int.natAbs_pow]
  have hv : (SevenRealCubicInt.norm
      (SevenRealCubicInt.eisensteinAxis ^ (42 * S.powerSplit.gapSplit.k) *
        (S.powerSplit.gapUnit : R) * S.powerSplit.gapRoot ^ 7)).natAbs =
      7 ^ (42 * S.powerSplit.gapSplit.k) * S.normRoot ^ 7 := by
    rw [mul_assoc, SevenRealCubicInt.norm_mul, Int.natAbs_mul,
      gapHeight_natAbs_norm_eisensteinAxis_pow, gapHeight_natAbs_norm_gapCore_eq,
      ← S.normRoot_eq]
  rw [hv]
  ring

/-- 正の共通平方根 M と六位相の等式。正値性も同じ既存パケットから得る。 -/
theorem phase_root_correction_norm_seven_square_pos (F : CurrentPhaseSeventhFamily p) :
    ∃ M : ℕ, 0 < M ∧ ∀ i : Fin 6,
      Int.natAbs (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)) = 7 * M ^ 2 := by
  obtain ⟨S⟩ := directOrbitSmallerNormPacket p
  refine ⟨7 ^ 31 * (7 ^ (42 * S.powerSplit.gapSplit.k) * S.normRoot ^ 7),
    ?_, phase_root_correction_norm_smaller_packet F S⟩
  have := S.normRoot_pos
  positivity

/-- 補正ノルムの7進付値は奇数。深度63が正確という主張ではない。 -/
theorem phase_root_correction_norm_valuation_odd (F : CurrentPhaseSeventhFamily p)
    (i : Fin 6) :
    Odd (padicValNat 7 (Int.natAbs
      (cyclotomicNormHom (F.root i ^ 7 + ofReal p.rho)))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨M, hM, hn⟩ := phase_root_correction_norm_seven_square_pos F
  rw [hn i, padicValNat.mul (by decide) (pow_ne_zero _ (Nat.ne_of_gt hM)),
    padicValNat_self, padicValNat.pow]
  exact ⟨padicValNat 7 M, by omega⟩

end
end DkMath.FLT.Kummer.SevenRealGN
