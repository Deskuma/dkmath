/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenGNSource

#print "file: DkMath.FLT.Kummer.SevenRealUnitObstruction"

/-!
# 実三次 GN の単元障害：ノルム二成分と共役位相一成分

六次単元の七乗性を、実三次ノルムの二成分対数と μ₇ に値を持つ共役位相で判定する。
位相は共役比の八乗を取り、± の符号を消して七乗根の群へ送る。
整数との合同を仮定せず、任意の六次単元の障害として定義する。
-/

namespace DkMath.FLT.Kummer.SevenRealGN

open scoped NumberField
open NumberField DkMath.FLT.Seven
open DkMath.FLT.Kummer.SevenPrimaryNorm

noncomputable section

/-- この章の実三次係数環。 -/
abbrev R := SevenRealCubicInt
/-- 実三次環上の既存六次円分環。 -/
abbrev C := SevenCyclotomicDegreeSixInt.Ring

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- 二次共役を単元群に適用する乗法的写像。 -/
def unitConj : Cˣ →* Cˣ := Units.map (starRingAut : C ≃+* C).toMonoidHom

/-- 単元の共役比。乗法性を明示し、七乗の取り替えを追跡する。 -/
def unitRatio : Cˣ →* Cˣ where
  toFun u := u * (unitConj u)⁻¹
  map_one' := by simp
  map_mul' u v := by simp only [map_mul, mul_inv_rev]; ac_rfl

/-- 具体的な共役比は、前章の CM 共役比を同じ環同型で運んだ元である。 -/
theorem unitRatio_transport (u : Cˣ) :
    Units.map integralEquiv.toMonoidHom
      (conjugateRatio (Units.map integralEquiv.symm.toMonoidHom u)) = unitRatio u := by
  let v := Units.map integralEquiv.symm.toMonoidHom u
  have hv : Units.map integralEquiv.toMonoidHom v = u := by
    apply Units.ext
    exact integralEquiv.apply_symm_apply (u : C)
  have hc : Units.map integralEquiv.toMonoidHom (Units.map integralConj.toMonoidHom v) = unitConj u := by
    apply Units.ext
    change integralEquiv (integralConj (integralEquiv.symm (u : C))) = star (u : C)
    rw [integralEquiv_conj, RingEquiv.apply_symm_apply]
  change Units.map integralEquiv.toMonoidHom (v * (Units.map integralConj.toMonoidHom v)⁻¹) =
    u * (unitConj u)⁻¹
  rw [map_mul, map_inv, hv, hc]

/-- CM 単元定理から得られる有限位相の具体的分類。まだ合同は要求しない。 -/
theorem unitRatio_signed_root (u : Cˣ) :
    ∃ i < 7, unitRatio u = SevenCyclotomicDegreeSixInt.zetaUnit ^ i ∨
      unitRatio u = -SevenCyclotomicDegreeSixInt.zetaUnit ^ i := by
  let v := Units.map integralEquiv.symm.toMonoidHom u
  have hf : IsOfFinOrder ((conjugateRatio v : 𝓞 (CyclotomicField 7 ℚ)) : CyclotomicField 7 ℚ) :=
    ((algebraMap (𝓞 (CyclotomicField 7 ℚ)) (CyclotomicField 7 ℚ)).toMonoidHom.comp
      (Units.coeHom (𝓞 (CyclotomicField 7 ℚ)))).isOfFinOrder (conjugateRatio_finite v)
  obtain ⟨i, hi, hh⟩ := septicRoot_spec.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide) hf
  have hc : (unitRatio u : C) = integralEquiv (conjugateRatio v : _) :=
    (congrArg Units.val (unitRatio_transport u)).symm
  refine ⟨i, hi, ?_⟩
  rcases hh with hp | hm
  · have he : (conjugateRatio v : 𝓞 (CyclotomicField 7 ℚ)) = septicRoot_spec.toInteger ^ i :=
      RingOfIntegers.coe_injective hp
    apply Or.inl
    apply Units.ext
    change (unitRatio u : C) = SevenCyclotomicDegreeSixInt.zeta ^ i
    rw [hc, he, map_pow, integralEquiv_septicRoot]
  · have he : (conjugateRatio v : 𝓞 (CyclotomicField 7 ℚ)) = -septicRoot_spec.toInteger ^ i :=
      RingOfIntegers.coe_injective hm
    apply Or.inr
    apply Units.ext
    change (unitRatio u : C) = -SevenCyclotomicDegreeSixInt.zeta ^ i
    rw [hc, he, map_neg, map_pow, integralEquiv_septicRoot]

/-- 共役比の位数は14を割る。位相を μ₇ に射影するための有限性の証明。 -/
theorem unitRatio_pow_fourteen (u : Cˣ) : unitRatio u ^ 14 = 1 := by
  have hz : SevenCyclotomicDegreeSixInt.zetaUnit ^ 14 = 1 := by
    rw [show 14 = 7 * 2 by decide, pow_mul, SevenCyclotomicDegreeSixInt.zetaUnit_pow_seven, one_pow]
  obtain ⟨i, _, h | h⟩ := unitRatio_signed_root u
  · rw [h, pow_right_comm, hz, one_pow]
  · rw [h, neg_pow, pow_right_comm, hz]
    norm_num

/-- 共役比の八乗は七乗すると1。8は偶数かつ mod 7 で1なので符号だけを消す。 -/
theorem unitRatio_eighth_pow_seven (u : Cˣ) : (unitRatio u ^ 8) ^ 7 = 1 := by
  rw [← pow_mul, show 8 * 7 = 14 * 4 by decide, pow_mul, unitRatio_pow_fourteen, one_pow]

/-- 共役位相の一成分。値域は実際の七乗根の群 μ₇。 -/
def phaseCharacter : Cˣ →* rootsOfUnity 7 C where
  toFun u := ⟨unitRatio u ^ 8, (mem_rootsOfUnity _ _).mpr (unitRatio_eighth_pow_seven u)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := by
    apply Subtype.ext
    change unitRatio (u * v) ^ 8 = unitRatio u ^ 8 * unitRatio v ^ 8
    rw [map_mul, mul_pow]

/-- 位相の値域は7元の群である。任意の単元商群全体の分類を仮定していない。 -/
theorem phase_target_card : Nat.card (rootsOfUnity 7 C) = 7 :=
  SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot.card_rootsOfUnity

/-- 実三次ノルムの二つの障害座標。 -/
def normCoordinates (u : Cˣ) : ZMod 7 × ZMod 7 :=
  SevenRealCubicInt.projectiveLog (Additive.ofMul (Units.map relativeNorm u))

/-- ノルムの二成分は単元の積に対して加法的。 -/
theorem normCoordinates_mul (u v : Cˣ) :
    normCoordinates (u * v) = normCoordinates u + normCoordinates v := by
  simp only [normCoordinates, map_mul, ofMul_mul, map_add]

/-- 七乗単元の実ノルム対数は零。 -/
theorem normCoordinates_seventh (u : Cˣ) : normCoordinates (u ^ 7) = 0 := by
  unfold normCoordinates
  rw [map_pow]
  exact SevenRealCubicInt.projectiveLog_pow_seven _

/-- 七乗単元の共役位相は1。 -/
theorem phaseCharacter_seventh (u : Cˣ) : phaseCharacter (u ^ 7) = 1 := by
  apply Subtype.ext
  change unitRatio (u ^ 7) ^ 8 = 1
  rw [map_pow, pow_right_comm]
  exact unitRatio_eighth_pow_seven u

/-- 二つの実ノルム座標と一つの共役位相を同時に保持する。 -/
def unitObstruction (u : Cˣ) : (ZMod 7 × ZMod 7) × rootsOfUnity 7 C :=
  (normCoordinates u, phaseCharacter u)

/-- 実ノルムと共役比の積は、同じ単元の平方を復元する。 -/
theorem unit_square_eq_norm_ratio (u : Cˣ) :
    u ^ 2 = Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom
      (Units.map relativeNorm u) * unitRatio u := by
  let v := Units.map integralEquiv.symm.toMonoidHom u
  have hu : integralEquiv (v : _) = (u : C) := integralEquiv.apply_symm_apply _
  have hr : integralEquiv (conjugateRatio v : _) = (unitRatio u : C) :=
    congrArg Units.val (unitRatio_transport u)
  have hh := unit_square_eq_norm_mul_ratio v
  change integralEquiv (v : _) ^ 2 =
    SevenCyclotomicDegreeSixInt.ofReal (relativeNorm (integralEquiv (v : _))) *
      integralEquiv (conjugateRatio v : _) at hh
  rw [hu, hr] at hh
  apply Units.ext
  change (u : C) ^ 2 = SevenCyclotomicDegreeSixInt.ofReal (relativeNorm (u : C)) * (unitRatio u : C)
  exact hh

/-- 障害消滅は七乗性の必要十分条件。
ノルムの二成分と μ₇ の位相一成分のどちらも省略しない。 -/
theorem unit_seventh_iff_obstruction (u : Cˣ) :
    (∃ k : Cˣ, u = k ^ 7) ↔ normCoordinates u = 0 ∧ phaseCharacter u = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨normCoordinates_seventh k, phaseCharacter_seventh k⟩
  · rintro ⟨hN, hphase⟩
    obtain ⟨v, hv⟩ := (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
      (Units.map relativeNorm u)).mpr hN
    have h8 : unitRatio u ^ 8 = 1 := congrArg Subtype.val hphase
    have h2 : unitRatio u ^ 2 = 1 := by
      calc
        unitRatio u ^ 2 = (unitRatio u ^ 8) ^ 2 * (unitRatio u ^ 14)⁻¹ := by group
        _ = 1 := by rw [h8, unitRatio_pow_fourteen]; simp
    have h7 : unitRatio u ^ 7 = unitRatio u := by
      calc
        unitRatio u ^ 7 = (unitRatio u ^ 2) ^ 3 * unitRatio u := by group
        _ = unitRatio u := by rw [h2]; simp
    let η := Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom v * unitRatio u
    have hsq : u ^ 2 = η ^ 7 := by
      rw [unit_square_eq_norm_ratio, hv, map_pow, ← h7]
      exact (mul_pow _ _ 7).symm
    exact ⟨u * η⁻¹ ^ 3, (DkMath.Lib.Algebra.oddPower_root_of_square 3 hsq).symm⟩

/-- 七乗根を単元倍で取り替えても、障害の三成分を同時に保存する。 -/
theorem unitObstruction_mul_seventh (u t : Cˣ) :
    unitObstruction (u * t ^ 7) = unitObstruction u := by
  apply Prod.ext
  · change normCoordinates (u * t ^ 7) = normCoordinates u
    rw [normCoordinates_mul, normCoordinates_seventh, add_zero]
  · change phaseCharacter (u * t ^ 7) = phaseCharacter u
    rw [map_mul, phaseCharacter_seventh, mul_one]

/-- 同じ七乗剰余類なら、ノルム二成分と共役位相も同じ。
整数との合同を要求しない、任意の単元の比較である。 -/
theorem unitObstruction_eq_of_same_class (u v : Cˣ)
    (h : DkMath.Lib.Algebra.SameUnitPowerClass 7 u v) : unitObstruction u = unitObstruction v := by
  obtain ⟨t, rfl⟩ := h
  exact unitObstruction_mul_seventh v t

/-- 三成分は単元七乗剰余類を完全に識別する。群の商の全射分類は主張しない。 -/
theorem same_class_iff_unitObstruction_eq (u v : Cˣ) :
    DkMath.Lib.Algebra.SameUnitPowerClass 7 u v ↔ unitObstruction u = unitObstruction v := by
  constructor
  · exact unitObstruction_eq_of_same_class u v
  · intro he
    have hn : normCoordinates u = normCoordinates v := congrArg Prod.fst he
    have hp : phaseCharacter u = phaseCharacter v := congrArg Prod.snd he
    have hinv : normCoordinates v⁻¹ = -normCoordinates v := by
      have hh := normCoordinates_mul v v⁻¹
      have hz : normCoordinates (1 : Cˣ) = 0 := by simp [normCoordinates]
      rw [mul_inv_cancel, hz] at hh
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh.symm)
    have hzero : normCoordinates (u * v⁻¹) = 0 ∧ phaseCharacter (u * v⁻¹) = 1 := by
      constructor
      · rw [normCoordinates_mul, hinv, hn, add_neg_cancel]
      · rw [map_mul, map_inv, hp, mul_inv_cancel]
    obtain ⟨k, hk⟩ := (unit_seventh_iff_obstruction (u * v⁻¹)).mpr hzero
    refine ⟨k, ?_⟩
    have hu : u = k ^ 7 * v := (mul_inv_eq_iff_eq_mul).mp hk
    simpa only [mul_comm] using hu

end

end DkMath.FLT.Kummer.SevenRealGN
