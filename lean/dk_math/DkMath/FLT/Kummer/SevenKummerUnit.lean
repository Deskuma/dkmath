/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenConjugatePhase
import DkMath.Lib.Algebra.OddPowerRecovery

#print "file: DkMath.FLT.Kummer.SevenKummerUnit"

/-!
# 七次 Kummer 単元補題と同じ GN 因子の七乗復元

前章の実三次ノルム根と、この章の共役位相1を組み合わせる。
平方が七乗なので、明示的な群の恒等式で単元自身の七乗根を作る。
一般の単元補題や完成した FLT7 を仮定しない。
-/

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

open scoped NumberField
open NumberField DkMath.FLT.Seven DkMath.Lib.NumberTheory

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- 具体的六次環でも、一次単元は二次共役で固定される。
整数環へ逆輸送して位相を解析し、同じ元へ戻す。 -/
theorem concrete_primary_unit_fixed (u : SevenCyclotomicDegreeSixInt.Ringˣ)
    (h : ∃ n : ℤ, (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ (u : _) - (n : _)) :
    star (u : SevenCyclotomicDegreeSixInt.Ring) = (u : SevenCyclotomicDegreeSixInt.Ring) := by
  let v := Units.map integralEquiv.symm.toMonoidHom u
  have hv : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (v : _) - (n : _) := by
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have hm := map_dvd integralEquiv.symm.toRingHom hn
    change integralEquiv.symm (7 : SevenCyclotomicDegreeSixInt.Ring) ∣
      integralEquiv.symm ((u : _) - (n : _)) at hm
    change (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ integralEquiv.symm (u : _) - (n : _)
    simpa only [map_ofNat, map_sub, map_intCast] using hm
  have hf := congrArg (fun w : (𝓞 (CyclotomicField 7 ℚ))ˣ => integralEquiv (w : _))
    (primary_unit_fixed v hv)
  change integralEquiv (v : _) = integralEquiv (integralConj (v : _)) at hf
  rw [integralEquiv_conj] at hf
  change integralEquiv (integralEquiv.symm (u : _)) =
    star (integralEquiv (integralEquiv.symm (u : _))) at hf
  simpa only [RingEquiv.apply_symm_apply] using hf.symm

/-- 具体的六次環上の七次単元補題。整数合同だけを仮定し、七乗根を実際に構成する。 -/
theorem concrete_kummer_unit_power_criterion :
    KummerUnitPowerCriterion SevenCyclotomicDegreeSixInt.Ring 7 := by
  intro u h
  obtain ⟨v, hv⟩ := primary_unit_mul_conjugate u h
  let η := Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom v
  have hsq : u ^ 2 = η ^ 7 := by
    apply Units.ext
    rw [concrete_primary_unit_fixed u h] at hv
    change (u : SevenCyclotomicDegreeSixInt.Ring) ^ 2 =
      SevenCyclotomicDegreeSixInt.ofReal (v : SevenRealCubicInt) ^ 7
    simpa only [pow_two] using hv
  exact ⟨u * η⁻¹ ^ 3, (DkMath.Lib.Algebra.oddPower_root_of_square 3 hsq).symm⟩

/-- 円分整数環上の七次 Kummer 単元補題の実供給。
型は `KummerUnitPowerCriterion` そのもので、criterion を入力に要求しない。 -/
theorem septic_kummer_unit_power_criterion :
    KummerUnitPowerCriterion (𝓞 (CyclotomicField 7 ℚ)) 7 := by
  intro u h
  have hc : ∃ n : ℤ, (7 : SevenCyclotomicDegreeSixInt.Ring) ∣
      (Units.map integralEquiv.toMonoidHom u : SevenCyclotomicDegreeSixInt.Ring) - (n : _) := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, integralEquiv_congruent_integer hn⟩
  obtain ⟨v, hv⟩ := concrete_kummer_unit_power_criterion (Units.map integralEquiv.toMonoidHom u) hc
  refine ⟨Units.map integralEquiv.symm.toMonoidHom v, ?_⟩
  apply Units.ext
  apply integralEquiv.injective
  change integralEquiv (u : _) = integralEquiv (integralEquiv.symm (v : _) ^ 7)
  rw [map_pow, RingEquiv.apply_symm_apply]
  exact congrArg Units.val hv

/-- 正規化済みの同じ GN 一次単元 δᵢ の七乗根。ノルム値だけでなく元の等式を返す。 -/
theorem GN_primary_unit_seventh
    {ζ : CyclotomicField 7 ℚ} {hζ : IsPrimitiveRoot ζ 7} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction hζ (by decide : Odd 7) (Q.generator i) = 1) :
    ∃ κ : (𝓞 (CyclotomicField 7 ℚ))ˣ, Q.primaryUnit hi = κ ^ 7 :=
  septic_kummer_unit_power_criterion (Q.primaryUnit hi)
    ⟨-u, Q.primaryUnit_congruent_integer (by decide : Odd 7) hi hγ⟩

/-- 同じパケットの因子を、未解析単元を残さない形へ戻す。
根は既存の生成元と一次単元の根との積。降下パケットの構成は別段階である。 -/
theorem GN_factor_eq_zeta_sub_one_mul_seventh
    {ζ : CyclotomicField 7 ℚ} {hζ : IsPrimitiveRoot ζ 7} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction hζ (by decide : Odd 7) (Q.generator i) = 1) :
    ∃ θ : 𝓞 (CyclotomicField 7 ℚ), (x : _) + (1 - hζ.toInteger ^ i) * (u : _) =
      (hζ.toInteger ^ i - 1) * θ ^ 7 :=
  factor_eq_zeta_sub_one_mul_pow_of_unit_criterion Q (by decide : Odd 7)
    septic_kummer_unit_power_criterion hi hγ

/-- 七次の既存 PID 定理により、類数は1。類数条件を未証明の仮定として残さない。 -/
theorem septic_classGroup_card_eq_one :
    Fintype.card (ClassGroup (𝓞 (CyclotomicField 7 ℚ))) = 1 := by
  let : IsPrincipalIdealRing (𝓞 (CyclotomicField 7 ℚ)) :=
    CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing (CyclotomicField 7 ℚ)
  simpa only [Fintype.card_eq_nat_card] using card_classGroup_eq_one (R := 𝓞 (CyclotomicField 7 ℚ))

/-- 原始 FLT7 方程式の分岐側から、単元を除いた因子表示を得る。
正則性・単元補題の追加引数はない。新しい解・厳密降下・矛盾は結論しない。 -/
theorem exists_GN_septic_factor_eq_zeta_sub_one_mul_seventh
    {ζ : CyclotomicField 7 ℚ} (hζ : IsPrimitiveRoot ζ 7)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ 7 + b ^ 7 = c ^ 7)
    (hprim : IsCoprime a b) (hcase : (7 : ℤ) ∣ c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) :
    ∃ θ : 𝓞 (CyclotomicField 7 ℚ), (a : _) + hζ.toInteger ^ i * (b : _) =
      (hζ.toInteger ^ i - 1) * θ ^ 7 := by
  have hreg : Nat.Coprime 7 (Fintype.card (ClassGroup (𝓞 (CyclotomicField 7 ℚ)))) := by
    rw [septic_classGroup_card_eq_one]
    exact Nat.coprime_one_right 7
  exact exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion hζ (by decide) (by decide)
    hc0 heq hprim hcase hreg septic_kummer_unit_power_criterion hi

end

end DkMath.FLT.Kummer.SevenPrimaryNorm
