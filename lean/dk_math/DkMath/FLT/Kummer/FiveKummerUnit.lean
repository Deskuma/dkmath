/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGoldenRelativeNorm
import DkMath.FLT.Kummer.GNKummerUnitAdapter
import DkMath.FLT.Five.SignedGoldenZeroSectorDescent
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# 五次の Kummer 単元補題

単元 u の `u/conj(u)` は CM 体の根付き単位となる。mod 5 の整数合同は
その位相を1に固定する。相対ノルムは黄金比単元で、同じ合同条件から五乗。
従って u² が五乗となり、2 と5の互いに素性で u 自身の五乗根を作る。
黄金比単元の分類は既存の一般的な単元定理を再利用する。FLT5 の不可能性や
既存パケットの五乗抽出は入力にしない。
-/

open scoped NumberField
open NumberField

namespace DkMath.FLT.Kummer

open DkMath.FLT.Five DkMath.Lib.NumberTheory

/-- 既存の座標単元の定義と Mathlib の `IsUnit` をつなぐ。 -/
theorem goldenUnit_of_isUnit {x : GoldenInt} (hx : IsUnit x) : GoldenUnit x := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨↑u⁻¹, u.val_inv, u.inv_val⟩

/-- 黄金比単元が整数と mod 5 で合同なら五乗である。
一般単元の五剰余類を使うが、FLT 反例に由来するセクター排除は使わない。 -/
theorem golden_unit_fifth_of_integer_congruence {x : GoldenInt}
    (hx : IsUnit x) (hcong : ∃ n : ℤ, (5 : GoldenInt) ∣ x - (n : GoldenInt)) :
    ∃ y : GoldenInt, IsUnit y ∧ x = y ^ 5 := by
  obtain ⟨i, y, hy⟩ := goldenUnitClassesModFifth x (goldenUnit_of_isUnit hx)
  have hxy : IsUnit ((goldenPhi ^ (i : ℕ)) * y ^ 5) := by
    change IsUnit (goldenMul (goldenPow goldenPhi i.val) (goldenPow y 5))
    rw [← hy]
    exact hx
  have hyunit : IsUnit y := (isUnit_pow_iff (by decide : 5 ≠ 0)).mp (isUnit_of_mul_isUnit_right hxy)
  have h5snd : (5 : ℤ) ∣ x.snd := by
    obtain ⟨n, w, hw⟩ := hcong
    refine ⟨w.snd, ?_⟩
    have hs := congrArg GoldenInt.snd hw
    change x.snd - (goldenOfInt n).snd =
      (goldenMul (⟨5, 0⟩ : GoldenInt) w).snd at hs
    simp only [goldenOfInt, goldenMul, zero_mul, add_zero, sub_zero] at hs
    simpa using hs
  by_cases hi : i = 0
  · refine ⟨y, hyunit, ?_⟩
    simpa [hi] using hy
  · have h5 := five_dvd_norm_of_nonzero_goldenUnitSector hi hy h5snd
    rcases goldenNorm_eq_one_or_neg_one_of_unit (goldenUnit_of_isUnit hyunit) with hn | hn
    all_goals rw [hn] at h5; norm_num at h5

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] {ζ : K}

/-- mod 5 の可除性を四つの整数冪基底の座標へ射影する。 -/
theorem quinticCoordinates_dvd_five (hζ : IsPrimitiveRoot ζ 5) {x : 𝓞 K}
    (hx : (5 : 𝓞 K) ∣ x) (i : Fin 4) : (5 : ℤ) ∣ quinticCoordinates hζ x i := by
  obtain ⟨w, hw⟩ := hx
  have hw' : x = (5 : ℤ) • w := by simpa [Algebra.smul_def] using hw
  rw [hw', map_smul]
  exact ⟨quinticCoordinates hζ w i, rfl⟩

/-- 冪基底での根の座標を計算する。 -/
theorem quinticCoordinates_root_pow (hζ : IsPrimitiveRoot ζ 5) (n i : Fin 4) :
    quinticCoordinates hζ (hζ.toInteger ^ (n : ℕ)) i = if n = i then 1 else 0 := by
  rw [← quinticBasis_apply hζ n]
  exact (quinticBasis hζ).equivFun_self n i

/-- 自然数添字で使う冪基底の座標計算規則。 -/
theorem quinticCoordinates_pow (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (hn : n < 4) (i : Fin 4) :
    quinticCoordinates hζ (hζ.toInteger ^ n) i = if n = (i : ℕ) then 1 else 0 := by
  simpa only [Fin.ext_iff, Fin.val_mk] using quinticCoordinates_root_pow hζ ⟨n, hn⟩ i

/-- 四つの基底を超える ζ⁴ の座標は全て −1。 -/
theorem quinticCoordinates_root_four (hζ : IsPrimitiveRoot ζ 5) (i : Fin 4) :
    quinticCoordinates hζ (hζ.toInteger ^ 4) i = -1 := by
  have hz : hζ.toInteger ^ 4 = -hζ.toInteger ^ 3 - hζ.toInteger ^ 2 - hζ.toInteger - 1 := by
    linear_combination quintic_root_sum hζ
  rw [hz]
  have hc (n : Fin 4) := quinticCoordinates_root_pow hζ n i
  simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
  have h0 : quinticCoordinates hζ 1 i = if (0 : Fin 4) = i then 1 else 0 := by
    simpa using hc 0
  have h1 : quinticCoordinates hζ hζ.toInteger i = if (1 : Fin 4) = i then 1 else 0 := by
    simpa using hc 1
  rw [quinticCoordinates_pow hζ 3 (by decide), quinticCoordinates_pow hζ 2 (by decide), h1, h0]
  fin_cases i <;> norm_num

/-- 根付き単位 ±ζ^r のうち、1 と mod 5 で合同なのは1だけ。
λ の付値を仮定せず、整数冪基底の係数 ±1,±2 を検査する。 -/
theorem quintic_rootOfUnity_eq_one_of_congruent (hζ : IsPrimitiveRoot ζ 5)
    {x : 𝓞 K} (hx : ∃ r < 5, x = hζ.toInteger ^ r ∨ x = -hζ.toInteger ^ r)
    (h5 : (5 : 𝓞 K) ∣ x - 1) : x = 1 := by
  obtain ⟨r, hr, hx⟩ := hx
  have h0 (i : Fin 4) : quinticCoordinates hζ 1 i = if (0 : Fin 4) = i then 1 else 0 := by
    simpa using quinticCoordinates_root_pow hζ 0 i
  have h1 (i : Fin 4) : quinticCoordinates hζ hζ.toInteger i = if (1 : ℕ) = (i : ℕ) then 1 else 0 := by
    simpa only [pow_one] using quinticCoordinates_pow hζ 1 (by decide) i
  rcases hx with rfl | rfl
  all_goals
    interval_cases r <;> first
    | solve | simp
    | solve |
        have hc := quinticCoordinates_dvd_five hζ h5 0
        simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply] at hc
        norm_num [quinticCoordinates_pow, quinticCoordinates_root_four, h0, h1] at hc
    | solve |
        have hc := quinticCoordinates_dvd_five hζ h5 1
        simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply] at hc
        norm_num [quinticCoordinates_pow, quinticCoordinates_root_four, h0, h1] at hc

/-- 構成した相対共役が CM 体の複素共役と一致することを、生成元で証明する。 -/
theorem quinticConj_eq_CM (hζ : IsPrimitiveRoot ζ 5) [IsCMField K] :
    (quinticConj hζ).toRingHom = (IsCMField.ringOfIntegersComplexConj K).toRingHom := by
  have hz : (IsCMField.ringOfIntegersComplexConj K) hζ.toInteger = hζ.toInteger ^ 4 := by
    let η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
    have hη : (η : 𝓞 K) = hζ.toInteger := IsUnit.unit_spec _
    have hp : η ^ 5 = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, hη] using hζ.toInteger_isPrimitiveRoot.pow_eq_one
    let t : Units.torsion K := ⟨η, (CommGroup.mem_torsion _).mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by decide, hp⟩)⟩
    have hc := IsCMField.complexConj_torsion K t
    apply RingOfIntegers.coe_injective
    change IsCMField.complexConj K ζ = ζ ^ 4
    have hc' : IsCMField.complexConj K ζ = ζ⁻¹ := by
      have htval : (algebraMap (𝓞 K) K) (t.val : 𝓞 K) = ζ := by
        change (algebraMap (𝓞 K) K) (η : 𝓞 K) = ζ
        rw [hη]
        rfl
      rw [htval] at hc
      exact hc
    rw [hc']
    symm
    calc
      ζ ^ 4 = ζ ^ 4 * (ζ * ζ⁻¹) := by rw [mul_inv_cancel₀ (hζ.ne_zero (by decide)), mul_one]
      _ = ζ ^ 5 * ζ⁻¹ := by ring
      _ = ζ⁻¹ := by rw [hζ.pow_eq_one, one_mul]
  have hh : (quinticConj hζ).toRingHom.toIntAlgHom =
      (IsCMField.ringOfIntegersComplexConj K).toRingHom.toIntAlgHom := by
    apply hζ.integralPowerBasis.algHom_ext
    rw [hζ.integralPowerBasis_gen]
    change quinticConj hζ hζ.toInteger = IsCMField.ringOfIntegersComplexConj K hζ.toInteger
    rw [quinticConj_root, hz]
  exact congrArg AlgHom.toRingHom hh

/-- 五次円分体では類数条件を既存の PID 定理から供給できる。 -/
theorem quintic_classGroup_card_eq_one : Fintype.card (ClassGroup (𝓞 K)) = 1 := by
  let : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  simpa only [Fintype.card_eq_nat_card] using card_classGroup_eq_one (R := 𝓞 K)

/-- 五次 Kummer 単元補題の実際の供給。外部の criterion や FLT5 を仮定しない。
相対ノルムの五乗性と、CM 共役比の位相1を結び、最後に平方から五乗根を復元する。 -/
theorem quintic_kummer_unit_power_criterion (hζ : IsPrimitiveRoot ζ 5) :
    KummerUnitPowerCriterion (𝓞 K) 5 := by
  let : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {5}) ⟨5, by simp, by decide⟩
  intro δ hcong
  obtain ⟨n, hn⟩ := hcong
  have hNunit : IsUnit (fiveGoldenRelativeNorm hζ (δ : 𝓞 K)) :=
    δ.isUnit.map (fiveGoldenRelativeNorm hζ)
  obtain ⟨v, hvunit, hv⟩ := golden_unit_fifth_of_integer_congruence hNunit
    ⟨n ^ 2, by simpa only [Int.cast_pow] using fiveGoldenRelativeNorm_congruent_integer hζ hn⟩
  let σδ : (𝓞 K)ˣ := IsCMField.unitsComplexConj K δ
  let r := δ * σδ⁻¹
  have hs : (σδ : 𝓞 K) = quinticConj hζ (δ : 𝓞 K) := by
    have hs := RingHom.congr_fun (quinticConj_eq_CM hζ) (δ : 𝓞 K)
    exact hs.symm
  have h5diff : (5 : 𝓞 K) ∣ (δ : 𝓞 K) - (σδ : 𝓞 K) := by
    have hc : (5 : 𝓞 K) ∣ quinticConj hζ (δ : 𝓞 K) - (n : 𝓞 K) := by
      convert map_dvd (quinticConj hζ).toRingHom hn using 1 <;> norm_num
      exact (map_ofNat (quinticConj hζ) 5).symm
    rw [hs]
    convert dvd_sub hn hc using 1
    ring
  have h5r : (5 : 𝓞 K) ∣ (r : 𝓞 K) - 1 := by
    convert dvd_mul_of_dvd_left h5diff (↑σδ⁻¹ : 𝓞 K) using 1
    dsimp only [r]
    simp only [Units.val_mul, sub_mul]
    have hc : (σδ : 𝓞 K) * (↑σδ⁻¹ : 𝓞 K) = 1 := by
      exact σδ.val_inv
    rw [hc]
  have hfiniteU : IsOfFinOrder r :=
    (CommGroup.mem_torsion _).mp (IsCMField.unitsMulComplexConjInv K δ).property
  have hfiniteK : IsOfFinOrder ((r : 𝓞 K) : K) :=
    ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).isOfFinOrder hfiniteU
  obtain ⟨i, hi, hroot⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide) hfiniteK
  have hrootR : (r : 𝓞 K) = hζ.toInteger ^ i ∨ (r : 𝓞 K) = -hζ.toInteger ^ i := by
    rcases hroot with h | h
    · exact Or.inl (RingOfIntegers.coe_injective h)
    · exact Or.inr (RingOfIntegers.coe_injective h)
  have hrR := quintic_rootOfUnity_eq_one_of_congruent hζ ⟨i, hi, hrootR⟩ h5r
  have hr : r = 1 := Units.ext hrR
  have hfixed : δ = σδ := mul_inv_eq_one.mp hr
  let η : (𝓞 K)ˣ := Units.map (fiveGoldenEmbedding hζ).toMonoidHom hvunit.unit
  have hη : (η : 𝓞 K) = fiveGoldenEmbedding hζ v := by
    exact congrArg (fiveGoldenEmbedding hζ) (IsUnit.unit_spec hvunit)
  have hsq : δ ^ 2 = η ^ 5 := by
    apply Units.ext
    have hN := fiveGoldenRelativeNorm_embedding hζ (δ : 𝓞 K)
    rw [hv, map_pow, ← hs, ← hfixed] at hN
    simpa only [Units.val_pow_eq_pow_val, Units.val_mul, hη, pow_two] using hN.symm
  refine ⟨δ * η⁻¹ ^ 2, ?_⟩
  symm
  calc
    (δ * η⁻¹ ^ 2) ^ 5 = δ ^ 5 * ((η ^ 5)⁻¹) ^ 2 := by simp only [mul_pow, inv_pow, ← pow_mul]
    _ = δ := by rw [← hsq]; group

end DkMath.FLT.Kummer
