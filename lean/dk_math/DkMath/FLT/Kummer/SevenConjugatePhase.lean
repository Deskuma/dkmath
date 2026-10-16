/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenPrimaryNormBridge
import DkMath.FLT.Kummer.GNKummerUnitAdapter
import Mathlib.NumberTheory.NumberField.CMField

/-!
# 七次一次単元の共役位相を固定する

整数冪基底で mod 7 の根付き単位を識別し、具体的二次共役を CM 共役と同定する。
CM 単元の共役比は有限位数であり、整数合同からその位相は1に固定される。
前章の相対ノルム七乗性と合わせ、同じ単元の七乗根を構成する。
-/

open scoped NumberField
open NumberField DkMath.FLT.Seven DkMath.Lib.NumberTheory

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- 抽象円分体で選ばれた原始七乗根。同型の向きと同じ根を使う。 -/
def septicRoot : CyclotomicField 7 ℚ :=
  IsCyclotomicExtension.zeta 7 ℚ (CyclotomicField 7 ℚ)

/-- 選んだ根は原始七乗根である。 -/
theorem septicRoot_spec : IsPrimitiveRoot septicRoot 7 :=
  IsCyclotomicExtension.zeta_spec 7 ℚ (CyclotomicField 7 ℚ)

/-- 既存の整数生成元と、原始根の整数環への持ち上げを同定する。 -/
theorem septicRoot_toInteger :
    septicRoot_spec.toInteger = SevenCyclotomicDegreeSixInt.cyclotomicIntegralGenerator := by
  apply RingOfIntegers.coe_injective
  exact SevenCyclotomicDegreeSixInt.cyclotomicIntegralGenerator_coe.symm

/-- 原始根を同型で運ぶと、具体的な向き付き生成元になる。 -/
theorem integralEquiv_septicRoot :
    integralEquiv septicRoot_spec.toInteger = SevenCyclotomicDegreeSixInt.zeta := by
  rw [septicRoot_toInteger, integralEquiv_generator]

/-- 七次円分整数環の六つの整数冪基底。 -/
def septicBasis : Module.Basis (Fin 6) ℤ (𝓞 (CyclotomicField 7 ℚ)) :=
  septicRoot_spec.integralPowerBasis.basis.reindex
    (finCongr (by norm_num [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime (by decide : Nat.Prime 7)]))

/-- 冪基底の元を計算する規則。 -/
@[simp] theorem septicBasis_apply (i : Fin 6) :
    septicBasis i = septicRoot_spec.toInteger ^ (i : ℕ) := by
  simp [septicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- 六つの整数係数を観測する線形同型。 -/
def septicCoordinates : 𝓞 (CyclotomicField 7 ℚ) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  septicBasis.equivFun

/-- 整数環の mod 7 可除性を、各整数係数の可除性へ移す。 -/
theorem septicCoordinates_dvd_seven {x : 𝓞 (CyclotomicField 7 ℚ)}
    (hx : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ x) (i : Fin 6) :
    (7 : ℤ) ∣ septicCoordinates x i := by
  obtain ⟨w, hw⟩ := hx
  have hw' : x = (7 : ℤ) • w := by simpa [Algebra.smul_def] using hw
  rw [hw', map_smul]
  exact ⟨septicCoordinates w i, rfl⟩

/-- 基底範囲にある根の冪の係数は Kronecker のデルタである。 -/
theorem septicCoordinates_root_pow (n i : Fin 6) :
    septicCoordinates (septicRoot_spec.toInteger ^ (n : ℕ)) i = if n = i then 1 else 0 := by
  rw [← septicBasis_apply n]
  exact septicBasis.equivFun_self n i

/-- 自然数の添字で同じ計算規則を使う。 -/
theorem septicCoordinates_pow (n : ℕ) (hn : n < 6) (i : Fin 6) :
    septicCoordinates (septicRoot_spec.toInteger ^ n) i = if n = (i : ℕ) then 1 else 0 := by
  simpa only [Fin.ext_iff, Fin.val_mk] using septicCoordinates_root_pow ⟨n, hn⟩ i

/-- 七次円分多項式の関係を整数環内で保持する。 -/
theorem septic_root_sum :
    septicRoot_spec.toInteger ^ 6 + septicRoot_spec.toInteger ^ 5 +
      septicRoot_spec.toInteger ^ 4 + septicRoot_spec.toInteger ^ 3 +
      septicRoot_spec.toInteger ^ 2 + septicRoot_spec.toInteger + 1 = 0 := by
  apply RingOfIntegers.coe_injective
  change septicRoot ^ 6 + septicRoot ^ 5 + septicRoot ^ 4 + septicRoot ^ 3 +
    septicRoot ^ 2 + septicRoot + 1 = 0
  have hf : Polynomial.cyclotomic 7 (CyclotomicField 7 ℚ) =
      Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 3 +
      Polynomial.X ^ 2 + Polynomial.X + 1 := by
    rw [Polynomial.cyclotomic_prime _ 7]
    simp [Finset.sum_range_succ]
    ring
  simpa [hf] using septicRoot_spec.isRoot_cyclotomic (by decide)

/-- 基底の外側の ζ⁶ は、六座標がすべて −1 になる。 -/
theorem septicCoordinates_root_six (i : Fin 6) :
    septicCoordinates (septicRoot_spec.toInteger ^ 6) i = -1 := by
  have hz : septicRoot_spec.toInteger ^ 6 = -septicRoot_spec.toInteger ^ 5 -
      septicRoot_spec.toInteger ^ 4 - septicRoot_spec.toInteger ^ 3 -
      septicRoot_spec.toInteger ^ 2 - septicRoot_spec.toInteger - 1 := by
    linear_combination septic_root_sum
  rw [hz]
  simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
  have h0 : septicCoordinates 1 i = if (0 : Fin 6) = i then 1 else 0 := by
    simpa using septicCoordinates_root_pow 0 i
  have h1 : septicCoordinates septicRoot_spec.toInteger i = if (1 : ℕ) = (i : ℕ) then 1 else 0 := by
    simpa only [pow_one] using septicCoordinates_pow 1 (by decide) i
  rw [septicCoordinates_pow 5 (by decide), septicCoordinates_pow 4 (by decide),
    septicCoordinates_pow 3 (by decide), septicCoordinates_pow 2 (by decide), h1, h0]
  fin_cases i <;> norm_num

/-- 根付き単位 ±ζʳ が 1 と mod 7 で合同なら位相は1。
λ 進付値を新たに仮定せず、整数冪基底の小さい係数を検査する。 -/
theorem septic_rootOfUnity_eq_one_of_congruent
    {x : 𝓞 (CyclotomicField 7 ℚ)}
    (hx : ∃ r < 7, x = septicRoot_spec.toInteger ^ r ∨ x = -septicRoot_spec.toInteger ^ r)
    (h7 : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ x - 1) : x = 1 := by
  obtain ⟨r, hr, hx⟩ := hx
  have h0 (i : Fin 6) : septicCoordinates 1 i = if (0 : Fin 6) = i then 1 else 0 := by
    simpa using septicCoordinates_root_pow 0 i
  have h1 (i : Fin 6) : septicCoordinates septicRoot_spec.toInteger i =
      if (1 : ℕ) = (i : ℕ) then 1 else 0 := by
    simpa only [pow_one] using septicCoordinates_pow 1 (by decide) i
  rcases hx with rfl | rfl
  all_goals
    interval_cases r <;> first
    | solve | simp
    | solve |
        have hc := septicCoordinates_dvd_seven h7 0
        simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply] at hc
        norm_num [septicCoordinates_pow, septicCoordinates_root_six, h0, h1] at hc
    | solve |
        have hc := septicCoordinates_dvd_seven h7 1
        simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply] at hc
        norm_num [septicCoordinates_pow, septicCoordinates_root_six, h0, h1] at hc

/-- 六次モデルの二次共役を、整数環の環自己同型として輸送する。 -/
def integralConj : 𝓞 (CyclotomicField 7 ℚ) ≃+* 𝓞 (CyclotomicField 7 ℚ) :=
  integralEquiv.trans (starRingAut.trans integralEquiv.symm)

/-- 同型が共役も運ぶことを元の等式で記録する。 -/
theorem integralEquiv_conj (x : 𝓞 (CyclotomicField 7 ℚ)) :
    integralEquiv (integralConj x) = star (integralEquiv x) := by
  simp [integralConj]

/-- 二次共役は、選んだ原始根をその六乗へ送る。 -/
theorem integralConj_root : integralConj septicRoot_spec.toInteger = septicRoot_spec.toInteger ^ 6 := by
  apply integralEquiv.injective
  rw [integralEquiv_conj, map_pow, integralEquiv_septicRoot]
  rw [← SevenCyclotomicDegreeSixInt.zetaInv_eq_pow_six]
  ext <;> simp [SevenCyclotomicDegreeSixInt.zeta, SevenCyclotomicDegreeSixInt.zetaInv]

/-- 具体的二次共役は、円分整数環上の CM 共役に等しい。
両写像が原始根を逆根へ送ることを確認し、整数冪基底で拡張する。 -/
theorem integralConj_eq_CM [IsCMField (CyclotomicField 7 ℚ)] :
    integralConj.toRingHom = (IsCMField.ringOfIntegersComplexConj (CyclotomicField 7 ℚ)).toRingHom := by
  have hz : (IsCMField.ringOfIntegersComplexConj (CyclotomicField 7 ℚ))
      septicRoot_spec.toInteger = septicRoot_spec.toInteger ^ 6 := by
    let η : (𝓞 (CyclotomicField 7 ℚ))ˣ :=
      (septicRoot_spec.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
    have hη : (η : 𝓞 (CyclotomicField 7 ℚ)) = septicRoot_spec.toInteger := IsUnit.unit_spec _
    have hp : η ^ 7 = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, hη] using
        septicRoot_spec.toInteger_isPrimitiveRoot.pow_eq_one
    let t : Units.torsion (CyclotomicField 7 ℚ) := ⟨η, (CommGroup.mem_torsion _).mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨7, by decide, hp⟩)⟩
    have hc := IsCMField.complexConj_torsion (CyclotomicField 7 ℚ) t
    apply RingOfIntegers.coe_injective
    change IsCMField.complexConj (CyclotomicField 7 ℚ) septicRoot = septicRoot ^ 6
    have hc' : IsCMField.complexConj (CyclotomicField 7 ℚ) septicRoot = septicRoot⁻¹ := by
      have htval : (algebraMap (𝓞 (CyclotomicField 7 ℚ)) (CyclotomicField 7 ℚ))
          (t.val : 𝓞 (CyclotomicField 7 ℚ)) = septicRoot := by
        change (algebraMap (𝓞 (CyclotomicField 7 ℚ)) (CyclotomicField 7 ℚ))
          (η : 𝓞 (CyclotomicField 7 ℚ)) = septicRoot
        rw [hη]
        rfl
      rw [htval] at hc
      exact hc
    rw [hc']
    symm
    calc
      septicRoot ^ 6 = septicRoot ^ 6 * (septicRoot * septicRoot⁻¹) := by
        rw [mul_inv_cancel₀ (septicRoot_spec.ne_zero (by decide)), mul_one]
      _ = septicRoot ^ 7 * septicRoot⁻¹ := by ring
      _ = septicRoot⁻¹ := by rw [septicRoot_spec.pow_eq_one, one_mul]
  have hh : integralConj.toRingHom.toIntAlgHom =
      (IsCMField.ringOfIntegersComplexConj (CyclotomicField 7 ℚ)).toRingHom.toIntAlgHom := by
    apply septicRoot_spec.integralPowerBasis.algHom_ext
    rw [septicRoot_spec.integralPowerBasis_gen]
    change integralConj septicRoot_spec.toInteger =
      IsCMField.ringOfIntegersComplexConj (CyclotomicField 7 ℚ) septicRoot_spec.toInteger
    rw [integralConj_root, hz]
  exact congrArg AlgHom.toRingHom hh

/-- 単元の共役比を単元群内で定義する。分母の逆元も整数環の単元である。 -/
def conjugateRatio (u : (𝓞 (CyclotomicField 7 ℚ))ˣ) : (𝓞 (CyclotomicField 7 ℚ))ˣ :=
  u * (Units.map integralConj.toMonoidHom u)⁻¹

/-- ノルムと共役比が元の平方を復元する恒等式。
ノルムは共役との積、比はその差としての位相を保持し、両者を掛けると平方になる。 -/
theorem unit_square_eq_norm_mul_ratio (u : (𝓞 (CyclotomicField 7 ℚ))ˣ) :
    integralEquiv (u : _) ^ 2 =
      SevenCyclotomicDegreeSixInt.ofReal (integralRelativeNorm (u : _)) *
        integralEquiv (conjugateRatio u : _) := by
  let v := Units.map integralConj.toMonoidHom u
  have hc : star (integralEquiv (u : _)) * integralEquiv (↑v⁻¹ : _) = 1 := by
    rw [← integralEquiv_conj]
    change integralEquiv (v : _) * integralEquiv (↑v⁻¹ : _) = 1
    have hv : (v : 𝓞 (CyclotomicField 7 ℚ)) * (↑v⁻¹ : 𝓞 (CyclotomicField 7 ℚ)) = 1 := v.val_inv
    rw [← map_mul, hv, map_one]
  change integralEquiv (u : _) ^ 2 =
    algebraMap SevenRealCubicInt SevenCyclotomicDegreeSixInt.Ring
      (QuadraticAlgebra.norm (integralEquiv (u : _))) *
      integralEquiv ((u : _) * (↑v⁻¹ : _))
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, map_mul]
  calc
    integralEquiv (u : _) ^ 2 = integralEquiv (u : _) ^ 2 *
        (star (integralEquiv (u : _)) * integralEquiv (↑v⁻¹ : _)) := by rw [hc, mul_one]
    _ = _ := by ring

/-- CM 単元定理の消費。共役比は根付き単位、すなわち有限位数である。 -/
theorem conjugateRatio_finite (u : (𝓞 (CyclotomicField 7 ℚ))ˣ) :
    IsOfFinOrder (conjugateRatio u) := by
  let : IsCMField (CyclotomicField 7 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField 7 ℚ) (S := {7}) ⟨7, by simp, by decide⟩
  have hs : Units.map integralConj.toMonoidHom u =
      IsCMField.unitsComplexConj (CyclotomicField 7 ℚ) u := by
    apply Units.ext
    exact RingHom.congr_fun integralConj_eq_CM (u : 𝓞 (CyclotomicField 7 ℚ))
  dsimp only [conjugateRatio]
  rw [hs]
  exact (CommGroup.mem_torsion _).mp
    (IsCMField.unitsMulComplexConjInv (CyclotomicField 7 ℚ) u).property

/-- 整数合同から共役比の合同へ。共役が整数を固定し、分母が単元であることを使う。 -/
theorem conjugateRatio_congruent_one (u : (𝓞 (CyclotomicField 7 ℚ))ˣ)
    (h : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (n : _)) :
    (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (conjugateRatio u : 𝓞 (CyclotomicField 7 ℚ)) - 1 := by
  obtain ⟨n, hn⟩ := h
  let v := Units.map integralConj.toMonoidHom u
  have hc : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ integralConj (u : _) - (n : _) := by
    have hm := map_dvd integralConj.toRingHom hn
    change integralConj (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ integralConj ((u : _) - (n : _)) at hm
    simpa only [map_ofNat, map_sub, map_intCast] using hm
  have hd : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (v : _) := by
    change (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - integralConj (u : _)
    convert dvd_sub hn hc using 1
    ring
  convert dvd_mul_of_dvd_left hd (↑v⁻¹ : 𝓞 (CyclotomicField 7 ℚ)) using 1
  dsimp only [conjugateRatio]
  simp only [Units.val_mul, sub_mul]
  exact congrArg ((u : 𝓞 (CyclotomicField 7 ℚ)) * (↑v⁻¹ : 𝓞 (CyclotomicField 7 ℚ)) - ·) v.val_inv.symm

/-- 一次単元の共役比の位相は1。有限位数の分類と六座標の合同識別を結合する。 -/
theorem conjugateRatio_eq_one (u : (𝓞 (CyclotomicField 7 ℚ))ˣ)
    (h : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (n : _)) :
    conjugateRatio u = 1 := by
  have hfiniteK : IsOfFinOrder ((conjugateRatio u : 𝓞 (CyclotomicField 7 ℚ)) : CyclotomicField 7 ℚ) :=
    ((algebraMap (𝓞 (CyclotomicField 7 ℚ)) (CyclotomicField 7 ℚ)).toMonoidHom.comp
      (Units.coeHom (𝓞 (CyclotomicField 7 ℚ)))).isOfFinOrder (conjugateRatio_finite u)
  obtain ⟨i, hi, hroot⟩ :=
    septicRoot_spec.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide) hfiniteK
  have hrootR : (conjugateRatio u : 𝓞 (CyclotomicField 7 ℚ)) = septicRoot_spec.toInteger ^ i ∨
      (conjugateRatio u : 𝓞 (CyclotomicField 7 ℚ)) = -septicRoot_spec.toInteger ^ i := by
    rcases hroot with h | h
    · exact Or.inl (RingOfIntegers.coe_injective h)
    · exact Or.inr (RingOfIntegers.coe_injective h)
  exact Units.ext (septic_rootOfUnity_eq_one_of_congruent ⟨i, hi, hrootR⟩
    (conjugateRatio_congruent_one u h))

/-- 整数と mod 7 で合同な単元は、具体的二次共役で固定される。 -/
theorem primary_unit_fixed (u : (𝓞 (CyclotomicField 7 ℚ))ˣ)
    (h : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (n : _)) :
    u = Units.map integralConj.toMonoidHom u :=
  mul_inv_eq_one.mp (conjugateRatio_eq_one u h)

end

end DkMath.FLT.Kummer.SevenPrimaryNorm
