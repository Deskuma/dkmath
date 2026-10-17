/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamified
import DkMath.Lib.NumberTheory.CosmicRamifiedPacket
import DkMath.NumberTheory.GNRamifiedRoot

#print "file: DkMath.FLT.Kummer.GNRamifiedArithmetic"

/-!
# 分岐側 GN の整数深度とノルム復元

p∣c の向きの原始的 FLT 方程式を入力し、x=a+b, u=−b に固定する。
正則性なしの指数配分 `v_p(a+b)+1=p*v_p(c)` と、正則性を使う
`GN_p(a+b,−b)=p*t^p` を別々に公開する。

`RamifiedIdealPowerPacket` は実際に構成され、正則性による拡張も同じ
イデアル根を保持する。これらの必要条件は、新しい解や無限降下を構成しない。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField
open DkMath.CosmicFormula DkMath.Lib.NumberTheory

/-- 原始的な分岐側 FLT 方程式の整数付値配分。円分体も正則性も不要。
p∣(a+b), p∤(−b) を導き、GN の先頭項による exact-one 定理を適用する。 -/
theorem padicValInt_gap_add_one_of_ramified_case
    {p : ℕ} [hp : Fact p.Prime] (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c) :
    padicValInt p (a + b) + 1 = p * padicValInt p c := by
  have hxu : IsCoprime (a + b) (-b) := by
    simpa using (hprim.add_mul_left_left 1).neg_right
  have hx := prime_dvd_gap_of_dvd_right_of_flt_equation heq hcase
  have hu : ¬ (p : ℤ) ∣ -b := fun h =>
    (Nat.prime_iff_prime_int.mp hp.out).not_isUnit (hxu.isUnit_of_dvd' hx h)
  exact padicValInt_gap_add_one_eq_prime_mul hp3 hx hu hc0
    ((signed_GN_identity hodd a b).trans heq)

/-- 教科書の表示 `v_p(a+b)=p*v_p(c)-1`。
前定理の +1 形式が自然数の切り捨て減算を避けた一次的な保存等式である。 -/
theorem padicValInt_gap_of_ramified_case
    {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c) :
    padicValInt p (a + b) = p * padicValInt p c - 1 := by
  have h := padicValInt_gap_add_one_of_ramified_case hodd hp3 hc0 heq hprim hcase
  omega

/-- FLT の整数方程式から、剥離商・イデアル根・GN の積・付値を同時に構成。
正則性なし。パケットは単なる条件付き降下のインターフェイスではない。 -/
theorem nonempty_GN_ramified_packet_of_flt_equation
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c) :
    Nonempty (RamifiedIdealPowerPacket hζ (a + b) (-b) c) := by
  have hxu : IsCoprime (a + b) (-b) := by
    simpa using (hprim.add_mul_left_left 1).neg_right
  exact nonempty_ramifiedIdealPowerPacket hζ hp3 hxu
    (prime_dvd_gap_of_dvd_right_of_flt_equation heq hcase) hc0
    ((signed_GN_identity hodd a b).trans heq)

/-- 正則性を加えた分岐側の整数冪復元 `GN=p*t^p`。
整数根は p 非可除で、例外因子 a+b を含む積等式も同時に返す。
単元合同解析による円分整数環内の単元除去や、厳密な降下は結論しない。 -/
theorem exists_GN_eq_prime_mul_pow_of_ramified_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ t : ℤ, GN p (a + b) (-b) = (p : ℤ) * t ^ p ∧ ¬ (p : ℤ) ∣ t ∧
      (a + b) * ((p : ℤ) * t ^ p) = c ^ p := by
  obtain ⟨P⟩ := nonempty_GN_ramified_packet_of_flt_equation hζ hodd hp3 hc0 heq hprim hcase
  obtain ⟨Q, _⟩ := P.exists_principal_extension hreg
  exact Q.exists_integral_root hodd

/-- 基底パケットの座標に対して `GN=p*t^p` を満たす任意の整数根は 1 mod p。
正則性や選ばれた主イデアル化には依存せず、同じ座標の整数合同式から得る。 -/
theorem ramified_packet_integral_root_modEq_one
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c t : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c)
    (ht : GTail p 1 x u = (p : ℤ) * t ^ p) :
    t ≡ 1 [ZMOD (p : ℤ)] :=
  DkMath.NumberTheory.ramified_integral_root_modEq_one hp.out P.prime_ge_three
    P.gap_divisible P.parameter_not_divisible ht

/-- 分岐側の整数冪復元を、根の剰余類 `t≡1 mod p` まで強化する。
元の根・非可除性・例外因子を含む積等式を保ったまま合同条件を追加する。
整数ノルムの根の条件であり、円分整数環内の単元合同解析とは区別する。 -/
theorem exists_GN_eq_prime_mul_pow_modEq_one_of_ramified_case
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ t : ℤ, GN p (a + b) (-b) = (p : ℤ) * t ^ p ∧ t ≡ 1 [ZMOD (p : ℤ)] ∧
      ¬ (p : ℤ) ∣ t ∧ (a + b) * ((p : ℤ) * t ^ p) = c ^ p := by
  obtain ⟨P⟩ := nonempty_GN_ramified_packet_of_flt_equation hζ hodd hp3 hc0 heq hprim hcase
  obtain ⟨Q, _⟩ := P.exists_principal_extension hreg
  obtain ⟨t, ht, hnot, hprod⟩ := Q.exists_integral_root hodd
  exact ⟨t, ht, ramified_packet_integral_root_modEq_one Q.toRamifiedIdealPowerPacket ht,
    hnot, hprod⟩

end DkMath.FLT.Kummer
