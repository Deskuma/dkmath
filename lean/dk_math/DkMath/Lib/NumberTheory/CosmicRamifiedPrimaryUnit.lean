/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedPrimePower

#print "file: DkMath.Lib.NumberTheory.CosmicRamifiedPrimaryUnit"

/-!
# 幾何和の単元を除き、整数と mod p で合同な単元を取り出す

Sᵢ=1+ζ+...+ζ^(i−1) は 1≤i<p で大域的な単元。
δᵢ=εᵢ*Sᵢ⁻¹ を **単元群内** で定義し、
δᵢ≡−u mod λ^p、従って δᵢ≡−u mod p を証明する。
FLT 座標 u=−b では、これは Kummer の単元補題の入力 δᵢ≡b mod p になる。
ここではその補題自体や δᵢ の p 乗性は仮定も証明もしない。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField

/-- 非自明添字の幾何和 Sᵢ を、実際の単元群の元として選ぶ。
以降の逆元は円分整数環の除算ではなく、この単元群の逆元である。 -/
noncomputable def ramifiedGeomUnit
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {i : ℕ} (hi : i ∈ (Finset.range p).erase 0) :
    (𝓞 K)ˣ := by
  have hi0 := (Finset.mem_erase.mp hi).1
  have hilt := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
  have hc : i.Coprime p :=
    (hp.out.coprime_iff_not_dvd.mpr (fun h =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega))).symm
  exact (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit hp.out.two_le hc).unit

/-- 選んだ円分単元の値は、元の幾何和に厳密に一致する。 -/
theorem ramifiedGeomUnit_val
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {i : ℕ} (hi : i ∈ (Finset.range p).erase 0) :
    (ramifiedGeomUnit hζ hi : 𝓞 K) = ∑ k ∈ Finset.range i, hζ.toInteger ^ k := by
  unfold ramifiedGeomUnit
  exact IsUnit.unit_spec _

/-- 解析対象の単元 δᵢ=εᵢ*Sᵢ⁻¹。元の εᵢ や幾何和を p 乗と仮定しない。 -/
noncomputable def RamifiedPrincipalPowerPacket.primaryUnit
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) : (𝓞 K)ˣ :=
  (Q.principal i hi).1.unit * (ramifiedGeomUnit hζ hi)⁻¹

/-- δᵢ と Sᵢ の積が元の単元 εᵢ を復元する。単元群の逆元で厳密に取り消す。 -/
theorem RamifiedPrincipalPowerPacket.primaryUnit_mul_geom_sum
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0) :
    (Q.primaryUnit hi : 𝓞 K) * (∑ k ∈ Finset.range i, hζ.toInteger ^ k) = Q.unitFactor i := by
  rw [← ramifiedGeomUnit_val hζ hi]
  simp only [primaryUnit, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  exact (Q.principal i hi).1.unit_spec

/-- εᵢ≡−Sᵢ*u mod λ^p を単元 Sᵢ で割り、δᵢ≡−u mod λ^p を得る。
単元群の元として構成したので、δᵢ の単元性は存在条件ではなく型に含まれる。 -/
theorem RamifiedPrincipalPowerPacket.primaryUnit_add_parameter_dvd_pow_prime
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ p ∣ (Q.primaryUnit hi : 𝓞 K) + (u : 𝓞 K) := by
  let e := ramifiedGeomUnit hζ hi
  let S := ∑ k ∈ Finset.range i, hζ.toInteger ^ k
  have hS : S * (↑(e⁻¹) : 𝓞 K) = 1 := by
    dsimp only [S]
    rw [← ramifiedGeomUnit_val hζ hi]
    exact Units.mul_inv e
  have hd := dvd_mul_of_dvd_left (Q.unit_geom_sum_dvd_pow_prime hodd hi hγ) (↑(e⁻¹) : 𝓞 K)
  rw [← Q.primaryUnit_mul_geom_sum hi] at hd
  have heq : ((Q.primaryUnit hi : 𝓞 K) * S + S * (u : 𝓞 K)) * (↑(e⁻¹) : 𝓞 K) =
      (Q.primaryUnit hi : 𝓞 K) + (u : 𝓞 K) := by
    calc
      _ = ((Q.primaryUnit hi : 𝓞 K) + (u : 𝓞 K)) * (S * (↑(e⁻¹) : 𝓞 K)) := by ring
      _ = _ := by rw [hS, mul_one]
  exact heq ▸ hd

/-- Kummer 単元補題に渡す正確な合同条件。整数 −u を明示し、mod λ^p から mod p へ下ろす。 -/
theorem RamifiedPrincipalPowerPacket.primaryUnit_congruent_integer
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (p : 𝓞 K) ∣ (Q.primaryUnit hi : 𝓞 K) - ((-u : ℤ) : 𝓞 K) := by
  have hpRam : (p : 𝓞 K) ∣ (hζ.toInteger - 1) ^ p :=
    (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ).dvd'.trans
      (pow_dvd_pow (hζ.toInteger - 1) (by omega : p - 1 ≤ p))
  simpa only [Int.cast_neg, sub_neg_eq_add] using
    hpRam.trans (Q.primaryUnit_add_parameter_dvd_pow_prime hodd hi hγ)

/-- 正規化済みパケットを、幾何和で除いた単元群の族に束ねる。
単元の p 乗性を前提にせず、λ^p 合同・整数合同・元の因子表示を同時に返す。 -/
theorem RamifiedPrincipalPowerPacket.primaryUnit_spec
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) {i : ℕ}
    (hi : i ∈ (Finset.range p).erase 0)
    (hγ : ramifiedReduction hζ hodd (Q.generator i) = 1) :
    (hζ.toInteger - 1) ^ p ∣ (Q.primaryUnit hi : 𝓞 K) + (u : 𝓞 K) ∧
    (p : 𝓞 K) ∣ (Q.primaryUnit hi : 𝓞 K) - ((-u : ℤ) : 𝓞 K) ∧
    (x : 𝓞 K) + (1 - hζ.toInteger ^ i) * (u : 𝓞 K) =
      (hζ.toInteger ^ i - 1) * ((Q.primaryUnit hi : 𝓞 K) * Q.generator i ^ p) := by
  refine ⟨Q.primaryUnit_add_parameter_dvd_pow_prime hodd hi hγ,
    Q.primaryUnit_congruent_integer hodd hi hγ, ?_⟩
  rw [(Q.factor i hi).1, (Q.principal i hi).2.2, ← Q.primaryUnit_mul_geom_sum hi]
  have hgeom := mul_geom_sum hζ.toInteger i
  calc
    _ = ((hζ.toInteger - 1) * ∑ k ∈ Finset.range i, hζ.toInteger ^ k) *
        ((Q.primaryUnit hi : 𝓞 K) * Q.generator i ^ p) := by ring
    _ = _ := by rw [hgeom]

end DkMath.Lib.NumberTheory
