/-
Adapted for DkMath from leanprover-community/flt-regular, commit
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89, FltRegular/NumberTheory/KummersLemma/KummersLemma.lean.
Original and adapted material licensed under Apache-2.0; see LICENSE in this directory tree.
DkMath changes: isolated namespace, Lean 4.34 compatibility, and mathematical commentary.
-/

module

public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

import DkMath.Lib.NumberTheory.RegularKummer.Cyclotomic.MoreLemmas
import DkMath.Lib.NumberTheory.RegularKummer.Hilbert94
import DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.Field

/-!
# Kummer's lemma for regular primes

This file proves the unit form of Kummer's lemma for regular primes.
-/

@[expose] public section

namespace DkMath.Lib.NumberTheory.RegularKummer

/-!
一般奇正則素数の Kummer 単元補題。
整数と mod p で合同な単元 u に対し、まず u^(p−1) を λ^p を法として1に正規化する。
p乗根が存在しないと仮定すると次数pの不分岐巡回拡大を得るが、Hilbert 94 は p が類数を割ると結論する。
類数との互いに素性でこれを排除し、整性・単元性を回復して元の u の単元群内のp乗根を構成する。
完成済み FLT、State の不存在、一段降下はいずれもこの証明の入力にしない。
-/

#print "file: DkMath.Lib.NumberTheory.RegularKummer.KummersLemma.KummersLemma"


open Polynomial IsCyclotomicExtension.Rat
open scoped NumberField

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hp hreg

/-- 高い一次合同から、まず体内の p 乗根を得る。

根が存在しなければ、素数次数の二項式 `X^p-u` は既約となる。
原始 p 乗根を含むので、その根を添加した拡大は次数 p の巡回 Galois 拡大である。
`KummersLemma.isUnramified` が有限素点の不分岐性を与え、Hilbert 94 は p が
類数を割ることを強制する。ここで初めて正則性を使い、非存在の仮定を反駁する。
この結論の根はまだ体の元であり、単元群への復元は次の定理で行う。 -/
theorem exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one {u : (𝓞 K)ˣ}
    (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ p = u := by
  by_contra! hu
  have hirr := X_pow_sub_C_irreducible_of_prime hpri.out hu
  have := Fact.mk hirr
  let L := AdjoinRoot (X ^ p - C (u : K))
  have := isSplittingField_AdjoinRoot_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr
  have := isGalois_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional ℚ L := Module.Finite.trans K L
  have : NumberField L := ⟨⟩
  have hKL : Module.finrank K L = p :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := dvd_card_classGroup_of_unramified_isCyclic (hKL.symm ▸ hpri.out) (hKL.symm ▸ hp)
  rw [hKL, hpri.out.dvd_iff_not_coprime] at this
  exact this (by convert hreg)

/-- 整数と mod p で合同な単元を、単元群の p 乗へ戻す一般 Kummer 補題。

合同する整数が p の倍数なら u の単元性に反するので、有限体での Fermat 合同を
適用できる。これにより u^(p−1) は mod p で1に合同となる。整数ノルムの条件を
使ってさらに mod (ζ−1)^p へ強め、前定理の体内根を得る。
根の p 乗が整数環の単元であることから、根も整かつ単元と分かる。
最後に u をその根で割り、指数 p と p−1 の互いに素性を具体的な群計算で利用する。
単なるノルムの p 乗性から元そのものの p 乗性を結論しているわけではない。 -/
theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) :
    ∃ v, u = v ^ p := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (B := K)
    (Set.mem_singleton p) (NeZero.ne p)
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1) - 1 := by
      refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := Int.cast_dvd_cast (α := 𝓞 K) _ _ h
      simp only [Int.cast_natCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_isUnit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime _ hζ).dvd.trans h) u.isUnit))
      simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := Int.cast_dvd_cast (α := 𝓞 K) _ _ hn'
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    rw [hx]
    rw [sub_eq_iff_eq_add, add_comm] at hx
    have H : Algebra.norm ℤ (1 + p • x) = 1 := norm_add_one_smul_of_isUnit hpri.out
      hp x (by
        rw [nsmul_eq_mul, ← hx]
        exact Units.isUnit _)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ x
    simpa [ge_iff_le, Int.cast_one, sub_self, nsmul_eq_mul, Nat.cast_mul, PNat.pos,
      Nat.cast_pred, zero_sub, IsUnit.mul_iff, ne_eq, tsub_eq_zero_iff_le, not_le, dvd_neg,
      Units.isUnit, and_true, zero_add] using this
  obtain ⟨v, hv⟩ := exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one hp hreg hζ this
  have hv' : IsIntegral ℤ v :=
    IsIntegral.of_pow (NeZero.pos p) (hv ▸ NumberField.RingOfIntegers.isIntegral_coe _)
  set w : 𝓞 K := ⟨v, hv'⟩
  have : IsUnit w := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm]
    convert (u ^ (p - 1) : (𝓞 K)ˣ).isUnit
    ext
    exact hv
  have hv'' : this.unit ^ p = u ^ (p - 1) := by
    ext
    simpa using! hv
  use u / this.unit
  rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_one]

end DkMath.Lib.NumberTheory.RegularKummer
