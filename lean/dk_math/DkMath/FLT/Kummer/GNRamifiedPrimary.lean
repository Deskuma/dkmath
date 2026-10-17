/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedQuadratic
import DkMath.Lib.NumberTheory.CosmicRamifiedPrimaryUnit

#print "file: DkMath.FLT.Kummer.GNRamifiedPrimary"

/-!
# GN から Kummer 単元補題の入力へ

保存パケットの整数深度から、εᵢ≡b*Sᵢ mod λ^p を得る。
幾何和 Sᵢ を単元群で除いた δᵢ は、整数 b と mod λ^p および mod p で合同。
ここまでの合同条件は DkMath 内で証明し、一般の Kummer 単元補題は使わない。
-/

namespace DkMath.FLT.Kummer

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory

/-- 原始的 FLT 方程式から、単元補題に渡せる単元 δᵢ を持つパケットを構成。
同じ Q の εᵢ と生成元を保ち、幾何和による既知の単元だけを取り出す。
λ^p 合同・整数 b との mod p 合同・δᵢ を使う厳密な因子表示を同時に返す。 -/
theorem exists_GN_ramified_primary_packet
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ (a + b) (-b) c,
      ∀ (i : ℕ) (hi : i ∈ (Finset.range p).erase 0),
        ramifiedReduction hζ hodd (Q.generator i) = 1 ∧
        (hζ.toInteger - 1) ^ p ∣ Q.unitFactor i -
          (∑ k ∈ Finset.range i, hζ.toInteger ^ k) * (b : 𝓞 K) ∧
        (hζ.toInteger - 1) ^ p ∣ (Q.primaryUnit hi : 𝓞 K) - (b : 𝓞 K) ∧
        (p : 𝓞 K) ∣ (Q.primaryUnit hi : 𝓞 K) - (b : 𝓞 K) ∧
        (a : 𝓞 K) + hζ.toInteger ^ i * (b : 𝓞 K) =
          (hζ.toInteger ^ i - 1) * ((Q.primaryUnit hi : 𝓞 K) * Q.generator i ^ p) := by
  obtain ⟨P⟩ := nonempty_GN_ramified_packet_of_flt_equation hζ hodd hp3 hc0 heq hprim hcase
  obtain ⟨Q, _, hred⟩ := P.exists_residue_normalized_principal_extension hodd hreg
  refine ⟨Q, fun i hi => ⟨(hred i hi).1, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using
      Q.unit_geom_sum_dvd_pow_prime hodd hi (hred i hi).1
  · simpa only [Int.cast_neg, sub_eq_add_neg] using
      Q.primaryUnit_add_parameter_dvd_pow_prime hodd hi (hred i hi).1
  · simpa only [neg_neg] using Q.primaryUnit_congruent_integer hodd hi (hred i hi).1
  · have h := (Q.primaryUnit_spec hodd hi (hred i hi).1).2.2
    convert h using 1
    push_cast
    ring

end DkMath.FLT.Kummer
