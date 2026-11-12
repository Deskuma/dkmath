/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealGaloisTransport
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Norm.Transitivity

#print "file: DkMath.Lib.NumberTheory.GaloisIdealNorm"

/-!
# IRR-008: イデアルの全共役積は整数ノルムの主イデアル

有限ガロア数体 K/ℚ に対し、∏σ σ(I)=(N(I)) を実際のイデアルとして証明する。
まず各 x∈I の元ノルム ∏σ σ(x) が共役イデアル積に入るので、相対ノルムを
拡張したイデアルが共役積に含まれる。次に両辺の絶対ノルムが N(I)^[K:ℚ] で
一致することから等式を得る。この方法は分岐素数も含み、非分岐性を仮定しない。
最後に類群へ写すと全共役積が1になる。各類が1になるという結論ではない。
-/

namespace DkMath.Lib.NumberTheory.GaloisIdealNorm
open scoped NumberField nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- 体の真のガロア自己同型を整数環へ制限する。 -/
noncomputable def integerAut (σ : K ≃ₐ[ℚ] K) : 𝓞 K ≃+* 𝓞 K :=
  NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv

/-- 元ノルムと整数環の全共役積の一致。イデアルノルムとの接続の生成元となる。 -/
theorem intNorm_eq_prod (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.intNorm ℤ (𝓞 K) x) =
      ∏ σ : K ≃ₐ[ℚ] K, integerAut σ x := by
  apply IsFractionRing.injective (𝓞 K) K
  rw [map_prod, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
    IsScalarTower.algebraMap_apply ℤ ℚ K, Algebra.algebraMap_intNorm (K := ℚ) (L := K)]
  change algebraMap ℚ K (Algebra.norm ℚ (x : K)) = ∏ σ : K ≃ₐ[ℚ] K, σ (x : K)
  exact Algebra.norm_eq_prod_automorphisms ℚ (x : K)

omit [IsGalois ℚ K] in
/-- 同型によるイデアルの輸送は絶対ノルムを変えない。 -/
theorem absNorm_map (e : 𝓞 K ≃+* 𝓞 K) (I : Ideal (𝓞 K)) :
    (I.map e).absNorm = I.absNorm := by
  rw [← Ideal.absNorm_relNorm ℤ (𝓞 K) (I.map e), ← Ideal.absNorm_relNorm ℤ (𝓞 K) I]
  exact congrArg Ideal.absNorm (Ideal.relNorm_map_algEquiv e.toIntAlgEquiv I)

/-- イデアルノルムを拡張したものは全共役積に含まれる。元の所属を全共役へ運ぶ。 -/
theorem map_relNorm_le_prod (I : Ideal (𝓞 K)) :
    (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K)) ≤
      ∏ σ : K ≃ₐ[ℚ] K, I.map (integerAut σ) := by
  rw [Ideal.map_relNorm]
  apply Ideal.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [Function.comp_apply, intNorm_eq_prod]
  exact Ideal.prod_mem_prod (fun σ _ => Ideal.mem_map_of_mem (integerAut σ) hx)

omit [IsGalois ℚ K] in
/-- 同じ有限指数を持つ非零イデアルの包含は等式。差の因子のノルムが1になる。 -/
theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (hJ : J ≠ ⊥)
    (h : I ≤ J) (hn : I.absNorm = J.absNorm) : I = J := by
  obtain ⟨H, hH⟩ := Ideal.dvd_iff_le.mpr h
  have hnorm : J.absNorm * H.absNorm = J.absNorm * 1 := by
    rw [← map_mul, ← hH, hn, mul_one]
  have hHone : H.absNorm = 1 :=
    Nat.eq_of_mul_eq_mul_left ((Ideal.absNorm_eq_zero_iff.not).mpr hJ |> Nat.pos_of_ne_zero) hnorm
  rw [Ideal.absNorm_eq_one_iff] at hHone
  simpa [hHone] using hH

/-- 全共役イデアル積は絶対ノルムを生成元とする主イデアル。
非零性を残し、絶対ノルムの0デフォルトと有限指数の議論を分離する。 -/
theorem prod_map_eq_span_absNorm (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (∏ σ : K ≃ₐ[ℚ] K, I.map (integerAut σ)) =
      Ideal.span {(I.absNorm : 𝓞 K)} := by
  have hcard : Fintype.card (K ≃ₐ[ℚ] K) = Module.finrank ℤ (𝓞 K) := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact IsFractionRing.finrank_eq ℤ ℚ (𝓞 K) K
  have hnorm : (∏ σ : K ≃ₐ[ℚ] K, I.map (integerAut σ)).absNorm =
      I.absNorm ^ Module.finrank ℤ (𝓞 K) := by
    simp only [map_prod, absNorm_map, Finset.prod_const, Finset.card_univ, hcard]
  symm
  apply eq_of_le_of_absNorm_eq
  · exact Finset.prod_ne_zero_iff.mpr (fun σ _ =>
      (Ideal.map_eq_bot_iff_of_injective (integerAut σ).injective).not.mpr hI)
  · simpa only [Ideal.relNorm_int, Ideal.map_span, Set.image_singleton, map_intCast,
      Int.cast_natCast, map_natCast] using map_relNorm_le_prod I
  · rw [Ideal.absNorm_span_natCast, hnorm]

/-- 真のガロア作用による任意のイデアル類の全共役積は1。
非零整数イデアルの代表を選び、上の主イデアル等式を類群へ写す。 -/
theorem classGroup_prod_eq_one (w : ClassGroup (𝓞 K)) :
    ∏ σ : K ≃ₐ[ℚ] K, ClassGroup.mulEquiv (integerAut σ) w = 1 := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective w
  simp_rw [classGroup_map_mk0]
  rw [← map_prod]
  apply (ClassGroup.mk0_eq_one_iff _).mpr
  change (((∏ σ : K ≃ₐ[ℚ] K, mapNonzeroIdeal (integerAut σ) I) :
    (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).IsPrincipal
  rw [show (((∏ σ : K ≃ₐ[ℚ] K, mapNonzeroIdeal (integerAut σ) I) :
      (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      ∏ σ : K ≃ₐ[ℚ] K, (I : Ideal (𝓞 K)).map (integerAut σ) from
        map_prod (Submonoid.subtype _) _ _,
    prod_map_eq_span_absNorm _ (nonZeroDivisors.coe_ne_zero I)]
  infer_instance

end DkMath.Lib.NumberTheory.GaloisIdealNorm
