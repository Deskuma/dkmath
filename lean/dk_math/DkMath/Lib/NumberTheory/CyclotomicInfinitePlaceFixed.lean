/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: retain DkMath SAME rootField, specified primitive root and characterEquiv;
handle inverse Galois action explicitly, without replacing the cyclotomic field.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

#print "file: DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed"

/-!
# 同じ円分指標による無限素点の固定点分類

指定された原始根と同じ rootField の既存 characterEquiv を保持する。
埋め込みの一致／複素共役の一致を分け、逆自己同型の指数 d⁻¹ を明示する。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed

open NumberField NumberField.InfinitePlace
open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
noncomputable section

variable {p : ℕ} [Fact p.Prime]
local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

lemma neg_one_inv' : (-1 : (ZMod p)ˣ)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by simp)

lemma pow_natCast_neg_one {z : ℂ} (hz : IsPrimitiveRoot z p)
    {n : ℕ} (hn : (n : ZMod p) = -1) : z ^ n = z⁻¹ := by
  have hd : p ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hn]
    ring
  obtain ⟨k, hk⟩ := hd
  have h1 : z ^ (n + 1) = 1 := by rw [hk, pow_mul, hz.pow_eq_one, one_pow]
  rw [pow_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

lemma natCast_eq_neg_one_of_pow {z : ℂ} (hz : IsPrimitiveRoot z p) (hz0 : z ≠ 0)
    {n : ℕ} (hpow : z ^ n = z⁻¹) : (n : ZMod p) = -1 := by
  have h1 : z ^ (n + 1) = 1 := by rw [pow_succ, hpow, inv_mul_cancel₀ hz0]
  have h2 := (hz.pow_eq_one_iff_dvd _).mp h1
  have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 素点の作用は自己同型の逆元を使う。同じ根の指数も d⁻¹。 -/
theorem symm_symm_apply_zeta (d : (ZMod p)ˣ) :
    ((characterEquiv hζ).symm d).symm (baseRoot ζ) =
      baseRoot ζ ^ ((d⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
  have he : ((characterEquiv hζ).symm d).symm = (characterEquiv hζ).symm d⁻¹ := by
    rw [← AlgEquiv.aut_inv, ← map_inv]
  rw [he]
  exact characterEquiv_symm_root hζ d⁻¹

/-- 同じ σd が一つの無限素点を固定することは d=±1 と同値。 -/
theorem smul_infinitePlace_eq_self_iff (_hp : 2 < p) (d : (ZMod p)ˣ) (w : InfinitePlace (rootField ζ)) :
    (characterEquiv hζ).symm d • w = w ↔ (d = 1 ∨ d = -1) := by
  let := rootField_isCyclotomic hζ
  have hroot := baseRoot_primitive hζ
  have hzprim : IsPrimitiveRoot (w.embedding (baseRoot ζ)) p :=
    hroot.map_of_injective w.embedding.injective
  have hz0 : w.embedding (baseRoot ζ) ≠ 0 := by
    intro h0
    have := hzprim.pow_eq_one
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact zero_ne_one this
  have hznorm : ‖w.embedding (baseRoot ζ)‖ = 1 := by
    refine Complex.norm_eq_one_of_pow_eq_one ?_ (Fact.out : p.Prime).ne_zero
    rw [← map_pow, hroot.pow_eq_one, map_one]
  have hconj : (starRingEnd ℂ) (w.embedding (baseRoot ζ)) =
      (w.embedding (baseRoot ζ))⁻¹ :=
    (Complex.inv_eq_conj hznorm).symm
  constructor
  · intro hw
    rw [← mk_embedding w, smul_mk] at hw
    rcases mk_eq_iff.mp hw with h | h
    · left
      have hσ1 : (characterEquiv hζ).symm d = 1 := by
        have hsymm : ((characterEquiv hζ).symm d).symm = 1 := by
          apply AlgEquiv.ext
          intro x
          exact w.embedding.injective (RingHom.congr_fun h x)
        calc (characterEquiv hζ).symm d
            = ((characterEquiv hζ).symm d).symm.symm := (AlgEquiv.symm_symm _).symm
          _ = (1 : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)).symm := by rw [hsymm]
          _ = 1 := rfl
      have hd1 : d = characterEquiv hζ ((characterEquiv hζ).symm d) :=
        (MulEquiv.apply_symm_apply _ d).symm
      rw [hσ1, map_one] at hd1
      exact hd1
    · right
      have heval : w.embedding (((characterEquiv hζ).symm d).symm
          (baseRoot ζ)) =
          (w.embedding (baseRoot ζ))⁻¹ := by
        have h2 := congrArg (starRingEnd ℂ)
          (RingHom.congr_fun h (baseRoot ζ))
        rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at h2
        rw [RingHom.coe_comp, Function.comp_apply] at h2
        exact h2.trans hconj
      rw [symm_symm_apply_zeta, map_pow] at heval
      have hcast : (((((d⁻¹ : (ZMod p)ˣ) : ZMod p)).val : ZMod p)) = -1 :=
        natCast_eq_neg_one_of_pow (p := p) hzprim hz0 heval
      rw [ZMod.natCast_val, ZMod.cast_id] at hcast
      have hinv : d⁻¹ = (-1 : (ZMod p)ˣ) := by
        apply Units.ext
        rw [hcast]
        simp
      rw [← inv_inv d, hinv, neg_one_inv']
  · intro hd
    rcases hd with rfl | rfl
    · rw [map_one]
      exact one_smul _ w
    · rw [← mk_embedding w, smul_mk, mk_eq_iff]
      right
      have hgen : w.embedding (((characterEquiv hζ).symm (-1)).symm
          (baseRoot ζ)) =
          ComplexEmbedding.conjugate w.embedding (baseRoot ζ) := by
        rw [symm_symm_apply_zeta, map_pow, ComplexEmbedding.conjugate_coe_eq, hconj]
        refine pow_natCast_neg_one (p := p) hzprim ?_
        rw [ZMod.natCast_val, ZMod.cast_id, neg_one_inv']
        simp
      have h1 : RingHom.toRatAlgHom
          (w.embedding.comp ↑(((characterEquiv hζ).symm (-1)).symm)) =
          RingHom.toRatAlgHom (ComplexEmbedding.conjugate w.embedding) := by
        apply PowerBasis.algHom_ext (hroot.powerBasis ℚ)
        rw [IsPrimitiveRoot.powerBasis_gen]
        exact hgen
      have h2 : w.embedding.comp ↑(((characterEquiv hζ).symm (-1)).symm) =
          ComplexEmbedding.conjugate w.embedding := congrArg AlgHom.toRingHom h1
      rw [h2]
      exact star_star w.embedding

/-- 同じ素点作用の実際の固定点数。まず一般の totient 表示で得る。 -/
theorem card_fixedPlaces (hp : 2 < p) (d : (ZMod p)ˣ) :
    Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} =
      if d = 1 ∨ d = -1 then p.totient / 2 else 0 := by
  let := rootField_isCyclotomic hζ
  split_ifs with hd
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun w => (smul_infinitePlace_eq_self_iff hζ hp d w).mpr hd))]
    rw [Nat.card_eq_fintype_card]
    have h1 := card_eq_nrRealPlaces_add_nrComplexPlaces (rootField ζ)
    have h2 : nrRealPlaces (rootField ζ) = 0 := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (rootField ζ) hp
    have h3 : nrComplexPlaces (rootField ζ) = p.totient / 2 := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p (rootField ζ)
    omega
  · have he : IsEmpty {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} := by
      refine ⟨fun x => hd ?_⟩
      exact (smul_infinitePlace_eq_self_iff hζ hp d x.1).mp x.2
    have := he
    exact Nat.card_of_isEmpty


/-- 素数次数での固定点数。新しい濃度・作用 provider を要求しない。 -/
theorem card_fixedPlaces_prime (hp : 2 < p) (d : (ZMod p)ˣ) :
    Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} =
      if d = 1 ∨ d = -1 then (p - 1) / 2 else 0 := by
  rw [card_fixedPlaces hζ hp, Nat.totient_prime (Fact.out : p.Prime)]


end
end DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed
