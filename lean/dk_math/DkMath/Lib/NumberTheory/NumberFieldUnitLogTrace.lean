/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Dirichlet logarithmic trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: compare the SAME integer free-unit action with the actual infinite-place
permutation via the Dirichlet logarithm; cast the SAME integer trace explicitly.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace"

/-!
# 同じ自由単元作用の Dirichlet 対数と無限素点上のトレース

全無限素点への重み付き対数の像は座標和が零の超平面を張る。
同じ整数作用行列を実係数へ写して比較し、自由商の整数 trace が固定素点数−1となる。
円分体の固定点の分類や射影子の trace=1 はまだ証明しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem Module
open NumberFieldUnitGaloisTrace
open scoped NumberField
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- 全無限素点に対する、重み付きの同じ単元の対数。 -/
def logFull : Additive ((𝓞 F)ˣ) →+ (InfinitePlace F → ℝ) where
  toFun x w := mult w * Real.log (w (x.toMul : F))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, Pi.add_apply, map_mul]
    have hx : w (algebraMap (𝓞 F) F (x.toMul : 𝓞 F)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    have hy : w (algebraMap (𝓞 F) F (y.toMul : 𝓞 F)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    rw [Real.log_mul hx hy, mul_add]

omit [NumberField F] in
theorem logFull_apply (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    logFull F (Additive.ofMul u) w = mult w * Real.log (w (u : F)) := rfl

theorem sum_logFull (x : Additive ((𝓞 F)ˣ)) : ∑ w, logFull F x w = 0 :=
  sum_mult_mul_log x.toMul

/-- 全対数が零であることは、同じ元が捩れ単元であることと同値。 -/
theorem logFull_eq_zero_iff {u : (𝓞 F)ˣ} :
    logFull F (Additive.ofMul u) = 0 ↔ u ∈ torsion F := by
  constructor
  · intro h
    refine (logEmbedding_eq_zero_iff (K := F)).mp ?_
    funext w
    exact congrFun h w.1
  · intro h
    funext w
    have hw : w ((u : 𝓞 F) : F) = 1 := (mem_torsion F).mp h w
    simp [logFull_apply, hw]

/-- 対数の実際の核が捩れ単元であることを用いて自由商へ降ろす。 -/
def logQuot : Additive ((𝓞 F)ˣ ⧸ torsion F) →+ (InfinitePlace F → ℝ) :=
  MonoidHom.toAdditiveLeft <|
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logFull F))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext u
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one,
          ← logFull_eq_zero_iff (F := F)])).toMonoidHom

theorem logQuot_mk (u : (𝓞 F)ˣ) :
    logQuot F (Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F))) =
      logFull F (Additive.ofMul u) := rfl

omit [NumberField F] in
private lemma logQuot_surjective_rep (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    ∃ u : (𝓞 F)ˣ,
      x = Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F)) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x.toMul)
  refine ⟨u, ?_⟩
  rw [hu]
  exact (ofMul_toMul x).symm

/-- 同じ Galois 元による無限素点の置換表現。 -/
def permL (σ : F ≃ₐ[ℚ] F) : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w)

private lemma mult_smul' (σ : F ≃ₐ[ℚ] F) (w : InfinitePlace F) : mult (σ • w) = mult w := by
  classical
  simp only [mult]
  exact if_congr isReal_smul_iff rfl rfl

theorem logFull_unitsMap (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    logFull F (Additive.ofMul (unitsMap F σ u)) = permL F σ (logFull F (Additive.ofMul u)) := by
  funext w
  simp only [permL, LinearMap.funLeft_apply, logFull_apply, unitsMap_coe]
  have h1 : (σ⁻¹ • w) ((u : 𝓞 F) : F) = w (σ ((u : 𝓞 F) : F)) := by
    rw [NumberField.InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rw [mult_smul' F σ⁻¹ w, h1]

/-- 整数自由商の同じ作用と、実際の対数・素点置換との同変性。 -/
theorem logQuot_quotMap (σ : F ≃ₐ[ℚ] F) (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    logQuot F (quotMap F σ x) = permL F σ (logQuot F x) := by
  obtain ⟨u, rfl⟩ := logQuot_surjective_rep F x
  rw [quotMap_mk, logQuot_mk, logQuot_mk, logFull_unitsMap]

private def vFam : Fin (rank F) → (InfinitePlace F → ℝ) := fun i => logQuot F (basisModTorsion F i)

private def restr : (InfinitePlace F → ℝ) →ₗ[ℝ] logSpace F :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {w : InfinitePlace F // w ≠ w₀} → InfinitePlace F)

private lemma restr_logFull (x : Additive ((𝓞 F)ˣ)) :
    restr F (logFull F x) = logEmbedding F x := rfl

private lemma restr_vFam (i : Fin (rank F)) :
    restr F (vFam F i) = (basisUnitLattice F i : logSpace F) := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep F (basisModTorsion F i)
  rw [vFam, hu, logQuot_mk, restr_logFull, basisUnitLattice, Basis.map_apply, hu,
    logEmbeddingEquiv_apply]

private lemma span_restr_vFam :
    Submodule.span ℝ (Set.range ((restr F) ∘ (vFam F))) = ⊤ := by
  rw [← unitLattice_span_eq_top (K := F)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    rw [Function.comp_apply, restr_vFam]
    exact Submodule.subset_span (basisUnitLattice F i).2
  · rw [Submodule.span_le]
    intro y hy
    set z : unitLattice F := ⟨y, hy⟩ with hzdef
    have hz : y = ((∑ i, (basisUnitLattice F).repr z i • basisUnitLattice F i :
        unitLattice F) : logSpace F) := by
      rw [(basisUnitLattice F).sum_repr z]
    rw [hz]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine zsmul_mem (Submodule.subset_span ?_) _
    refine Set.mem_range.mpr ⟨i, ?_⟩
    rw [Function.comp_apply, restr_vFam]

private lemma linearIndependent_vFam : LinearIndependent ℝ (vFam F) := by
  classical
  refine LinearIndependent.of_comp (restr F) ?_
  refine linearIndependent_of_top_le_span_of_card_eq_finrank
    (le_of_eq (span_restr_vFam F).symm) ?_
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, rank]

private lemma sum_vFam_eq_zero (i : Fin (rank F)) : ∑ w, vFam F i w = 0 := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep F (basisModTorsion F i)
  rw [vFam, hu, logQuot_mk]
  exact sum_logFull F _

private abbrev Wv : Submodule ℝ (InfinitePlace F → ℝ) := Submodule.span ℝ (Set.range (vFam F))

private abbrev Lone : Submodule ℝ (InfinitePlace F → ℝ) :=
  Submodule.span ℝ {(fun _ => (1 : ℝ) : InfinitePlace F → ℝ)}

private def sFun : (InfinitePlace F → ℝ) →ₗ[ℝ] ℝ := ∑ w, LinearMap.proj w

private lemma sFun_apply (f : InfinitePlace F → ℝ) : sFun F f = ∑ w, f w := by
  simp [sFun]

private lemma sFun_vanish_Wv {x : InfinitePlace F → ℝ} (hx : x ∈ Wv F) : sFun F x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; rw [sFun_apply]; exact sum_vFam_eq_zero F i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private lemma isCompl_Wv_Lone : IsCompl (Wv F) (Lone F) := by
  have hcard : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  have hdisj : Disjoint (Wv F) (Lone F) := by
    rw [Submodule.disjoint_def]
    intro x hxW hxL
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have h0 := sFun_vanish_Wv F hxW
    rw [map_smul, sFun_apply] at h0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc (Nat.cast_ne_zero.mpr hcard.ne')
  have hone : (fun _ => (1 : ℝ) : InfinitePlace F → ℝ) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary _)
    norm_num at this
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Wv F) (Lone F)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at hsum
  have hWv : Module.finrank ℝ (Wv F) = rank F := by
    rw [Wv, finrank_span_eq_card (linearIndependent_vFam F), Fintype.card_fin]
  have hLone : Module.finrank ℝ (Lone F) = 1 := by
    rw [Lone, finrank_span_singleton hone]
  rw [hWv, hLone] at hsum
  rw [hsum, Module.finrank_fintype_fun_eq_card, rank]
  omega

private lemma permL_one_const (σ : F ≃ₐ[ℚ] F) :
    permL F σ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := rfl

private lemma logQuot_mem_Wv (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) : logQuot F x ∈ Wv F := by
  have hx := (basisModTorsion F).sum_repr x
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

private lemma permL_mem_Wv (σ : F ≃ₐ[ℚ] F) {x : InfinitePlace F → ℝ} (hx : x ∈ Wv F) :
    permL F σ x ∈ Wv F := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    rw [show vFam F i = logQuot F (basisModTorsion F i) from rfl, ← logQuot_quotMap]
    exact logQuot_mem_Wv F _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private lemma permL_mem_Lone (σ : F ≃ₐ[ℚ] F) {_x : InfinitePlace F → ℝ} (hx : _x ∈ Lone F) :
    permL F σ _x ∈ Lone F := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, permL_one_const]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma one_ne_zero' : (fun _ => (1 : ℝ) : InfinitePlace F → ℝ) ≠ 0 := by
  intro h
  have := congrFun h (Classical.arbitrary _)
  norm_num at this

private lemma finrank_Lone : Module.finrank ℝ (Lone F) = 1 := by
  rw [Lone, finrank_span_singleton (one_ne_zero' F)]

/-- 座標の引き戻し作用の実トレースは、実際の固定座標数。 -/
theorem trace_funLeft (g : InfinitePlace F → InfinitePlace F) :
    LinearMap.trace ℝ (InfinitePlace F → ℝ) (LinearMap.funLeft ℝ ℝ g) =
      Nat.card {w // g w = w} := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (InfinitePlace F)), Matrix.trace]
  have hdiag : ∀ i, (LinearMap.toMatrix (Pi.basisFun ℝ (InfinitePlace F))
      (Pi.basisFun ℝ (InfinitePlace F)) (LinearMap.funLeft ℝ ℝ g)).diag i =
      if g i = i then 1 else 0 := by
    intro i
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      LinearMap.funLeft_apply, Pi.basisFun_apply]
    simp [Pi.single_apply]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_boole]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma trace_eq_trace_restrict_add_trace_restrict
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : IsCompl p q) (f : M →ₗ[R] M)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q)
    [Module.Finite R p] [Module.Free R p] [Module.Finite R q] [Module.Free R q] :
    LinearMap.trace R M f =
      LinearMap.trace R p (f.restrict hp) + LinearMap.trace R q (f.restrict hq) := by
  have key : (Submodule.prodEquivOfIsCompl p q h).symm.conj f =
      LinearMap.prodMap (f.restrict hp) (f.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm]
    rw [LinearEquiv.symm_apply_eq]
    rw [LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add]
    rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
  calc LinearMap.trace R M f
      = LinearMap.trace R (p × q) ((Submodule.prodEquivOfIsCompl p q h).symm.conj f) :=
        (LinearMap.trace_conj' f _).symm
    _ = _ := by rw [key, LinearMap.trace_prodMap']

private lemma permL_vFam_eq (σ : F ≃ₐ[ℚ] F) (j : Fin (rank F)) :
    permL F σ (vFam F j) =
      ∑ i, ((LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F)
        (quotMapLin F σ)) i j : ℝ) • vFam F i := by
  have h0 : permL F σ (vFam F j) = logQuot F (quotMapLin F σ (basisModTorsion F j)) := by
    rw [quotMapLin_apply, show vFam F j = logQuot F (basisModTorsion F j) from rfl,
      logQuot_quotMap]
  rw [h0]
  conv_lhs => rw [← (basisModTorsion F).sum_repr (quotMapLin F σ (basisModTorsion F j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, LinearMap.toMatrix_apply]
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

private lemma trace_restrict_Lone (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℝ (Lone F)
      ((permL F σ).restrict (fun _x hx => permL_mem_Lone F σ hx)) = 1 := by
  have hid : (permL F σ).restrict (fun _x hx => permL_mem_Lone F σ hx) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨_x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq, map_smul, permL_one_const]
  rw [hid, LinearMap.trace_id, finrank_Lone]
  norm_num

private lemma trace_restrict_Wv (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℝ (Wv F)
      ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) =
      ((LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F)
        (quotMapLin F σ)).trace : ℝ) := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F) (quotMapLin F σ)
    with hA
  set bW : Basis (Fin (rank F)) ℝ (Wv F) :=
    (Basis.span (linearIndependent_vFam F) : _) with hbW
  have hcoe : ∀ j, (bW j : InfinitePlace F → ℝ) = vFam F j := by
    intro j
    rw [hbW]
    exact congrArg Subtype.val (Basis.span_apply (linearIndependent_vFam F) j)
  have hW : ∀ j, ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) (bW j) =
      ∑ k, (A k j : ℝ) • bW k := by
    intro j
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hcoe, permL_vFam_eq]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by rw [SetLike.val_smul, hcoe]
  have hmat : LinearMap.toMatrix bW bW
      ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) =
      A.map (Int.cast : ℤ → ℝ) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hW j, map_sum]
    simp [Basis.repr_self, Finsupp.single_apply]
  rw [LinearMap.trace_eq_matrix_trace ℝ bW, hmat, Matrix.trace, Matrix.trace]
  push_cast
  rfl

/-- 同じ自由単元商の整数 trace は、実際の無限素点の固定点数−1。 -/
theorem trace_quotMap_eq (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) (quotMapLin F σ) =
      (Nat.card {w : InfinitePlace F // σ • w = w} : ℤ) - 1 := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F) (quotMapLin F σ)
    with hA
  have h1 : LinearMap.trace ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) (quotMapLin F σ) = A.trace := by
    rw [hA]
    exact LinearMap.trace_eq_matrix_trace ℤ (basisModTorsion F) _
  have h2 : LinearMap.trace ℝ (InfinitePlace F → ℝ) (permL F σ) =
      (Nat.card {w : InfinitePlace F // σ • w = w} : ℝ) := by
    rw [show permL F σ = LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w) from rfl, trace_funLeft]
    congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    rw [inv_smul_eq_iff, eq_comm]
  have h3 := trace_eq_trace_restrict_add_trace_restrict (isCompl_Wv_Lone F) (permL F σ)
    (fun _x hx => permL_mem_Wv F σ hx) (fun _x hx => permL_mem_Lone F σ hx)
  rw [trace_restrict_Wv, trace_restrict_Lone, h2, ← hA] at h3
  rw [h1]
  have h4 : ((A.trace : ℤ) : ℝ) =
      ((Nat.card {w : InfinitePlace F // σ • w = w} : ℤ) : ℝ) - 1 := by
    push_cast
    rw [h3]
    ring
  exact_mod_cast h4


/-- 同じ UnitClass の mod p trace を、捩れ成分と実際の固定素点数へ接続する。 -/
theorem trace_vMap_eq_exponent_add_fixedPlaces (p : ℕ) [Fact p.Prime]
    (hdiv : p ∣ torsionOrder F) (σ : F ≃ₐ[ℚ] F) (n : ℕ)
    (hσ : ∀ x : 𝓞 F, x ^ p = 1 →
      (CyclotomicKummerEquivariance.integerAut σ).integers x = x ^ n) :
    LinearMap.trace (ZMod p) _ (vMap p F σ) =
      (n : ZMod p) + (Nat.card {w : InfinitePlace F // σ • w = w} : ZMod p) - 1 := by
  rw [trace_vMap p F hdiv σ n hσ, trace_quotMap_eq, Int.cast_sub,
    Int.cast_natCast, Int.cast_one]
  ring

end

section Cyclotomic

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicKummerEquivariance

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
noncomputable section

/-- 同じ指標で選んだ自己同型は、整数環のすべての p 乗根に d 乗で作用する。 -/
theorem integerAut_on_pth_roots (d : (ZMod p)ˣ) (x : 𝓞 (rootField ζ)) (hx : x ^ p = 1) :
    (integerAut ((characterEquiv hζ).symm d)).integers x = x ^ (d : ZMod p).val := by
  have hroot := (baseRoot_primitive hζ).toInteger_isPrimitiveRoot
  obtain ⟨a, _, ha⟩ := hroot.eq_pow_of_pow_eq_one hx
  have he : (integerAut ((characterEquiv hζ).symm d)).integers
      (baseRoot_primitive hζ).toInteger = (baseRoot_primitive hζ).toInteger ^ (d : ZMod p).val := by
    apply NumberField.RingOfIntegers.coe_injective
    exact characterEquiv_symm_root hζ d
  rw [← ha, map_pow, he, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- 同じ既存 unitAction の実際の trace。固定素点数の ±1 分類はまだ入力しない。 -/
theorem trace_unitAction_eq_character_add_fixedPlaces (d : (ZMod p)ˣ) :
    LinearMap.trace (ZMod p) _ (unitAction (p := p) ((characterEquiv hζ).symm d)) =
      (d : ZMod p) +
        (Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} : ZMod p) - 1 := by
  have hdiv : p ∣ torsionOrder (rootField ζ) :=
    dvd_torsionOrder_of_isPrimitiveRoot (baseRoot_primitive hζ)
  have h := trace_vMap_eq_exponent_add_fixedPlaces (rootField ζ) p hdiv
    ((characterEquiv hζ).symm d) (d : ZMod p).val (integerAut_on_pth_roots hζ d)
  rw [ZMod.natCast_zmod_val] at h
  exact h

end
end Cyclotomic
end DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace
