/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.KummerExtension

#print "file: DkMath.Lib.NumberTheory.CyclicKummer"

/-!
# 同じ巡回拡大の Kummer 表示

有限巡回拡大 `M/F` の次数と原始根から、実際の `α : M` と `b : F` を得る。
`α^n=b` に加え、`F(α)=M` と `X^n-b` の既約性を保持する。
この生成性により、根を固定することと拡大全体を固定することを取り違えない。
ここでは類群・単数の消滅も、円分 Galois 作用の固有指標も主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclicKummer

open Polynomial
noncomputable section

variable (n : ℕ) (F M : Type*) [Field F] [Field M] [Algebra F M]

/-- 指定した体と指定した包含の上での Kummer 表示。別の同型な体に移さない。 -/
structure Presentation where
  radical : M
  constant : F
  radical_pow : radical ^ n = algebraMap F M constant
  adjoin_eq_top : IntermediateField.adjoin F {radical} = ⊤
  irreducible : Irreducible (X ^ n - C constant)

variable {n F M}

/-- 巡回性・実際の次数・底体の原始根から表示を構成する。
Mathlib の固有ベクトルによる逆 Kummer 定理を使う。 -/
theorem exists_presentation [FiniteDimensional F M] [IsGalois F M]
    [IsCyclic (M ≃ₐ[F] M)] (hdegree : Module.finrank F M = n)
    (hroots : (primitiveRoots n F).Nonempty) : Nonempty (Presentation n F M) := by
  have hroots' : (primitiveRoots (Module.finrank F M) F).Nonempty := hdegree ▸ hroots
  obtain ⟨α, ⟨b, hb⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic F M hroots'
  have hi := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hb.symm hα
  exact ⟨⟨α, b, hdegree ▸ hb.symm, hα, hdegree ▸ hi⟩⟩

namespace Presentation

variable (P : Presentation n F M)

/-- 次数が1でない既約表示の定数は、底体の `n` 乗ではない。 -/
theorem constant_not_pow (hn : n ≠ 1) (b : F) : b ^ n ≠ P.constant :=
  pow_ne_of_irreducible_X_pow_sub_C P.irreducible dvd_rfl hn b

/-- 特に定数は零でない。零の冪から非自明な拡大を作ることはできない。 -/
theorem constant_ne_zero (hn : 1 < n) : P.constant ≠ 0 := by
  intro h
  exact P.constant_not_pow hn.ne' 0 ((zero_pow (Nat.zero_lt_of_lt hn).ne').trans h.symm)

/-- 選んだ同じ根は非零であり、後の Kummer 比 `σ(α)/α` に使える。 -/
theorem radical_ne_zero (hn : 1 < n) : P.radical ≠ 0 := by
  intro h
  have he := P.radical_pow
  rw [h, zero_pow (Nat.zero_lt_of_lt hn).ne'] at he
  exact P.constant_ne_zero hn ((algebraMap F M).injective (he.symm.trans (map_zero _).symm))

/-- 同じ根で一致する底体上の準同型は、拡大全体で一致する。 -/
theorem algHom_ext {E : Type*} [Field E] [Algebra F E]
    {f g : M →ₐ[F] E} (h : f P.radical = g P.radical) : f = g := by
  apply AlgHom.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin F {P.radical} := by
    rw [P.adjoin_eq_top]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => simpa only [Set.mem_singleton_iff.mp hy] using h
  | algebraMap y => exact (f.commutes y).trans (g.commutes y).symm
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | inv y _ hy => simp only [map_inv₀, hy]
  | mul y z _ _ hy hz => simp only [map_mul, hy, hz]

/-- 相対自己同型は同じ根の固定性だけで恒等写像と判定できる。 -/
theorem aut_fix_radical_iff (σ : M ≃ₐ[F] M) : σ P.radical = P.radical ↔ σ = 1 := by
  constructor
  · intro h
    have he : σ.toAlgHom = (1 : M ≃ₐ[F] M).toAlgHom := P.algHom_ext h
    exact AlgEquiv.ext fun x => DFunLike.congr_fun he x
  · rintro rfl
    rfl

/-- 同じ表示の多項式に対して、構成済みの体自身が分解体となる。 -/
theorem isSplittingField [FiniteDimensional F M] (hdegree : Module.finrank F M = n)
    (hroots : (primitiveRoots n F).Nonempty) : IsSplittingField F M (X ^ n - C P.constant) := by
  have hroots' : (primitiveRoots (Module.finrank F M) F).Nonempty := hdegree ▸ hroots
  have hp : P.radical ^ Module.finrank F M = algebraMap F M P.constant := hdegree ▸ P.radical_pow
  have hs := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hroots' hp P.adjoin_eq_top
  exact hdegree ▸ hs

/-- Kummer の比を与える実際の相対 Galois 群と底体の根の群との同型。 -/
def autEquivRoots [NeZero n] [FiniteDimensional F M] (hdegree : Module.finrank F M = n)
    (hroots : (primitiveRoots n F).Nonempty) : (M ≃ₐ[F] M) ≃* rootsOfUnity n F := by
  let := P.isSplittingField hdegree hroots
  exact autEquivRootsOfUnity hroots P.irreducible M

/-- 同型は選んだ同じ根への作用を計算する。 -/
theorem autEquivRoots_smul [NeZero n] [FiniteDimensional F M]
    (hdegree : Module.finrank F M = n) (hroots : (primitiveRoots n F).Nonempty)
    (σ : M ≃ₐ[F] M) : P.autEquivRoots hdegree hroots σ • P.radical = σ P.radical := by
  let := P.isSplittingField hdegree hroots
  exact autEquivRootsOfUnity_smul hroots P.irreducible M P.radical_pow σ

/-- Kummer 指標は実際に同じ根の比 `σ(α)/α` を与える。 -/
theorem autEquivRoots_ratio [NeZero n] [FiniteDimensional F M] (hn : 1 < n)
    (hdegree : Module.finrank F M = n) (hroots : (primitiveRoots n F).Nonempty)
    (σ : M ≃ₐ[F] M) :
    σ P.radical / P.radical =
      algebraMap F M ((P.autEquivRoots hdegree hroots σ).val : F) := by
  have h := P.autEquivRoots_smul hdegree hroots σ
  change ((P.autEquivRoots hdegree hroots σ).val : F) • P.radical = _ at h
  rw [Algebra.smul_def] at h
  rw [← h, mul_div_cancel_right₀ _ (P.radical_ne_zero hn)]

end Presentation
end
end DkMath.Lib.NumberTheory.CyclicKummer
