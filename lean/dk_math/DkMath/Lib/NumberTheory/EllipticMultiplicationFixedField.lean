/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean.
Upstream blob: e82e468ec9dc155bbe1c531016cbd83735a3b037
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticMultiplicationFunctionDegree
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import Mathlib.FieldTheory.Fixed

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationFixedField"

/-!
# torsion平行移動の固定体は倍写像の像である

既存の作用の忠実性と|E[n]|=n²から、固定体に対する関数体の次数はn²。
一方、[n](γ+S)=[n]γなので倍写像の引き戻しの像は固定体に含まれる。
028-Aで証明した関数体全体の上界n²を比較し、二つの中間体の一致を得る。
固定体の一致だけでは局所付値の降下や非退化性までは得られない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticMultiplicationFixedField : DecidableEq (AlgebraicClosure K) := Classical.decEq _

omit [CharZero K] in
/-- 同じ実際のtorsion点を関数体の平行移動へ送る群準同型。
加法群をMultiplicativeで包むのは、自己同型群の乗法に型を合わせるためだけである。 -/
noncomputable def torsionTranslation (n : ℕ) : Multiplicative (Torsion E n) →*
    ((E.toAffine⁄(AlgebraicClosure K)).FunctionField ≃ₐ[AlgebraicClosure K]
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField) where
  toFun S := transEquiv E (AlgebraicClosure K) S.toAdd.val
  map_one' := by
    change transEquiv E (AlgebraicClosure K) 0 = 1
    rw [transEquiv_zero]
    rfl
  map_mul' S T := by
    change transEquiv E (AlgebraicClosure K) (S.toAdd.val + T.toAdd.val) = _
    exact transEquiv_add E (AlgebraicClosure K) S.toAdd.val T.toAdd.val

omit [CharZero K] in
/-- 関数体上の平行移動を等しくする二つのtorsion点は等しい。 -/
theorem torsionTranslation_injective (n : ℕ) : Function.Injective (torsionTranslation E n) := by
  intro S T h
  exact Multiplicative.toAdd.injective (Subtype.ext (transEquiv_injective E (AlgebraicClosure K) h))

omit [CharZero K] in
/-- torsion平行移動から実際に生成される有限自己同型群。 -/
noncomputable def torsionTranslationGroup (n : ℕ) :
    Subgroup ((E.toAffine⁄(AlgebraicClosure K)).FunctionField ≃ₐ[AlgebraicClosure K]
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField) := (torsionTranslation E n).range

/-- 忠実性により、平行移動自己同型群の位数は同じ実際のtorsionの位数n²である。 -/
theorem card_torsionTranslationGroup (n : ℕ) (hn : n ≠ 0) : Nat.card (torsionTranslationGroup E n) = n ^ 2 := by
  rw [← card_torsion_sq E n hn]
  exact (Nat.card_congr (Equiv.ofInjective (torsionTranslation E n) (torsionTranslation_injective E n))).symm

/-- 非零指数のtorsion平行移動群の有限性を、正確な位数から得る。 -/
theorem finite_torsionTranslationGroup (n : ℕ) (hn : n ≠ 0) : Finite (torsionTranslationGroup E n) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsionTranslationGroup E n hn]; exact pow_ne_zero 2 hn)

omit [CharZero K] in
/-- 同じtorsion平行移動群の固定体。定義に次数公式や非退化性を含めない。 -/
noncomputable def torsionFixedField (n : ℕ) :
    IntermediateField (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  IntermediateField.fixedField (torsionTranslationGroup E n)

/-- 有限自己同型群の固定体定理より、固定体に対する次数はn²となる。 -/
theorem finrank_torsionFixedField (n : ℕ) (hn : n ≠ 0) :
    Module.finrank (torsionFixedField E n) (E.toAffine⁄(AlgebraicClosure K)).FunctionField = n ^ 2 := by
  let := finite_torsionTranslationGroup E n hn
  let := Fintype.ofFinite (torsionTranslationGroup E n)
  change Module.finrank (FixedPoints.subfield (torsionTranslationGroup E n)
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField) (E.toAffine⁄(AlgebraicClosure K)).FunctionField = _
  rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, card_torsionTranslationGroup E n hn]

/-- 倍写像の像はtorsion平行移動で固定される。 -/
theorem multiplicationRange_le_torsionFixedField (n : ℕ) (hn : n ≠ 0) :
    (multiplicationPull E n hn).fieldRange ≤ torsionFixedField E n := by
  rintro x ⟨f, rfl⟩
  change _ ∈ IntermediateField.fixedField (torsionTranslationGroup E n)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  obtain ⟨S, rfl⟩ := hσ
  exact transEquiv_multiplicationPull E n hn S.toAdd.val S.toAdd.property f

/-- 028-Bの固定体同定。包含と上下からの次数n²の比較で、実際の二つの中間体が一致する。 -/
theorem multiplicationRange_eq_torsionFixedField (n : ℕ) (hn : n ≠ 0) :
    (multiplicationPull E n hn).fieldRange = torsionFixedField E n := by
  obtain ⟨hfd, hdeg⟩ := finiteDimensional_finrank_multiplicationPull E n hn
  let := hfd
  apply IntermediateField.eq_of_le_of_finrank_le' (multiplicationRange_le_torsionFixedField E n hn)
  rw [finrank_torsionFixedField E n hn]
  exact hdeg

/-- 固定体同定を使えば、上界だった実際の倍写像の関数体次数が正確にn²となる。 -/
theorem finrank_multiplicationPull (n : ℕ) (hn : n ≠ 0) :
    Module.finrank (multiplicationPull E n hn).fieldRange
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField = n ^ 2 := by
  rw [multiplicationRange_eq_torsionFixedField E n hn]
  exact finrank_torsionFixedField E n hn

/-- 固定体の同定を、有理関数の実際の原像の存在として使う入口。
この等式だけでは、原像の零点・極の位数をまだ主張しない。 -/
theorem exists_multiplicationPull_of_invariant (n : ℕ) (hn : n ≠ 0)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : ∀ S : Torsion E n, transEquiv E (AlgebraicClosure K) S.val f = f) :
    ∃ g, multiplicationPull E n hn g = f := by
  have hmem : f ∈ torsionFixedField E n := by
    change f ∈ IntermediateField.fixedField (torsionTranslationGroup E n)
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨S, rfl⟩ := hσ
    exact hf S.toAdd
  rw [← multiplicationRange_eq_torsionFixedField E n hn] at hmem
  exact hmem

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
