/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticDivisionMultiplication
import DkMath.Lib.NumberTheory.EllipticTorsionFiniteLevel

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionFinite"

/-!
# 実際の標数0のtorsion点群は有限である

無限遠点以外のn-torsion点P=(x,y)では、倍写像の座標公式によりΨSqₙ(x)=0となる。
n≠0ならΨSqₙは非零多項式なので、その根は有限個である。
各x座標の上の点も有限個であることはMathlibの `finite_preimage_xRep0` が保証する。
根に対応する有限個のファイバーと無限遠点を合わせ、実際の点群の核の有限性を得る。

位数n²を数える定理も、除法多項式の全ての根から点を復元する定理も使用しない。
このため、位数公式が未完成でも開核と有限レベルの仮定を除去できる。
有理係数でy座標の分子を構成したため、ここでは標数0に範囲を限定している。
n=0は全点群なので除外する。曲線の非特異点群を使い、特異点を加えることはしない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve Polynomial
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- n倍零の有限座標点は、実際の除法多項式の根に拘束される。 -/
theorem torsion_some_coordinate_root (n : ℕ) {x y : AlgebraicClosure K}
    (h : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular x y)
    (ht : (nsmulAddMonoidHom n : Points E →+ Points E) (Affine.Point.some x y h) = 0) :
    ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x := by
  classical
  have hz : (n : ℤ) • (Affine.Point.some x y h : Points E) = 0 := by
    rw [natCast_zsmul]
    exact ht
  have hψ := (EllipticDivision.WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ
    (E.baseChange (AlgebraicClosure K)) h (n : ℤ)).mp hz
  have hs := EllipticDivision.WeierstrassCurve.evalEval_ψ_sq
    (E.baseChange (AlgebraicClosure K)) h.1 (n : ℤ)
  change _ = 0
  rw [← hs, hψ, zero_pow two_ne_zero]

/-- 非零次数では、有限個の根上の有限ファイバーと無限遠点が全torsion点を覆う。 -/
theorem finite_torsion_of_ne_zero (n : ℕ) (hn : n ≠ 0) : Finite (Torsion E n) := by
  classical
  let W := E.baseChange (AlgebraicClosure K)
  have hpoly : W.ΨSq (n : ℤ) ≠ 0 := W.ΨSq_ne_zero (by exact_mod_cast hn)
  have hroots := Polynomial.finite_setOfPred_isRoot hpoly
  have hfib := hroots.biUnion (fun x _ => W.toAffine.finite_preimage_xRep0 x)
  have hcover : {P : Points E | n • P = 0} ⊆
      {0} ∪ ⋃ x ∈ {x | (W.ΨSq (n : ℤ)).IsRoot x},
        {P : Points E | P.xRep 0 = x} := by
    intro P hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      apply Or.inr
      refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact torsion_some_coordinate_root E n h hP
      · rfl
  have hfinite := ((Set.finite_singleton 0).union hfib).subset hcover
  exact hfinite.to_subtype

/-- 次数が非零のとき、実際のtorsion点群に有限性の標準インスタンスを供給する。 -/
noncomputable instance torsionFinite (n : ℕ) [NeZero n] : Finite (Torsion E n) :=
  finite_torsion_of_ne_zero E n (NeZero.ne n)

/-- 幾何学的有限性を供給した後の開核。位数公式の仮定は不要になる。 -/
theorem representationKernel_isOpen_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    IsOpen (representationKernel E n : Set (Field.absoluteGaloisGroup K)) := by
  have := finite_torsion_of_ne_zero E n hn
  exact representationKernel_isOpen E n

/-- 同じ実際の点群の表現は、非零次数なら有限レベルを持つ。 -/
theorem factorsThroughFiniteLevel_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    FactorsThroughFiniteLevel E n := by
  have := finite_torsion_of_ne_zero E n hn
  exact factorsThroughFiniteLevel E n

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
