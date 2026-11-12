/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedTorsionExtension
import DkMath.FLT.FreyTorsionInertiaAbsorption
import DkMath.Lib.Algebra.TorsionPreimageLocalComplement

#print "file: DkMath.FLT.FreyCofixedTorsionTower"

/-!
# Cofixed 直線から、巡回捩れ塔の全段の実際の extension へ

同じ残余直線の点部分群 `B` を含む巡回 `K` を考える。
`#K=p^m`, `m≥1` なら `K[p]=B` を濃度から証明できる。従って既存の `B` 上の
円分作用は、全段の `V/C ≃ K/pK` へ輸送できる。`K` 全体が mod `p` の円分指標で
作用されるとは主張せず、第一段の `pK=0` を仮定することもない。

商の二次元性、固定像の一次元性・点ごとの固定性、開核も同じ `K` から供給する。
また最終 Frobenius 矛盾の底への降下仮定を、巡回性から除去する。
塔そのもの、局所分裂、大域 extension 消滅、Frobenius 関係は未構成である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule ValuationInertia
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 巡回塔のどの段でも、`p` 捩れ点は元の同じ残余直線へ戻る。
この結論に Cofixed 性や Galois 安定性は不要。 -/
theorem residual_cyclic_tower_socle_mem_base
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {x : Points S.rationalCurve} (hx : x ∈ K) (hpx : p • x = 0) :
    x ∈ pointSubgroup S.rationalCurve p L :=
  CyclicPrimePowerScalar.socle_mem_of_prime_subgroup (Fact.out : p.Prime) hm
    K (pointSubgroup S.rationalCurve p L) hcard hbase
    (card_pointSubgroup S.rationalCurve p L hline)
    (pointSubgroup_killed S.rationalCurve p L) hx hpx

/-- 全段の円分商公式。底の円分作用を使い、`pK=0` の制限を除く。 -/
theorem residual_cofixed_cyclic_extension_quotient_cyclotomic
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    (σ : Field.absoluteGaloisGroup ℚ) (v : TorsionPreimageQuotient.Quotient p K) :
    preimageRepresentation S.rationalCurve p K hstable σ v -
        (cyclotomicCharacter p σ : ZMod p).val • v ∈ TorsionPreimageQuotient.torsionImage p K := by
  apply TorsionPreimageQuotient.representation_sub_nsmul_mem_torsionImage_of_cyclic
    (Fact.out : p.Prime) K hm hcard (pointActionEndHom S.rationalCurve) hstable
    (fun τ => (cyclotomicCharacter p τ : ZMod p).val) ?_ σ v
  intro τ x hx hpx
  exact S.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul L hline hcofixed τ
    (S.residual_cyclic_tower_socle_mem_base L hline K hm hcard hbase hx hpx)

/-- 同じ巡回段から、固定線を持つ二次元の連続有限表現を構成する。
捩れ指数は `#K=p^m` から供給し、個別の provider にしない。 -/
theorem residual_cofixed_cyclic_extension_profile
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K) :
    Nat.card (TorsionPreimageQuotient.Quotient p K) = p ^ 2 ∧
      Module.finrank (ZMod p) (TorsionPreimageQuotient.Quotient p K) = 2 ∧
      Module.finrank (ZMod p) (TorsionPreimageQuotient.torsionImage p K) = 1 ∧
      IsFixedOn (preimageRepresentation S.rationalCurve p K hstable)
        (TorsionPreimageQuotient.torsionImage p K) ∧
      IsOpen ((preimageRepresentation S.rationalCurve p K hstable).ker :
        Set (Field.absoluteGaloisGroup ℚ)) := by
  refine ⟨card_preimageQuotient S.rationalCurve K, finrank_preimageQuotient S.rationalCurve K,
    finrank_torsionImage_of_cyclic S.rationalCurve K hm hcard,
    preimageRepresentation_fixed_torsionImage_of_cofixed S.rationalCurve K hstable L hcofixed hbase,
    preimageRepresentation_kernel_isOpen S.rationalCurve K hstable m ?_⟩
  intro x hx
  exact congrArg (fun z : K => z.val)
    (hcard ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : K)))

/-- 局所部分群を同じ商へ送り、実際の分解群安定な補直線を得る。
`F` の存在・局所安定性は算術入力だが、補直線性とその輸送はここで証明する。 -/
theorem residual_cyclic_extension_complement_of_local_subgroup
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (F : AddSubgroup (Points S.rationalCurve))
    (hKF : K ≤ F) (hFP : ∀ x ∈ F, p • x ∈ K)
    (hFcard : Nat.card F = p ^ (m + 1))
    (hFdown : ∀ x ∈ F, p • x = 0 → x ∈ K)
    (hFstable : ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, pointAction S.rationalCurve σ x ∈ F) :
    ∃ C' : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) C' ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ v ∈ C',
        preimageRepresentation S.rationalCurve p K hstable σ v ∈ C') ∧
      TorsionPreimageQuotient.liftSubmodule p K C' = F := by
  refine ⟨TorsionPreimageQuotient.imageSubmodule p K F, ?_, ?_, ?_⟩
  · exact TorsionPreimageQuotient.isCompl_imageSubmodule K F hcard hFcard
      (card_preimageQuotient S.rationalCurve K)
      (card_torsionImage_of_cyclic S.rationalCurve K hm hcard) hKF hFP hFdown
  · intro σ hσ v hv
    exact TorsionPreimageQuotient.imageSubmodule_stable p K F
      (pointActionEndHom S.rationalCurve) hstable σ (hFstable σ hσ) hv
  · exact TorsionPreimageQuotient.lift_imageSubmodule p K F hKF hFP

/-- `p` 以外の全素点における商表現の不分岐性。
良還元素数は内部供給し、`2` と `abc` の素因子での逆像上の吸収だけを残す。
元の `E[p]` の不分岐性を高位捩れへ拡張したとはしない。 -/
theorem residual_preimage_unramified_away_of_bad_inertia
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hcard : Nat.card K = p ^ m)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → (q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    (v : TorsionPreimageQuotient.Quotient p K) :
    preimageRepresentation S.rationalCurve p K hstable τ v = v := by
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    change TorsionPreimageQuotient.quotientMap p K
      (TorsionPreimageQuotient.mapPreimage p K (pointAction S.rationalCurve τ) (hstable τ) y) =
        TorsionPreimageQuotient.quotientMap p K y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (TorsionPreimageQuotient.quotientMap_eq_zero_iff p K _).mpr
    change pointAction S.rationalCurve τ y.val - y.val ∈ K
    by_cases hb : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c
    · exact hbad q hq hqp hb A hA τ hτ y.val y.property
    · have hq2 : q ≠ 2 := fun h => hb (Or.inl h)
      have hgood : ¬ (q : ℤ) ∣ S.curve.Δ := by
        intro hΔ
        let : Fact q.Prime := ⟨hq⟩
        exact hb (Or.inr ((FreyPrimeValuation.prime_dvd_integral_discriminant_iff
          (Fact.out : p.Prime).pos hq2 S.normalization S.equation).mp hΔ))
      have hqn : ¬ q ∣ p ^ (m + 1) := by
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (hq.dvd_of_dvd_pow h))
      have hy : p ^ (m + 1) • y.val = 0 := by
        rw [pow_succ, mul_nsmul']
        exact congrArg (fun z : K => z.val)
          (hcard ▸ card_nsmul_eq_zero' (x := (⟨p • y.val, y.property⟩ : K)))
      rw [pointAction_eq_of_inertia_of_integer_good S.rationalCurve S.curve S.curve_map
        hq hqn hgood A hA τ hτ hy, sub_self]
      exact K.zero_mem

/-- 最終矛盾の `hdown` を、巡回段の底への包含から内部供給する。
残る仮定は高位捩れの悪い住所での吸収と実際の Frobenius 関係である。 -/
theorem residual_cyclic_tower_inertia_frobenius_impossible
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {N : ℕ} (hN : 0 < N)
    (hbad : ∀ q : ℕ, q.Prime → (q = 2 ∨ q = p ∨ (q : ℤ) ∣ S.a * S.b * S.c) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p ^ N • y = 0 → pointAction S.rationalCurve τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) (ell : ℤ)
    (hCH : ∀ y : Points S.rationalCurve, p ^ N • y = 0 →
      pointAction S.rationalCurve σ (pointAction S.rationalCurve σ y) + ell • y =
        (ell + 1 - (N : ℤ)) • pointAction S.rationalCurve σ y) : False :=
  S.residual_line_tower_inertia_frobenius_impossible L hline K hN
    (fun _ hx hpx => S.residual_cyclic_tower_socle_mem_base L hline K hm hcard hbase hx hpx)
    hbad σ ell hCH

end
end DkMath.FLT.Frey.Source
