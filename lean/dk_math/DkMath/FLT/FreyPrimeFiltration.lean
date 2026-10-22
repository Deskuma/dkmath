/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeGoodFiltration
import DkMath.FLT.FreyNodalReduction
import DkMath.Lib.NumberTheory.EllipticNodalInertia

#print "file: DkMath.FLT.FreyPrimeFiltration"

/-!
# NOTE-031-004: p上の良還元・乗法的還元を統合した局所二択

pがabcを割る場合、慣性変化量はまず滑らかな零成分へ入り、
還元準同型と剰余標数pでの節点曲線の捩れ消滅により、実際の還元核へ入る。
pがabcを割らない場合も、既存の良還元の定理から同じ還元核へ入る。
安定直線から得られる整な有限p捩れ点はこの核の外にあるので、核は真部分空間である。
最後に階数2の吸収空間補題と共役輸送により、全てのp上の場所で同じ側の二択を得る。
031-005の大域化やCofixed直線の不存在は本章の範囲に含まない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticDyadicSeparation EllipticTorsionRepresentation
open EllipticGoodReductionSeparation ValuationInertia WeierstrassCurve
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
noncomputable local instance instDecidableEqFreyPrimeFiltration : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- pがabcを割る場合、全ての実点の慣性変化量は同じモデルで滑らかに還元する。
位数を制限せず、以前構成した中心と接方向をそのまま慣性比較へ渡す。 -/
theorem inertia_difference_smooth_at_bad_prime (hp2 : p ≠ 2)
    (hbad : (p : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (P : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    HasSmoothReduction (S.valuationModel A) (Affine.Point.map σ.toAlgHom P - P) := by
  classical
  obtain ⟨C, D, hfix, _⟩ := S.exists_criticalCentre_directions_at_bad_prime
    (Nat.Prime.pos Fact.out) hp2 hbad A hA
  exact EllipticNodalInertia.inertia_difference_smooth S.rationalCurve A (S.valuationModel A)
    (S.valuationModel_map A) C D σ hσ (hfix σ hσ).1 P

/-- pがabcを割る場合も、全残余変化量は同じ還元核のFₚ部分加群へ入る。
剰余でのp倍零性は実際の還元準同型から供給し、節点曲線のp-torsion消滅へ接続する。 -/
theorem residualReductionKernel_absorbs_at_bad_prime (hp2 : p ≠ 2)
    (hbad : (p : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    CofixedOn S.residualRepresentation (S.residualReductionKernel A) (inertiaSubgroupIn A ℚ) := by
  classical
  have : CharP (IsLocalRing.ResidueField A) p := ValuationPrimeSupport.charP_residueField A Fact.out hA
  obtain ⟨C, _, _⟩ := S.exists_criticalCentre_at_bad_prime (Nat.Prime.pos Fact.out) hp2 hbad A hA
  intro σ hσ P
  rw [S.mem_residualReductionKernel_iff]
  let Q : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point := P.val
  have hs := S.inertia_difference_smooth_at_bad_prime hp2 hbad A hA σ hσ Q
  have ht := P.property
  change p • Q = 0 at ht
  have hd : p • (Affine.Point.map σ.toAlgHom Q - Q) = 0 := by
    rw [nsmul_sub, ← map_nsmul, ht, _root_.map_zero, sub_self]
  exact EllipticNodalReductionKernel.pole_of_smooth_torsion_of_model (S.valuationModel A)
    _ (S.valuationModel_map A) C hs hd

/-- 良還元・乗法的還元の両場合で、同じ還元核が全慣性変化量を吸収する。
abcの可除性は内部で場合分けし、呼出し側へ未証明のproviderを要求しない。 -/
theorem residualReductionKernel_absorbs_at_p (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    CofixedOn S.residualRepresentation (S.residualReductionKernel A) (inertiaSubgroupIn A ℚ) := by
  by_cases hd : (p : ℤ) ∣ S.a * S.b * S.c
  · exact S.residualReductionKernel_absorbs_at_bad_prime hp2 hd A hA
  · exact S.residualReductionKernel_absorbs_at_good_prime hp2 hd A hA

/-- 同じ全ガロア安定な真の非零部分空間について、p上の慣性全体でFixedまたはCofixedとなる。
真の吸収空間は同じSourceの数論から構成済みであり、追加の吸収仮定を持たない。 -/
theorem residual_fixed_or_cofixed_at_p (hp5 : 5 ≤ p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∨
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) := by
  have := S.rationalCurve_isElliptic
  exact AbsorbingSubspace.fixed_or_cofixed S.residualRepresentation S.residual_finrank_eq_two
    (inertiaSubgroupIn A ℚ) N (fun g _ => hN g) hbot htop (S.residualReductionKernel A)
    (S.residualReductionKernel_ne_top hp5 A hA N hN hbot htop)
    (S.residualReductionKernel_absorbs_at_p (by omega) A hA)

/-- 031-004の終点。一つの側を選び、全てのp上の付値環へその側を保存して輸送する。
同じSource・同じ安定直線・同じ商を保持し、場所ごとの二択へ弱めない。 -/
theorem residual_common_side_at_p (hp5 : 5 ≤ p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p →
      FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p →
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) := by
  by_cases hex : ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p
  · obtain ⟨A, hA⟩ := hex
    exact AbsoluteInertiaConjugacy.common_side_on_places S.residualRepresentation N hN Fact.out A hA
      (S.residual_fixed_or_cofixed_at_p hp5 N hN hbot htop A hA)
  · left
    intro A hA
    exact (hex ⟨A, hA⟩).elim

end DkMath.FLT.Frey.Source
