# NOTE-032 教科書：局所 Frobenius の稠密性と残余 p 捩れ像による共鳴枝判定

## 7 ステップ

1. 開部分群 modulo の近似から profinite 群の稠密生成を導く。
2. 実際の q 上の付値環について、I と Frobenius φ による D の稠密生成を、
   既存の局所開部分群定理から証明する。同じ住所に φ も内部構成する。
3. 元の残余直線 L の像は上段商 Q で零。大域 cofixed 性の下では、
   同じ曲線の E[p] から来る Q の類は全 Galois 元で固定される。
4. 同じ障害値 v が実際の E[p] の像であることを `GeneratorValueFromResidual` として明示。
   この条件と cofixed 性の下で、q≡1 の枝の D 固定性を証明する。
   障害値は底の L 自体の像ではないことも証明する。
5. 位数が 2 より大きい加法群の元について、固定と符号反転を分離する。
6. 同じ E[p] の像条件と cofixed 性の下、q≡−1 の枝では D 固定性が成立しない。
7. 同じ条件の下で D 固定性と q≡1 を同値化し、正の枝では連続代表を持つ非零通常 H¹(D,F) 類を得る。

`GeneratorValueFromResidual` は、元の障害値を実際の E[p] の点で表す存在条件である。
障害値の位数が p であることだけから、この代表の存在は導いていない。
大域 `hcofixed`、代表 `hres`、正の枝 `hq1` は終点に明示している。
負の枝における非固定性自体は矛盾や一般 hno ではない。
また、残る大域 Selmer・`hclass` と無条件一般 hno は未完成である。

模範解答の `S_FreyPackage_frey_torsion_fixed_eq_zero.lean` は、
大域的に固定された実際の p 捩れ点を有理点へ下降させて消滅させる。
今回の障害値は上段商の元なので、その定理を直接適用するには別の持ち上げが必要である。

以下の各 Lean ブロックは production ファイル全文であり、import の直後に
`#print "file: ..."` を保持する。


## STEP 1: `DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Topology.Algebra.ClopenNhdofOne

#print "file: DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration"

/-! # 開部分群 modulo の生成から profinite 群の稠密生成へ -/
namespace DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration

/-- profinite 群の閉部分群が、それを含む全開部分群で全群となるなら全群に等しい。 -/
theorem closed_eq_top_of_forall_open {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hclosed : IsClosed (H : Set G))
    (hopen : ∀ N : Subgroup G, IsOpen (N : Set G) → H ≤ N → N = ⊤) : H = ⊤ := by
  let C : ClosedSubgroup G := ⟨H, hclosed⟩
  have he := ProfiniteGrp.closedSubgroup_eq_sInf_open C
  apply le_antisymm le_top
  intro g _
  change g ∈ (C : Subgroup G)
  rw [he]
  apply Subgroup.mem_sInf.mpr
  intro N hN
  rw [hopen N hN.1 hN.2]
  exact Subgroup.mem_top g

/-- 任意の開商 modulo で部分群が全元を近似すれば、その閉包は全群。 -/
theorem closure_eq_top_of_open_approximation {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G)
    (happrox : ∀ N : Subgroup G, IsOpen (N : Set G) → H ≤ N →
      ∀ g : G, ∃ h ∈ H, h⁻¹ * g ∈ N) :
    H.topologicalClosure = ⊤ := by
  apply closed_eq_top_of_forall_open _ (Subgroup.isClosed_topologicalClosure H)
  intro N hN hHN
  apply le_antisymm le_top
  intro g _
  obtain ⟨h, hh, hdiff⟩ := happrox N hN ((Subgroup.le_topologicalClosure H).trans hHN) g
  have hhN : h ∈ N := hHN (Subgroup.le_topologicalClosure H hh)
  have hg := N.mul_mem hhN hdiff
  simpa only [mul_inv_cancel_left] using hg

end DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration
```

## STEP 2: `DkMath.FLT.FreyResidueFrobeniusDense`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusOpenQuotient
import DkMath.Lib.RepresentationTheory.ProfiniteOpenGeneration

#print "file: DkMath.FLT.FreyResidueFrobeniusDense"

/-! # 実際の分解群の慣性と Frobenius による稠密生成 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open ValuationInertia
noncomputable section

/-- 同じ局所住所では、慣性と実際の Frobenius は分解群を位相的に生成する。 -/
theorem frobeniusInertia_dense (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ := by
  let : CompactSpace (A.decompositionSubgroup ℚ) := decomposition_compact A
  apply ProfiniteOpenGeneration.closure_eq_top_of_open_approximation
  intro N hN hHN σ
  have hI : A.inertiaSubgroup ℚ ≤ N := le_sup_left.trans hHN
  obtain ⟨m, hm⟩ := exists_frobenius_power_mod_open A hA φ hφ N hN hI σ
  refine ⟨φ ^ m, ?_, hm⟩
  exact (show Subgroup.zpowers φ ≤ A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ from le_sup_right)
    (Subgroup.npow_mem_zpowers φ m)

/-- 同じ住所では、稠密生成する実際の Frobenius を内部構成できる。 -/
theorem exists_frobeniusInertia_dense (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q) :
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧
      (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  exact ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, frobeniusInertia_dense A hA _ hφ⟩

end
end DkMath.FLT.Frey.Source
```

## STEP 3: `DkMath.FLT.FreyResidualCofixedUpperClass`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusResonantLift
import DkMath.FLT.FreyCofixedCyclotomic

#print "file: DkMath.FLT.FreyResidualCofixedUpperClass"

/-! # 元の残余直線と上段商の p 捩れ像
底の直線そのものは上段商で零になる。cofixed 性から E[p] の像は大域的に固定される。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の底に入る上段点は、同じ上段商で零になる。 -/
theorem ResidualCyclicStage.upperClass_eq_zero_of_base
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∈ pointSubgroup S.rationalCurve p L) :
    (QuotientAddGroup.mk' T.upperStage) x = 0 := by
  apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) x).mpr
  exact T.base hx

/-- cofixed 性の下で、元の曲線の p 捩れから来た上段商の類は全 Galois 元で固定される。 -/
theorem ResidualCyclicStage.upperClass_fixed_of_cofixed_p_torsion
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (hx : p • x.val = 0)
    (σ : Field.absoluteGaloisGroup ℚ) :
    T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
      (QuotientAddGroup.mk' T.upperStage) x := by
  let P : S.ResidualSpace := ⟨x.val, hx⟩
  have hdiff : pointAction S.rationalCurve σ x.val - x.val ∈ pointSubgroup S.rationalCurve p L := by
    refine ⟨S.residualRepresentation σ P - P, hcofixed σ P, ?_⟩
    rfl
  change (QuotientAddGroup.mk' T.upperStage)
      (representation S.rationalCurve (p ^ (n + 1 + 1)) σ x) =
    (QuotientAddGroup.mk' T.upperStage) x
  apply QuotientAddGroup.eq.mpr
  change -pointAction S.rationalCurve σ x.val + x.val ∈ T.carrier
  convert T.carrier.neg_mem (T.base hdiff) using 1
  abel

end
end DkMath.FLT.Frey.Source
```

## STEP 4: `DkMath.FLT.FreyResidualObstructionSign`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualCofixedUpperClass

#print "file: DkMath.FLT.FreyResidualObstructionSign"

/-! # 同じ障害値が元の p 捩れから来る場合の符号
代表の存在は明示条件。q≡1 の枝では符号を供給し、q≡-1 の枝との関係を分ける。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ生成元評価値が元の p 捩れで表されるという、明示的な像条件。 -/
def NarrowAbsorptionObstruction.GeneratorValueFromResidual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) : Prop :=
  ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)), p • x.val = 0 ∧
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).val =
      (QuotientAddGroup.mk' T.upperStage) x

/-- cofixed 性の下で、同じ p 捩れ像条件は同じ障害値の全 D 固定性を与える。 -/
theorem NarrowAbsorptionObstruction.generatorValue_fixed_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (σ : A.decompositionSubgroup ℚ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    T.fixedDecompositionAction A σ v = v := by
  obtain ⟨x, hx, hv⟩ := hres
  apply Subtype.ext
  change T.upperQuotientAction σ.val _ = _
  rw [hv]
  exact T.upperClass_fixed_of_cofixed_p_torsion hcofixed x hx σ.val

/-- q≡1 の枝で、同じ p 捩れ像条件から実際の障害核元の D 固定性を得る。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_of_residual_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hq1 : (q : ZMod p) = 1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k := by
  apply (h.decomposition_fixed_iff_resonant_sign hp5 φ hφ).mpr
  exact Or.inl ⟨hq1, h.generatorValue_fixed_of_residual hp5 hcofixed hres φ⟩

/-- 同じ障害値は非零なので、底の残余直線の像からは生じない。 -/
theorem NarrowAbsorptionObstruction.generatorValue_not_from_base
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∈ pointSubgroup S.rationalCurve p L) :
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).val ≠
      (QuotientAddGroup.mk' T.upperStage) x := by
  intro hv
  have hz : T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime
      h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
        (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) = 0 := by
    apply Subtype.ext
    exact hv.trans (T.upperClass_eq_zero_of_base x hx)
  have ho := h.generatorValue_order_eq_prime hp5
  dsimp only at ho
  rw [hz, addOrderOf_zero] at ho
  omega

end
end DkMath.FLT.Frey.Source
```

## STEP 5: `DkMath.Lib.Algebra.PrimeOrderSignSeparation`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.Algebra.PrimeOrderSignSeparation"

/-! # 奇素数位数の元に対する二つの符号の分離 -/
namespace DkMath.Lib.Algebra.PrimeOrderSignSeparation

/-- 位数が 2 より大きい元は、自分自身の負に等しくない。 -/
theorem ne_neg_of_order_gt_two {A : Type*} [AddCommGroup A] (v : A)
    (horder : 2 < addOrderOf v) : v ≠ -v := by
  intro h
  have hz : 2 • v = 0 := by
    calc
      2 • v = v + v := two_nsmul v
      _ = v + -v := congrArg (fun z => v + z) h
      _ = 0 := add_neg_cancel v
  have hd : addOrderOf v ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 同じ元について固定作用と符号反転作用は両立しない。 -/
theorem fixed_ne_neg_of_order_gt_two {A : Type*} [AddCommGroup A] (v w : A)
    (horder : 2 < addOrderOf v) (hfix : w = v) : w ≠ -v := by
  rw [hfix]
  exact ne_neg_of_order_gt_two v horder

end DkMath.Lib.Algebra.PrimeOrderSignSeparation
```

## STEP 6: `DkMath.FLT.FreyResidualObstructionMinusBranch`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualObstructionSign
import DkMath.Lib.Algebra.PrimeOrderSignSeparation

#print "file: DkMath.FLT.FreyResidualObstructionMinusBranch"

/-! # 残余 p 捩れ像に入る障害値と負の共鳴枝
同じ値が p 捩れ像に入るという条件の下で、負の符号枝では D 固定性が成立しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open DkMath.Lib.Algebra.PrimeOrderSignSeparation
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害値が残余 p 捩れから来れば、その固定作用は符号反転と異なる。 -/
theorem NarrowAbsorptionObstruction.generatorValue_not_neg_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (φ : A.decompositionSubgroup ℚ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    T.fixedDecompositionAction A φ v ≠ -v := by
  have ho := h.generatorValue_order_eq_prime hp5
  dsimp only at ho
  apply fixed_ne_neg_of_order_gt_two _ _ (by rw [ho]; omega)
  exact h.generatorValue_fixed_of_residual hp5 hcofixed hres φ

/-- 負の共鳴枝では、同じ p 捩れ像条件は障害核元の D 固定性を排除する。 -/
theorem NarrowAbsorptionObstruction.not_decomposition_fixed_of_residual_minus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hqneg : (q : ZMod p) = -1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ¬ ∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k := by
  dsimp only
  intro hD
  have he := (h.frobenius_fixed_criterion hp5 φ hφ).mp (hD φ)
  rw [h.generatorValue_q_smul_minus hp5 hqneg] at he
  exact h.generatorValue_not_neg_of_residual hp5 hcofixed hres φ he

end
end DkMath.FLT.Frey.Source
```

## STEP 7: `DkMath.FLT.FreyResidualObstructionBranches`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualObstructionMinusBranch

#print "file: DkMath.FLT.FreyResidualObstructionBranches"

/-! # 実際の残余 p 捩れ像の下での共鳴枝判定
残余 p 捩れ代表の存在と大域 cofixed 性を保持する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ残余 p 捩れ像の下では、D 固定性は q≡1 の枝とちょうど一致する。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_plus_of_residual
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔ (q : ZMod p) = 1 := by
  constructor
  · intro hD
    rcases h.resonance with hplus | hminus
    · exact hplus
    · exact (h.not_decomposition_fixed_of_residual_minus hp5 hcofixed hres hminus φ hφ hD).elim
  · exact fun hplus => h.decomposition_fixed_of_residual_plus hp5 hcofixed hres hplus φ hφ

/-- 正の共鳴枝と同じ p 捩れ像から、元の連続代表を持つ非零 D 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_residual_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (hres : h.GeneratorValueFromResidual hp5) (hq1 : (q : ZMod p) = 1)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
          (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    (h.decomposition_fixed_of_residual_plus hp5 hcofixed hres hq1 φ hφ)

end
end DkMath.FLT.Frey.Source
```
