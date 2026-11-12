# NOTE-032 教科書：実際の局所 Frobenius による有限作用像の生成

実際の q 上の付値環 A と分解群 D、慣性 I、同じ有限係数核 K を固定する。
このノートの各 Lean ブロックは対応する production ファイルの全文であり、import の直後に
`#print "file: ..."` を保持する。

## 7 ステップと証明の道筋

1. `ValuationResidueAlgebraicClosure`: 元の付値環の剰余体 κ が素体 Fq 上代数閉包となる。
   代数的整数の単元分母表示から代数性を導き、単項多項式を持ち上げて代数閉性を得る。
2. `AlgebraicFiniteFieldApproximation`: Fq 上の代数拡大の有限個の元が生成する中間体は有限。
   そこへ自己同型を制限すると、全ての選択元上で一つの Frobenius 冪に一致する。
3. `FreyResidueFrobeniusApproximation`: 同じ実際の D 作用について、任意の有限個の剰余値上で
   任意の σ を同じ局所 Frobenius φ の冪で近似する。
4. `CompactFiniteDetection`: コンパクト空間の開条件が値の不一致で分離されるなら、
   その補集合の有限部分被覆により有限個の値で検出できる。
5. `FreyResidueOpenKernelDetection`: D の Krull コンパクト性と剰余値の開な不一致条件から、
   I を含む任意の開部分群 N を有限個の実際の剰余値で検出する。
6. `FreyResidueFrobeniusOpenQuotient`: 3 と 5 を組み合わせ、
   各 σ に対して `(φ ^ m)⁻¹ * σ ∈ N` を得る。元の開作用核に適用して、
   有限作用像生成 `himage` を元の住所から供給する。
7. `FreyResidueFrobeniusResonantLift`: `himage` と `horbit` を内部供給し、
   同じ障害元の固定性を符号条件で判定し、同じ非零通常 H¹(D,F) 類を得る。
   cocycle の連続性は別途結論として保持する。

有限個の剰余値上の近似は、D/I と全剰余 Galois 群との位相群同型の主張を必要としない。
同じ q と A を固定した局所定理である。模範解答の一般的な剰余体同定の証明を参照した。
また、その大域的 `FrobeniusPowerDense` は素数・場所・共役を変える別の命題である。

## 残る数学的境界

有限作用像生成と各障害元の軌道条件は、既存の素数、住所、Frobenius の条件から導出された。
`hsign`、すなわち同じ障害値に対する実際の Frey Frobenius の符号は未供給である。
非零 D 類から大域 Selmer 条件への接続、hclass の消滅、共鳴障害の排除、
無条件一般 hno は未完成である。


## STEP 1: `DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure`

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime.lean,
and P2M/Sol/S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: expose algebraicity and algebraic closure separately; reuse DkMath fraction and characteristic lemmas.
-/

import DkMath.Lib.NumberTheory.ValuationFrobenius
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import Mathlib.FieldTheory.Finite.Extension

#print "file: DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure"

/-! # 実際の付値環の剰余体は F_q の代数閉包
整数閉包の元と単元分母による分数表示を、同じ付値環の剰余体へ写す。 -/
namespace DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
open ValuationInertia ValuationFrobenius.PlaceTransitivity
open Polynomial

/-- 代数閉体の付値環の剰余体は代数閉体。 -/
theorem residue_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  obtain ⟨P, hP, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts p).mpr fun n => hsurj (p.coeff n)) hp
  have hdegL : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A L), hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdegL
  have hint : IsIntegral A x := ⟨P, hmon, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hPa : P.eval a = 0 := by
    apply IsFractionRing.injective A L
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]
    exact hx
  change p.IsRoot (IsLocalRing.residue A a)
  rw [← hP, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply, hPa, map_zero]

/-- 整数閉包の元の剰余は素体上で代数的。 -/
theorem integral_residue_isAlgebraic (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (z : Zbar) :
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
    letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
    IsAlgebraic (ZMod q) (IsLocalRing.residue A ⟨z, coe_mem A z⟩) := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  obtain ⟨P, hPmon, hPz⟩ := z.2
  refine ⟨P.map (Int.castRingHom (ZMod q)), (hPmon.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (ZMod q) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod q)) =
      algebraMap ℤ (IsLocalRing.ResidueField A) from RingHom.ext_int _ _,
    ← Polynomial.aeval_def,
    show IsLocalRing.residue A ⟨z, coe_mem A z⟩ =
      (IsLocalRing.residue A).toIntAlgHom ⟨z, coe_mem A z⟩ from rfl,
    Polynomial.aeval_algHom_apply]
  have h0 : Polynomial.aeval (⟨z, coe_mem A z⟩ : A) P = 0 := by
    have h1 : algebraMap A (AlgebraicClosure ℚ) (Polynomial.aeval (⟨z, coe_mem A z⟩ : A) P) =
        P.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ) := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (algebraMap ℤ A))
          (algebraMap ℤ (AlgebraicClosure ℚ))]
      rfl
    have h' : ((Polynomial.aeval (⟨z, coe_mem A z⟩ : A) P : A) : AlgebraicClosure ℚ) = 0 :=
      h1.trans hPz
    exact_mod_cast h'
  rw [h0, map_zero]

/-- 実際の剰余体の全元は、q 元の素体上代数的である。 -/
theorem residue_isAlgebraic (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q) :
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
    letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
    Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField A) := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨y, s, hs, hys⟩ :=
    ValuationInertiaLift.FractionRepresentation.exists_integral_fraction A (Fact.out : q.Prime) hA a a.2
  have hmul : a * ⟨s, coe_mem A s⟩ = ⟨y, coe_mem A y⟩ := Subtype.ext hys
  have hs0 : IsLocalRing.residue A ⟨s, coe_mem A s⟩ ≠ 0 := by
    intro hz
    apply hs
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
    rwa [← ValuationSubring.coe_mem_nonunits_iff] at hm
  have hx : IsLocalRing.residue A a =
      IsLocalRing.residue A ⟨y, coe_mem A y⟩ *
        (IsLocalRing.residue A ⟨s, coe_mem A s⟩)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hmul]
  rw [hx]
  exact (integral_residue_isAlgebraic A hA y).mul (integral_residue_isAlgebraic A hA s).inv

/-- 実際の剰余体を同じ素体上の代数閉包と同定する。 -/
theorem residue_isAlgClosure (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q) :
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
    letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
    IsAlgClosure (ZMod q) (IsLocalRing.ResidueField A) := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  exact ⟨residue_isAlgClosed A, residue_isAlgebraic A hA⟩

end DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
```

## STEP 2: `DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
import Mathlib.FieldTheory.Finite.Extension

#print "file: DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation"

/-! # 有限体上の代数拡大での有限個の値の Frobenius 近似
有限集合の生成する有限中間体に両自己同型を制限する。 -/
namespace DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]

/-- 有限個の値では、任意の k 自己同型は一つの Frobenius 冪と一致する。 -/
theorem finite_values_pow (σ : F ≃ₐ[k] F) (s : Finset F) :
    ∃ m : ℕ, ∀ x ∈ s, σ x = x ^ (Fintype.card k ^ m) := by
  classical
  let E := IntermediateField.adjoin k (s : Set F)
  let : Finite (s : Set F) := s.finite_toSet.to_subtype
  let : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let : Normal k E := by infer_instance
  let σE : E ≃ₐ[k] E := σ.restrictNormal E
  obtain ⟨m, _, hm⟩ := FiniteFieldFrobeniusImage.exists_bounded_power k E σE
  refine ⟨m, ?_⟩
  intro x hx
  let xE : E := ⟨x, IntermediateField.subset_adjoin k (s : Set F) hx⟩
  have h := congrArg (fun f : E ≃ₐ[k] E => (f xE : F)) hm
  have hpow : ((FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ m) xE : F) =
      x ^ (Fintype.card k ^ m) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    rfl
  rw [hpow] at h
  simpa [σE, xE, AlgEquiv.restrictNormal_apply] using h.symm

/-- 同じ Frobenius 自己同型の冪として、有限個の値を同時に近似できる。 -/
theorem finite_values_frobenius (σ φ : F ≃ₐ[k] F)
    (hφ : ∀ x : F, φ x = x ^ Fintype.card k) (s : Finset F) :
    ∃ m : ℕ, ∀ x ∈ s, σ x = (φ ^ m) x := by
  have hφeq : φ = FiniteField.frobeniusAlgEquivOfAlgebraic k F := by
    ext x
    exact hφ x
  obtain ⟨m, hm⟩ := finite_values_pow k F σ s
  refine ⟨m, fun x hx => ?_⟩
  rw [hφeq, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  exact hm x hx

end
end DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation
```

## STEP 3: `DkMath.FLT.FreyResidueFrobeniusApproximation`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFiniteActionFactor
import DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
import DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation

#print "file: DkMath.FLT.FreyResidueFrobeniusApproximation"

/-! # 同じ局所住所での有限剰余値 Frobenius 近似
同じ q 上の付値環と元の D 作用について、有限個の剰余値を同時に近似する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.NumberTheory.ValuationResidueAlgebraicClosure
open ValuationInertia
noncomputable section

/-- 実際の剰余作用は q 元の素体を固定する。 -/
def residueFieldAlgAction (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q) :
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
    letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
    A.decompositionSubgroup ℚ →* (IsLocalRing.ResidueField A ≃ₐ[ZMod q] IsLocalRing.ResidueField A) := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  refine { toFun := fun σ => AlgEquiv.ofRingEquiv (f := residueFieldAction A σ) ?_
           map_one' := ?_
           map_mul' := ?_ }
  · intro z
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    simp
  · ext x
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f x) (map_one (residueFieldAction A))
  · intro σ τ
    ext x
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f x) (map_mul (residueFieldAction A) σ τ)

/-- 元の D の剰余作用と、素体上の自己同型としての作用は同じ値を与える。 -/
theorem residueFieldAlgAction_apply (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (σ : A.decompositionSubgroup ℚ) (x : IsLocalRing.ResidueField A) :
    residueFieldAlgAction A hA σ x = σ • x := rfl

/-- 実際の D の任意の元は、有限個の剰余値上で同じ Frobenius の冪に一致する。 -/
theorem residueFinite_frobenius_approx (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (σ : A.decompositionSubgroup ℚ) (s : Finset (IsLocalRing.ResidueField A)) :
    ∃ m : ℕ, ∀ x ∈ s, σ • x = (φ ^ m) • x := by
  let : CharP (IsLocalRing.ResidueField A) q :=
    ValuationPrimeSupport.charP_residueField A (Fact.out : q.Prime) hA
  let : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  let : Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField A) := residue_isAlgebraic A hA
  have hf : ∀ x : IsLocalRing.ResidueField A,
      residueFieldAlgAction A hA φ x = x ^ Fintype.card (ZMod q) := by
    intro x
    rw [ZMod.card]
    exact residueFieldAction_frobenius A φ hφ x
  obtain ⟨m, hm⟩ := AlgebraicFiniteFieldApproximation.finite_values_frobenius
    (ZMod q) (IsLocalRing.ResidueField A) (residueFieldAlgAction A hA σ)
    (residueFieldAlgAction A hA φ) hf s
  refine ⟨m, fun x hx => ?_⟩
  have he := hm x hx
  rw [← map_pow (residueFieldAlgAction A hA)] at he
  exact he

end
end DkMath.FLT.Frey.Source
```

## STEP 4: `DkMath.Lib.RepresentationTheory.CompactFiniteDetection`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Topology.Compactness.Compact

#print "file: DkMath.Lib.RepresentationTheory.CompactFiniteDetection"

/-! # コンパクト性による有限個の値での開条件の検出
開集合の外の各点を少なくとも一つの値で検出できれば、有限個で同時に検出できる。 -/
namespace DkMath.Lib.RepresentationTheory.CompactFiniteDetection

/-- コンパクトな空間上の開条件を、開な非一致集合の有限個で検出する。 -/
theorem exists_finite_detecting_set {G X : Type*} [TopologicalSpace G] [CompactSpace G]
    (N : Set G) (hN : IsOpen N) (act : G → X → X)
    (hopen : ∀ x, IsOpen {g | act g x ≠ x})
    (hseparate : ∀ g ∉ N, ∃ x, act g x ≠ x) :
    ∃ s : Finset X, ∀ g, (∀ x ∈ s, act g x = x) → g ∈ N := by
  classical
  have hc : IsCompact Nᶜ := hN.isClosed_compl.isCompact
  have hcover : Nᶜ ⊆ ⋃ x : X, {g | act g x ≠ x} := by
    intro g hg
    obtain ⟨x, hx⟩ := hseparate g hg
    exact Set.mem_iUnion.mpr ⟨x, hx⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x => {g | act g x ≠ x}) hopen hcover
  refine ⟨s, fun g hg => ?_⟩
  by_contra hnot
  have hmem := hs hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
  obtain ⟨x, hx, hne⟩ := hmem
  exact hne (hg x hx)

end DkMath.Lib.RepresentationTheory.CompactFiniteDetection
```

## STEP 5: `DkMath.FLT.FreyResidueOpenKernelDetection`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusApproximation
import DkMath.Lib.NumberTheory.InertiaKrullClosed
import DkMath.Lib.RepresentationTheory.CompactFiniteDetection

#print "file: DkMath.FLT.FreyResidueOpenKernelDetection"

/-! # 実際の開作用核を有限個の剰余値で検出する
分解群の Krull コンパクト性と剰余作用の各軌道の連続性を用いる。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open ValuationInertia
noncomputable section

/-- 実際の分解群は代数閉包のコンパクト Galois 群の閉部分群。 -/
theorem decomposition_compact (A : ValuationSubring (AlgebraicClosure ℚ)) :
    CompactSpace (A.decompositionSubgroup ℚ) := by
  have h := InertiaStability.isClosed_decompositionSubgroup (K := ℚ) A
  exact h.isClosedEmbedding_subtypeVal.compactSpace

/-- 一つの剰余値を動かす分解群の元は、元の Krull 位相で開集合をなす。 -/
theorem residue_moved_isOpen (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : IsLocalRing.ResidueField A) :
    IsOpen {σ : A.decompositionSubgroup ℚ | σ • x ≠ x} := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have he : {σ : A.decompositionSubgroup ℚ |
      σ • IsLocalRing.residue A a ≠ IsLocalRing.residue A a} =
      Subtype.val ⁻¹' {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
        ¬ A.valuation (σ a - a) < 1} := by
    ext σ
    change (σ • IsLocalRing.residue A a ≠ IsLocalRing.residue A a) ↔
      ¬ A.valuation (σ.val a - a) < 1
    have hk : (σ • IsLocalRing.residue A a = IsLocalRing.residue A a) ↔
        A.valuation (σ.val a - a) < 1 := by
      rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
        IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      rfl
    exact not_congr hk
  rw [he]
  exact (InertiaClosed.isOpen_setOf_apply (K := ℚ)
    (fun y => ¬ A.valuation (y - a) < 1) (a : AlgebraicClosure ℚ)).preimage continuous_subtype_val

/-- 慣性を含む任意の開部分群は、有限個の実際の剰余値の固定性で検出される。 -/
theorem exists_finite_residue_detection (A : ValuationSubring (AlgebraicClosure ℚ))
    (N : Subgroup (A.decompositionSubgroup ℚ))
    (hN : IsOpen (N : Set (A.decompositionSubgroup ℚ)))
    (hI : A.inertiaSubgroup ℚ ≤ N) :
    ∃ s : Finset (IsLocalRing.ResidueField A),
      ∀ σ : A.decompositionSubgroup ℚ, (∀ x ∈ s, σ • x = x) → σ ∈ N := by
  let : CompactSpace (A.decompositionSubgroup ℚ) := decomposition_compact A
  apply CompactFiniteDetection.exists_finite_detecting_set (N : Set (A.decompositionSubgroup ℚ)) hN
    (fun σ x => σ • x) (residue_moved_isOpen A)
  intro σ hσ
  by_contra hnone
  push Not at hnone
  apply hσ
  apply hI
  change residueFieldAction A σ = 1
  ext x
  exact hnone x

end
end DkMath.FLT.Frey.Source
```

## STEP 6: `DkMath.FLT.FreyResidueFrobeniusOpenQuotient`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueOpenKernelDetection

#print "file: DkMath.FLT.FreyResidueFrobeniusOpenQuotient"

/-! # 実際の局所 Frobenius による開商の生成
有限剰余値近似とコンパクト性から、慣性を含む任意の開部分群 modulo の冪表示を得る。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section

/-- 慣性を含む任意の開部分群 modulo で、任意の D 元は同じ局所 Frobenius の冪。 -/
theorem exists_frobenius_power_mod_open (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (N : Subgroup (A.decompositionSubgroup ℚ))
    (hN : IsOpen (N : Set (A.decompositionSubgroup ℚ)))
    (hI : A.inertiaSubgroup ℚ ≤ N) (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, (φ ^ m)⁻¹ * σ ∈ N := by
  obtain ⟨s, hs⟩ := exists_finite_residue_detection A N hN hI
  obtain ⟨m, hm⟩ := residueFinite_frobenius_approx A hA φ hφ σ s
  refine ⟨m, hs _ ?_⟩
  intro x hx
  rw [mul_smul, hm x hx, inv_smul_smul]

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の有限 K 作用像の各元は、実際の Frobenius 像の自然数冪である。 -/
theorem ResidualCyclicStage.finiteDecomposition_power_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ =
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA φ) ^ m := by
  let : Fact q.Prime := ⟨hq⟩
  let π := T.finiteDecompositionProjection A hp5 hq hqp haddr hA
  have hker : IsOpen (π.ker : Set (A.decompositionSubgroup ℚ)) := by
    change IsOpen (((QuotientGroup.mk' (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker).ker :
      Subgroup (A.decompositionSubgroup ℚ)) : Set (A.decompositionSubgroup ℚ))
    rw [QuotientGroup.ker_mk']
    exact T.kernelDecompositionUnits_kernel_isOpen A hp5 hq hqp haddr hA
  obtain ⟨m, hm⟩ := exists_frobenius_power_mod_open A hA φ hφ π.ker hker
    (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA) σ
  change π ((φ ^ m)⁻¹ * σ) = 1 at hm
  rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at hm
  exact ⟨m, hm.symm⟩

/-- 元の住所から、以前は明示入力だった有限像生成性 `himage` を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    ∀ σ : A.decompositionSubgroup ℚ,
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈
        Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) := by
  intro σ
  obtain ⟨m, hm⟩ := T.finiteDecomposition_power_of_frobenius A hp5 hq hqp haddr hA φ hφ σ
  rw [hm]
  exact Subgroup.npow_mem_zpowers _ _

end
end DkMath.FLT.Frey.Source
```

## STEP 7: `DkMath.FLT.FreyResidueFrobeniusResonantLift`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFrobeniusOpenQuotient
import DkMath.FLT.FreyOrbitResonantLift

#print "file: DkMath.FLT.FreyResidueFrobeniusResonantLift"

/-! # 実際の局所 Frobenius から同じ障害元の固定性判定へ
有限像生成と軌道条件を内部供給する。共鳴符号の算術的証明は別途必要。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 同じ K の各元に対し、軌道条件は実際の局所データから供給される。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k :=
  T.kernelOrbitGenerated_of_finite_image A hp5 hq hqp haddr hA φ
    (T.finiteDecomposition_generated_of_frobenius A hp5 hq hqp haddr hA φ hφ) k

/-- 同じ K の D 固定性は、実際の Frobenius 一元による固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  T.kernel_fixed_iff_frobenius_of_orbit A hp5 hq hqp haddr hA φ k
    (T.kernelOrbitGenerated_of_frobenius A hp5 hq hqp haddr hA φ hφ k)

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 軌道生成を外部入力にせず、同じ障害元の D 固定性を共鳴符号で判定する。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) :=
  h.decomposition_fixed_iff_resonant_sign_of_orbit hp5 φ hφ
    (T.kernelOrbitGenerated_of_frobenius A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over φ hφ _)

/-- 共鳴符号から、同じ連続代表を持つ非零通常 H¹(D,F) 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_resonant_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hsign : let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v)) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
          (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    ((h.decomposition_fixed_iff_resonant_sign hp5 φ hφ).mpr hsign)

end
end DkMath.FLT.Frey.Source
```
