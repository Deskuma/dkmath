# NOTE-032 教科書：実際の剰余作用と障害核元の軌道判定

このノートの Lean ブロックは、各 production ファイルの全文である。先頭の import と直後の
`#print "file: DkMath.FLT.…"` を含むので、単独コピーでもモジュール名を確認できる。
コードは実際の Frey Source、同じ付値環 A、同じ障害核元 k と同じ連続 D 類を使う。

## 7 ステップ

1. 元の分解群 D の剰余体作用を明示する。
2. 作用核が元の慣性 I と一致し、D/I が剰余自己同型群へ忠実に入ることを証明する。
3. 実際の Frobenius 持ち上げは同じ剰余体上で q 乗として作用する。
4. 元の有限 K 作用を D/I からの全射として因子化する。
5. K 全体の有限像生成から、特定の k の軌道生成を導き、Frobenius 持ち上げ選択からの独立性を証明する。
6. k の軌道生成の下で D 固定性を一元の固定性および同じ γ の q 固有値へ還元する。
7. 元の共鳴符号を用い、同じ連続・非零 H¹(D,F) 類へ条件付きで到達する。

`KernelOrbitGenerated` は k の軌道だけを制御するため、K 全体の有限作用像生成より弱い。
実際の剰余体の有限部分拡大への因子化、軌道条件、Frobenius 符号は元の住所からまだ供給されない。
局所類から大域 Selmer への比較、hclass、無条件一般 hno も未完成である。
模範解答の `FrobeniusPowerDense` は素数・場所・共役を変える大域条件であり、
ここで固定した q と A の局所生成を直接与えるものではない。


## Lean ファイル 1: `DkMath.FLT.FreyResidueFiniteActionFactor`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteFrobeniusImage

#print "file: DkMath.FLT.FreyResidueFiniteActionFactor"

/-! # 実際の剰余作用と有限 K 作用の因子化
同じ付値環の剰余自己同型作用を使う。有限剰余拡大への因子化や Frobenius 生成性はここでは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section

/-- 同じ付値環の剰余体上の実際の分解群作用。 -/
def residueFieldAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    A.decompositionSubgroup ℚ →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (IsLocalRing.ResidueField A)

/-- この作用の核は、定義上、元の慣性群そのものである。 -/
theorem residueFieldAction_ker (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (residueFieldAction A).ker = A.inertiaSubgroup ℚ := rfl

/-- 元の D/I は実際の剰余自己同型群に忠実に作用する。 -/
def residueFieldFaithfulAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* RingAut (IsLocalRing.ResidueField A) :=
  QuotientGroup.lift _ (residueFieldAction A) (le_of_eq (residueFieldAction_ker A).symm)

/-- 忠実性は慣性核を割ったことから従う。 -/
theorem residueFieldFaithfulAction_injective (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective (residueFieldFaithfulAction A) := by
  exact QuotientGroup.kerLift_injective (residueFieldAction A)

/-- 実際の Frobenius 持ち上げは、この同じ剰余体上で q 乗として作用する。 -/
theorem residueFieldAction_frobenius (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} (φ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (x : IsLocalRing.ResidueField A) :
    (residueFieldAction A φ) x = x ^ q := by
  change φ • x = x ^ q
  have he : (⟨φ.val, hφ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) = φ :=
    Subtype.ext rfl
  rw [← he]
  exact hφ.smul_residue_eq x

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 同じ有限 K 作用は、実際の剰余群 D/I を通って因子化する。 -/
def ResidualCyclicStage.finiteResidueProjection :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →*
      T.finiteDecompositionImage A hp5 hq hqp haddr hA :=
  QuotientGroup.lift _ (T.finiteDecompositionProjection A hp5 hq hqp haddr hA)
    (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA)

/-- 元の D からの有限作用射影は、D/I を経由した射影に等しい。 -/
theorem ResidualCyclicStage.finiteResidueProjection_comp :
    (T.finiteResidueProjection A hp5 hq hqp haddr hA).comp
      (QuotientGroup.mk' (A.inertiaSubgroup ℚ)) =
      T.finiteDecompositionProjection A hp5 hq hqp haddr hA := by
  ext σ
  rfl

/-- この D/I からの射影は、実際の有限作用像へ全射である。 -/
theorem ResidualCyclicStage.finiteResidueProjection_surjective :
    Function.Surjective (T.finiteResidueProjection A hp5 hq hqp haddr hA) := by
  intro z
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨QuotientGroup.mk' (A.inertiaSubgroup ℚ) σ, rfl⟩

end
end DkMath.FLT.Frey.Source
```

## Lean ファイル 2: `DkMath.FLT.FreyKernelOrbitCriterion`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueFiniteActionFactor
import DkMath.FLT.FreyFiniteImageFixedCriterion
import DkMath.FLT.FreyFrobeniusLiftIndependence

#print "file: DkMath.FLT.FreyKernelOrbitCriterion"

/-! # 同じ障害核元ひとつの有限軌道による判定
K 全体の有限作用像の生成より弱い条件を、元の作用で表す。 -/
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

/-- 特定の k に限った D 軌道が、同じ Frobenius の非負冪軌道に含まれる条件。 -/
def ResidualCyclicStage.KernelOrbitGenerated
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A) : Prop :=
  ∀ σ : A.decompositionSubgroup ℚ, ∃ m : ℕ,
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k =
      (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ ^ m) k

/-- K 全体の有限作用像生成は、各 k の軌道生成を与える。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_of_finite_image
    (φ : A.decompositionSubgroup ℚ)
    (himage : ∀ σ : A.decompositionSubgroup ℚ,
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈
        Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ))
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k := by
  intro σ
  obtain ⟨m, _, hm⟩ := T.finiteDecomposition_bounded_action_power A hp5 hq hqp haddr hA φ himage σ
  exact ⟨m, congrArg (fun f : Module.End ℤ (T.fixedH1CoefficientKernel A) => f k) hm⟩

/-- 同じ q-Frobenius の持ち上げを替えても、この k の軌道条件は変わらない。 -/
theorem ResidualCyclicStage.kernelOrbitGenerated_frobenius_iff
    (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k ↔
      T.KernelOrbitGenerated A hp5 hq hqp haddr hA ψ k := by
  unfold ResidualCyclicStage.KernelOrbitGenerated
  rw [T.kernelFrobenius_action_eq A hp5 hq hqp haddr hA φ ψ hφ hψ]

/-- Frobenius が同じ k を固定し、その軌道が生成されれば D 全体が k を固定する。 -/
theorem ResidualCyclicStage.kernel_fixed_of_orbit
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k)
    (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  let f : Module.End ℤ (T.fixedH1CoefficientKernel A) :=
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ
  have hp : ∀ m : ℕ, (f ^ m) k = k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      calc (f ^ (m + 1)) k = (f ^ m) (f k) :=
            congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (pow_succ f m)
        _ = (f ^ m) k := congrArg (fun z : T.fixedH1CoefficientKernel A => (f ^ m) z) hfixed
        _ = k := ih
  intro σ
  obtain ⟨m, hm⟩ := horbit σ
  exact hm.trans (hp m)

/-- 同じ k の D 固定性は、軌道条件の下で単一 Frobenius 固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_frobenius_of_orbit
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  ⟨fun h => h φ, T.kernel_fixed_of_orbit A hp5 hq hqp haddr hA φ k horbit⟩

/-- 軌道条件の下で元の γ による Frobenius 固有値判定を得る。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_eigenvalue_of_orbit
    (φ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A)
    (horbit : T.KernelOrbitGenerated A hp5 hq hqp haddr hA φ k) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (T.kernel_fixed_iff_frobenius_of_orbit A hp5 hq hqp haddr hA φ k horbit).trans
    (T.kernelFrobenius_fixed_iff A hp5 hq hqp haddr hA φ hφ k)

end
end DkMath.FLT.Frey.Source
```

## Lean ファイル 3: `DkMath.FLT.FreyOrbitResonantLift`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelOrbitCriterion
import DkMath.FLT.FreyFiniteImageResonantLift

#print "file: DkMath.FLT.FreyOrbitResonantLift"

/-! # 同じ障害元の軌道条件と共鳴符号
有限作用像全体を生成する仮定は外せるが、軌道条件と符号の算術的証明はまだ必要。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害元の軌道条件の下で、D 固定性は元の共鳴符号条件と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_orbit
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (horbit : T.KernelOrbitGenerated A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      h.lies_over φ
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
        A h.lies_over ⟨y, h.killed⟩)) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime
        h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.kernel_fixed_iff_eigenvalue_of_orbit A hp5 h.prime
    h.ne_torsion_prime (Or.inr h.support) h.lies_over φ hφ
    (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) horbit
  constructor
  · intro hD
    have hv := he.mp hD
    rcases h.resonance with hplus | hminus
    · exact Or.inl ⟨hplus, hv.trans (h.generatorValue_q_smul_plus hp5 hplus)⟩
    · exact Or.inr ⟨hminus, hv.trans (h.generatorValue_q_smul_minus hp5 hminus)⟩
  · intro hs
    apply he.mpr
    rcases hs with ⟨hplus, hv⟩ | ⟨hminus, hv⟩
    · exact hv.trans (h.generatorValue_q_smul_plus hp5 hplus).symm
    · exact hv.trans (h.generatorValue_q_smul_minus hp5 hminus).symm

/-- 軌道条件と符号から、同じ連続な非零 D コホモロジー類を得る。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_orbit_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (horbit : T.KernelOrbitGenerated A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
      h.lies_over φ
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
        A h.lies_over ⟨y, h.killed⟩))
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
    ((h.decomposition_fixed_iff_resonant_sign_of_orbit hp5 φ hφ horbit).mpr hsign)

end
end DkMath.FLT.Frey.Source
```
