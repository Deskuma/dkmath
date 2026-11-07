/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelTameDescent

#print "file: DkMath.FLT.FreyKernelCommonTameQuotient"

/-!
# 核全体の全指標に共通する、実際の有限な馴分岐商

同じ J=I/W から全ての核指標の値を同時に記録する。核 K と F の実際の有限性から
共通核は開で、商は有限。有限商の巡回性や一元生成性は主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の Q/F との同型から、実際の係数核全体は有限である。 -/
theorem ResidualCyclicStage.fixedKernel_finite : Finite (T.fixedH1CoefficientKernel A) := by
  obtain ⟨s, _, hc⟩ := T.fixedKernel_prime_power_profile A hp5 hq hqp haddr hA
  exact Nat.finite_of_card_ne_zero (hc.trans_ne (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- 同じ J の元について、同じ全ての核指標の値を同時に記録する準同型。 -/
def ResidualCyclicStage.fixedKernelTameFamily :
    tameInertiaQuotient A →* (T.fixedH1CoefficientKernel A → Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  MonoidHom.pi (fun k => T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k)

/-- 共通核への所属は、全ての同じ核指標の値が 1 になること。 -/
theorem ResidualCyclicStage.mem_fixedKernelTameFamily_kernel (t : tameInertiaQuotient A) :
    t ∈ (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker ↔
      ∀ k, T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k t = 1 := by
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) t = 1 ↔ _
  exact ⟨fun he k => congrFun he k, fun he => funext he⟩

/-- 全ての同じ馴分岐値の族も、元の商位相から連続。 -/
theorem ResidualCyclicStage.fixedKernelTameFamily_continuous :
    Continuous (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) :=
  continuous_pi fun k => T.fixedKernelTameCharacter_continuous A hp5 hq hqp haddr hA k

/-- K の有限性と離散有限係数により、この共通正規核は開。 -/
theorem ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen :
    IsOpen ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker : Set (tameInertiaQuotient A)) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  change IsOpen ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA) ⁻¹' {1})
  exact (isOpen_discrete _).preimage (T.fixedKernelTameFamily_continuous A hp5 hq hqp haddr hA)

/-- 同じ全指標の共通核で割った、実際の J の群商。 -/
abbrev ResidualCyclicStage.fixedKernelCommonTameQuotient :=
  (tameInertiaQuotient A) ⧸ (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker

/-- 第一同型定理と実際の有限係数により、共通馴分岐商は有限。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameQuotient_finite :
    Finite (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA)).symm.toEquiv

/-- 全指標の値を、同じ実際の有限商上へ因子化する。 -/
def ResidualCyclicStage.fixedKernelCommonTameValues :
    T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA →*
      (T.fixedH1CoefficientKernel A → Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  QuotientGroup.lift (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) le_rfl

/-- 共通商でも、元の同じ指標の同じ値を保つ。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_mk (t : tameInertiaQuotient A)
    (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA (QuotientGroup.mk t) k =
      T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k t := rfl

/-- 有限商上の全ての評価が一致すれば、元の係数核の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_separates
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ t, T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA t x =
      T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA t y) : x = y := by
  apply T.fixedKernelEvaluation_separates A x y
  intro σ
  exact congrArg Multiplicative.toAdd (he (QuotientGroup.mk (QuotientGroup.mk σ)))

end
end DkMath.FLT.Frey.Source
