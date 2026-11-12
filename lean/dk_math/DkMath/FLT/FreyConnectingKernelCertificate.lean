/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelPrimeOrder

#print "file: DkMath.FLT.FreyConnectingKernelCertificate"

/-!
# 同じ係数核の濃度と位数 p の巡回部分群の算術証明書

核全体は同じ Q/F と同型。濃度積と p 冪上界を内部計算し、元の同じ証明書へ接続する。
-/
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

/-- 元の同じ剰余類を Q/F の同型へ渡すと、元の同じ核元になる。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA
      (T.fixedCosetInvariant hp5 hq hqp haddr A hA x).val =
      T.fixedCosetKernelElement hp5 hq hqp haddr A hA x := rfl

include hp5 hq hqp haddr hA in
/-- 実際の係数核の濃度と元の固定部分群の濃度の積は、元の Q の濃度 p^(n+3)。 -/
theorem ResidualCyclicStage.fixedKernel_card_mul_fixed :
    Nat.card (T.fixedH1CoefficientKernel A) * Nat.card (T.inertiaFixedUpperQuotient A) = p ^ (n + 3) := by
  have he := Nat.card_congr (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).toEquiv
  calc
    Nat.card (T.fixedH1CoefficientKernel A) * Nat.card (T.inertiaFixedUpperQuotient A) =
        Nat.card (T.fixedQuotientCoefficient A) * Nat.card (T.inertiaFixedUpperQuotient A) := by rw [he]
    _ = Nat.card T.upperQuotient :=
      (T.inertiaFixedUpperQuotient A).card_eq_card_quotient_mul_card_addSubgroup.symm
    _ = p ^ (n + 3) := T.upperQuotient_card

include hp5 hq hqp haddr hA in
/-- 同じ係数核全体の濃度は、上界 n+3 の p 冪。 -/
theorem ResidualCyclicStage.fixedKernel_prime_power_profile :
    ∃ s ≤ n + 3, Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  have hd : Nat.card (T.fixedH1CoefficientKernel A) ∣ p ^ (n + 3) :=
    ⟨Nat.card (T.inertiaFixedUpperQuotient A), (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm⟩
  exact (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd

end

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の位数 p 核元により、核濃度の p 冪指数は正。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have ho : addOrderOf k = p := h.fixedKernel_order_eq_prime hp5
  have hk : k ≠ 0 := by
    intro hz
    rw [hz, addOrderOf_zero] at ho
    exact (Fact.out : p.Prime).ne_one ho.symm
  have hc1 : Nat.card (T.fixedH1CoefficientKernel A) ≠ 1 := by
    intro hc
    exact hk ((Nat.card_eq_one_iff_unique.mp hc).1.elim k 0)
  obtain ⟨s, hs, hc⟩ := T.fixedKernel_prime_power_profile A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  have hs0 : s ≠ 0 := by intro hz; exact hc1 (by rw [hc, hz, pow_zero])
  exact ⟨s, by omega, hs, hc⟩
end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の同じ算術証明書から、同じ剰余類・H⁰ 元・係数核の元と巡回部分群を出力する。 -/
theorem residual_exists_prime_cyclic_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      addOrderOf (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf k = p ∧ Nat.card (AddSubgroup.zmultiples k) = p ∧
      k.val = T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.fixedCoset_order_eq_prime hp5, h.fixedCosetH0_order_eq_prime hp5,
    h.fixedKernel_order_eq_prime hp5, h.fixedKernel_cyclic_card hp5,
    T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    h.fixedKernel_positive_profile hp5⟩
end
end DkMath.FLT.Frey.Source
