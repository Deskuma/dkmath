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
