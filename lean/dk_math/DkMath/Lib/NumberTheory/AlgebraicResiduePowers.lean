/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual q-address and algebraicity class supply residue characteristic and torsion.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalGenerator
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.ZMod

#print "file: DkMath.Lib.NumberTheory.AlgebraicResiduePowers"

/-!
# tail の根構成に使う、実際の剰余冪根と有限位数

剰余の冪根の存在、非零剰余の有限位数を外部 provider にしない。
後者は整数の原始多項式を q で還元し、実際の有限部分代数を構成して証明する。
-/
namespace DkMath.Lib.NumberTheory.AlgebraicResidue
open Polynomial
noncomputable section
variable {L : Type} [Field L]

/-- 代数閉体の付値剰余体では、全ての正の冪写像が全射。 -/
theorem power_surjective [IsAlgClosed L] (P : ValuationSubring L) (n : ℕ) (hn : n ≠ 0)
    (c : IsLocalRing.ResidueField P) : ∃ y : IsLocalRing.ResidueField P, y ^ n = c := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (Nat.pos_of_ne_zero hn)
  have hβP : β ∈ P := by
    by_contra h
    have h1 : 1 < P.valuation β := by rwa [← not_le, P.valuation_le_one_iff]
    have h2 : P.valuation β ^ n ≤ 1 := by rw [← map_pow, hβ]; exact P.valuation_le_one x
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have h3 : P.valuation β ≤ P.valuation β ^ (k + 1) := by
      rw [pow_succ]
      calc P.valuation β = 1 * P.valuation β := (one_mul _).symm
        _ ≤ P.valuation β ^ k * P.valuation β := mul_le_mul' (one_le_pow_of_one_le' h1.le k) le_rfl
    exact absurd (lt_of_lt_of_le h1 (h3.trans h2)) (lt_irrefl 1)
  refine ⟨IsLocalRing.residue P ⟨β, hβP⟩, ?_⟩
  rw [← map_pow]
  congr 1
  exact Subtype.ext hβ

/-- ℚ 上代数的な体の q 上の剰余体では、非零元の乗法位数は有限。 -/
theorem nonzero_finite_order [CharZero L] [Algebra.IsAlgebraic ℚ L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hA : ValuationInertia.LiesOverPrime P q)
    (c : IsLocalRing.ResidueField P) (hc : c ≠ 0) : ∃ N : ℕ, 0 < N ∧ c ^ N = 1 := by
  classical
  have hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hA
  have hqκ : (q : IsLocalRing.ResidueField P) = 0 := by
    have : IsLocalRing.residue P (q : P) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hq
    simpa using this
  have : Fact q.Prime := ⟨hqp⟩
  have : CharP (IsLocalRing.ResidueField P) q := (CharP.charP_iff_prime_eq_zero hqp).mpr hqκ
  let : Algebra (ZMod q) (IsLocalRing.ResidueField P) := ZMod.algebra _ q
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  have halgZ : IsAlgebraic ℤ (x : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨g, hg0, hgx⟩ := halgZ
  set pp : ℤ[X] := g.primPart with hppdef
  have hppL : aeval (x : L) pp = 0 := by
    have h := hgx
    rw [g.eq_C_content_mul_primPart, map_mul, aeval_C] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    have : g.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hg0
    exact (map_ne_zero_iff (algebraMap ℤ L) (algebraMap ℤ L).injective_int).mpr this
  have hppP : aeval x pp = 0 := by
    have h := Polynomial.aeval_algHom_apply (P.subtype.toIntAlgHom) x pp
    apply P.subtype_injective
    rw [map_zero]
    change P.subtype.toIntAlgHom (aeval x pp) = 0
    rw [← h]
    exact hppL
  have hppκ : aeval (IsLocalRing.residue P x) pp = 0 := by
    have h := Polynomial.aeval_algHom_apply ((IsLocalRing.residue P).toIntAlgHom) x pp
    refine h.trans ?_
    rw [hppP, map_zero]
  set h : (ZMod q)[X] := pp.map (Int.castRingHom (ZMod q)) with hhdef
  have hh0 : h ≠ 0 := by
    intro h0
    have hdvd : C (q : ℤ) ∣ pp := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have : (Int.castRingHom (ZMod q)) (pp.coeff i) = 0 := by
        rw [← coeff_map, ← hhdef, h0, coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    have hu : IsUnit (q : ℤ) := (isPrimitive_iff_isUnit_of_C_dvd.mp g.isPrimitive_primPart) _ hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact hqp.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ q := Int.natCast_nonneg q
      omega
  have hhc : aeval (IsLocalRing.residue P x) h = 0 := by
    rw [hhdef, aeval_def, eval₂_map]
    have : (algebraMap (ZMod q) (IsLocalRing.ResidueField P)).comp (Int.castRingHom (ZMod q)) =
        algebraMap ℤ (IsLocalRing.ResidueField P) := RingHom.ext_int _ _
    rw [this, ← aeval_def, hppκ]
  have halgc : IsAlgebraic (ZMod q) (IsLocalRing.residue P x) := ⟨h, hh0, hhc⟩
  have hint : IsIntegral (ZMod q) (IsLocalRing.residue P x) :=
    IsAlgebraic.isIntegral (K := ZMod q) (A := IsLocalRing.ResidueField P) halgc
  set S := (Algebra.adjoin (ZMod q) {IsLocalRing.residue P x}).toSubmodule with hS
  have : Module.Finite (ZMod q) S := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : Finite S := Module.finite_of_finite (ZMod q)
  have hmem : ∀ i : ℕ, IsLocalRing.residue P x ^ i ∈ S := fun i =>
    show IsLocalRing.residue P x ^ i ∈ Algebra.adjoin (ZMod q) {IsLocalRing.residue P x} from
      Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ _) i
  obtain ⟨i, j, hij, hpow⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨_, hmem i⟩ : S))
  have hpow' : IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j := congrArg Subtype.val hpow
  have key : ∀ i j : ℕ, i < j → IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j →
      ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue P x ^ N = 1 := by
    intro i j hlt heq
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hsplit : IsLocalRing.residue P x ^ j = IsLocalRing.residue P x ^ i * IsLocalRing.residue P x ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hsplit] at heq
    have hi0 : IsLocalRing.residue P x ^ i ≠ 0 := pow_ne_zero _ hc
    exact (mul_right_injective₀ hi0 (heq.symm.trans (mul_one _).symm))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hpow'
  · exact key j i hlt hpow'.symm

end
end DkMath.Lib.NumberTheory.AlgebraicResidue
