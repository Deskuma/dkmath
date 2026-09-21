/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport
import DkMath.FLT.Seven.SevenRealCubicResidueCriterion
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

namespace DkMath.FLT.Seven

noncomputable section

open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

/-! ## Degree-one residue evaluation -/

theorem residueField_card_of_inertiaDeg_one
    {q : ℕ} {P : Ideal O}
    [P.IsMaximal] [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})]
    (hinertia : P.inertiaDeg ℤ = 1) :
    Nat.card P.ResidueField = q := by
  let : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  have hnormP : Ideal.absNorm P = q := by
    have hpow := Ideal.natAbs_pow_inertiaDeg (q : ℤ) P
    rw [hinertia, pow_one] at hpow
    exact hpow.symm
  have hcardQuot : Nat.card (O ⧸ P) = q := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hnormP]
  have hcardResidue : Nat.card (O ⧸ P) = Nat.card P.ResidueField :=
    Nat.card_congr (Equiv.ofBijective (algebraMap (O ⧸ P) P.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField P))
  rw [← hcardResidue, hcardQuot]

/-! ## The current packet maps to the neutral finite-field criterion -/

theorem common_norm_prime_mod_seven
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot)) :
    q % 7 = 1 ∨ q % 7 = 6 := by
  obtain ⟨P, Q, hPmax, hQmax, hPunder, hQunder, hPlies, hQlies,
    hPdiv, hQdiv, hPQ⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals t hq hqR hqS
  let : P.IsMaximal := hPmax
  let : P.IsPrime := hPmax.isPrime
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlies
  let : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  let : Fact q.Prime := ⟨hq⟩
  have hinertia : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span {(q : ℤ)}) P Gal(Field / ℚ)]
    exact (common_norm_prime_complete_split t hq hqR hqS).2.2.2
  have hcardNat : Nat.card P.ResidueField = q :=
    residueField_card_of_inertiaDeg_one hinertia
  have hcardP : Fintype.card P.ResidueField = q := by
    rw [Fintype.card_eq_nat_card, hcardNat]
  let e : P.ResidueField ≃+* ZMod q :=
    FiniteField.ringEquivOfCardEq (K := P.ResidueField) (K' := ZMod q) (by
      simpa [ZMod.card] using hcardP)
  let evalP : SevenRealCubicInt →+* ZMod q :=
    e.toRingHom.comp
      ((algebraMap O P.ResidueField).comp
        SevenRealCubic.modelEquivRingOfIntegers.toRingHom)
  have heval_int (n : ℤ) :
      evalP (SevenRealCubicInt.ofInt n) = (n : ZMod q) := by
    simp [evalP]
  have heval_mem {a : SevenRealCubicInt}
      (ha : SevenRealCubic.modelEquivRingOfIntegers a ∈ P) : evalP a = 0 := by
    have ha' : SevenRealCubic.modelToRingOfIntegers a ∈ P := by
      simpa only [SevenRealCubic.modelEquivRingOfIntegers_apply] using ha
    simp [evalP, Ideal.algebraMap_residueField_eq_zero.mpr ha']
  let beta : ZMod q := evalP SevenRealCubicInt.alpha
  have hbeta : beta ^ 3 - 2 * beta ^ 2 - beta + 1 = 0 := by
    have h := congrArg evalP SevenRealCubicInt.alpha_cube
    dsimp [beta]
    have h' : evalP SevenRealCubicInt.alpha ^ 3 =
        2 * evalP SevenRealCubicInt.alpha ^ 2 +
          evalP SevenRealCubicInt.alpha - 1 := by
      simpa only [map_pow, map_mul, map_add, map_sub, map_one, map_ofNat] using h
    linear_combination h'
  have hbeta3 : beta ≠ 3 := by
    intro hb
    have hseven : (7 : ZMod q) = 0 := by
      have hbeta' := hbeta
      rw [hb] at hbeta'
      norm_num at hbeta'
      exact hbeta'
    have hqdiv : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp hseven
    have hqeq : q = 7 := by
      exact (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hqdiv |>.resolve_left hq.ne_one
    exact (common_norm_prime_complete_split t hq hqR hqS).1 hqeq
  exact cubicRoot_mod_seven hq beta hbeta hbeta3

/-! ## GCD support, without asserting coprimality -/

theorem common_norm_prime_gcd_support
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqgcd : q ∣ Nat.gcd
      (Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot))
      (Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot))) :
    q % 7 = 1 ∨ q % 7 = 6 := by
  apply common_norm_prime_mod_seven t hq
  · exact (Nat.dvd_gcd_iff.mp hqgcd).1
  · exact (Nat.dvd_gcd_iff.mp hqgcd).2

end SevenRealCubic
end
end DkMath.FLT.Seven
