import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport
import DkMath.FLT.Seven.SevenRealCubicResidueCriterion
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

namespace DkMath.FLT.Seven

noncomputable section

open scoped NumberField
open Polynomial


namespace SevenRealCubic

#check Ideal.absNorm_pow_inertiaDeg
#check Ideal.natAbs_pow_inertiaDeg
#check Ideal.inertiaDegIn_eq_inertiaDeg
#check Ideal.bijective_algebraMap_quotient_residueField
#check Nat.card_congr
#check Fintype.card_eq_nat_card
#check FiniteField.ringEquivOfCardEq
#check Ideal.absNorm_span_singleton
#check SevenRealCubicInt.alpha_cube
#check Ideal.mem_of_dvd
#check Ideal.mem_under

example {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot)) :
    True := by
  obtain ⟨P, Q, hPmax, hQmax, hPunder, hQunder, hPlies, hQlies,
    hPdiv, hQdiv, hPQ⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals t hq hqR hqS
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hbaseMax : base.IsMaximal := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hq.ne_zero)).mpr
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq)) |>.isMaximal
      (by simpa using (Int.ofNat_ne_zero.mpr hq.ne_zero))
  let : base.IsMaximal := hbaseMax
  let : P.IsMaximal := hPmax
  let : P.IsPrime := hPmax.isPrime
  let hpLies : P.LiesOver base := ⟨by simpa [base] using hPlies.over⟩
  let : P.LiesOver base := hpLies
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlies
  let : Fintype P.ResidueField := Fintype.ofFinite P.ResidueField
  have hsplit := common_norm_prime_complete_split t hq hqR hqS
  have hcardP : Fintype.card P.ResidueField = q := by
    have hinertia : P.inertiaDeg ℤ = 1 := by
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg
        (Ideal.span {(q : ℤ)}) P Gal(Field / ℚ)]
      exact hsplit.2.2.2
    have hnormP : Ideal.absNorm P = q := by
      have hpow := Ideal.natAbs_pow_inertiaDeg (q : ℤ) P
      rw [hinertia, pow_one] at hpow
      exact hpow.symm
    have hcardQuot : Nat.card (O ⧸ P) = q := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hnormP]
    have hcardResidue : Nat.card (O ⧸ P) = Nat.card P.ResidueField :=
      Nat.card_congr (Equiv.ofBijective (algebraMap (O ⧸ P) P.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField P))
    rw [Fintype.card_eq_nat_card, ← hcardResidue, hcardQuot]
  let : Fact q.Prime := ⟨hq⟩
  let e : P.ResidueField ≃+* ZMod q :=
    FiniteField.ringEquivOfCardEq (K := P.ResidueField) (K' := ZMod q) (by
      simpa [ZMod.card] using hcardP)
  let evalP : SevenRealCubicInt →+* ZMod q :=
    e.toRingHom.comp
      ((algebraMap O P.ResidueField).comp
        SevenRealCubic.modelEquivRingOfIntegers.toRingHom)
  have heval_int (n : ℤ) : evalP (SevenRealCubicInt.ofInt n) = (n : ZMod q) := by
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
    exact hsplit.1 hqeq
  trivial

end SevenRealCubic
end
end DkMath.FLT.Seven
