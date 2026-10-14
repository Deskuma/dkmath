import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace DkMath.FLT.Seven

noncomputable section

open Polynomial

namespace Scratch

theorem cubicRoot_to_primitiveSeventhRoot
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (beta : ZMod q)
    (hbeta : beta ^ 3 - 2 * beta ^ 2 - beta + 1 = 0)
    (hbeta3 : beta ≠ 3) :
    ∃ t : AlgebraicClosure (ZMod q), IsPrimitiveRoot t 7 ∧
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) beta =
        1 + t + t⁻¹) ∧
      (t ^ q = t ∨ t ^ q = t⁻¹) ∧
      7 ∣ q ^ 2 - 1 := by
  let F := ZMod q
  let A := AlgebraicClosure F
  let b : A := algebraMap F A beta
  let c : A := b - 1
  let f : A[X] := X ^ 2 - C c * X + C 1
  have hdeg : f.degree ≠ 0 := by
    have hdegree := Polynomial.degree_quadratic (R := A)
      (a := 1) (b := -c) (c := 1) (by norm_num)
    have : f.degree = 2 := by
      simpa [f, sub_eq_add_neg, add_assoc] using hdegree
    rw [this]
    norm_num
  obtain ⟨t, htroot⟩ := IsAlgClosed.exists_root f hdeg
  have htquad : t ^ 2 - c * t + 1 = 0 := by
    simpa [f, IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow] using htroot
  have ht : t ≠ 0 := by
    intro ht0
    rw [ht0] at htquad
    norm_num at htquad
  have hbt : b = 1 + t + t⁻¹ := by
    have hct : c = t + t⁻¹ := by
      apply (mul_right_cancel₀ ht)
      calc
        c * t = t ^ 2 + 1 := by linear_combination -htquad
        _ = (t + t⁻¹) * t := by
          rw [add_mul, inv_mul_cancel₀ ht]
          ring
    dsimp [c] at hct
    linear_combination hct
  have hbetaA : b ^ 3 - 2 * b ^ 2 - b + 1 = 0 := by
    dsimp [b]
    have h2 : (algebraMap F A) (2 : F) = (2 : A) :=
      map_ofNat (algebraMap F A) 2
    have hmap := congrArg (algebraMap F A) hbeta
    simpa only [map_sub, map_pow, map_mul, map_add, map_zero, map_one, h2]
      using hmap
  have hsum : 1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 = 0 := by
    have hid : t ^ 3 * (b ^ 3 - 2 * b ^ 2 - b + 1) =
        1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6 := by
      rw [hbt]
      let Q : A := t ^ 2 * (t⁻¹) ^ 2 +
          (t + t ^ 2 + 3 * t ^ 3) * t⁻¹ +
          (1 + t + t ^ 2 + 2 * t ^ 3 + 3 * t ^ 4)
      have hfactor :
          t ^ 3 * ((1 + t + t⁻¹) ^ 3 - 2 * (1 + t + t⁻¹) ^ 2 -
            (1 + t + t⁻¹) + 1) -
            (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6) =
            (t * t⁻¹ - 1) * Q := by
        ring
      apply sub_eq_zero.mp
      rw [hfactor]
      rw [mul_inv_cancel₀ ht]
      simp
    rw [hbetaA, mul_zero] at hid
    exact hid.symm
  have ht7 : t ^ 7 = 1 := by
    have hgeom : (t - 1) *
        (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6) = t ^ 7 - 1 := by
      calc
        _ = t ^ 6 * t - 1 := by
          simp only [pow_succ, pow_zero]
          ring
        _ = t ^ 7 - 1 := by
          congr 1
          exact (pow_succ t 6).symm
    rw [hsum, mul_zero] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have htne1 : t ≠ 1 := by
    intro h
    rw [h] at hbt
    exact hbeta3 (by
      apply (algebraMap F A).injective
      have hbt' : (algebraMap F A) beta = (algebraMap F A) 3 := by
        calc
          (algebraMap F A) beta = 1 + 1 + 1 := by simpa [b] using hbt
          _ = (algebraMap F A) 3 := by
            rw [map_ofNat]
            norm_num
      exact hbt')
  have hprim : IsPrimitiveRoot t 7 := by
    apply isPrimitiveRoot_of_mem_nthRootsFinset (p := 7) (η := t) (by decide)
    · rw [mem_nthRootsFinset]
      · exact ht7
      · norm_num
    exact htne1
  have hfixed : b ^ q = b := by
    have hp : beta ^ q = beta := by simp only [ZMod.pow_card]
    calc
      b ^ q = algebraMap F A (beta ^ q) := by rw [map_pow]
      _ = algebraMap F A beta := by rw [hp]
      _ = b := rfl
  have htqroot : (t ^ q) ^ 2 - c * (t ^ q) + 1 = 0 := by
    have hqpow := congrArg (fun x : A => x ^ q) htquad
    rw [show t ^ 2 - c * t + 1 = (t ^ 2 - c * t) + 1 by ring] at hqpow
    rw [add_pow_char, sub_pow_char, mul_pow] at hqpow
    have hcfixed : c ^ q = c := by
      dsimp [c]
      rw [sub_pow_char, hfixed, one_pow]
    rw [hcfixed] at hqpow
    have hpow : (t ^ 2) ^ q = (t ^ q) ^ 2 := by
      calc
        (t ^ 2) ^ q = t ^ (2 * q) := (pow_mul t 2 q).symm
        _ = t ^ (q * 2) := by rw [mul_comm]
        _ = (t ^ q) ^ 2 := pow_mul t q 2
    rw [hpow, zero_pow hq.ne_zero] at hqpow
    simpa [mul_comm, mul_left_comm, mul_assoc] using hqpow
  have hpair : (t ^ q - t) * (t ^ q - t⁻¹) = 0 := by
    have htinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    have hcoef : t + t⁻¹ = c := by
      apply (mul_right_cancel₀ ht)
      calc
        (t + t⁻¹) * t = t ^ 2 + 1 := by
          rw [add_mul, inv_mul_cancel₀ ht]
          ring
        _ = c * t := by linear_combination htquad
    calc
      (t ^ q - t) * (t ^ q - t⁻¹) =
          (t ^ q) ^ 2 - (t + t⁻¹) * (t ^ q) + t * t⁻¹ := by ring
      _ = (t ^ q) ^ 2 - c * (t ^ q) + 1 := by rw [hcoef, htinv]
      _ = 0 := htqroot
  have hpair' : t ^ q = t ∨ t ^ q = t⁻¹ := by
    rcases mul_eq_zero.mp hpair with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hq2 : t ^ (q ^ 2) = t := by
    rcases hpair' with h | h
    · calc
        t ^ (q ^ 2) = (t ^ q) ^ q := by
          simpa [pow_two] using (pow_mul t q q)
        _ = t ^ q := congrArg (fun x : A => x ^ q) h
        _ = t := h
    · calc
        t ^ (q ^ 2) = (t ^ q) ^ q := by
          simpa [pow_two] using (pow_mul t q q)
        _ = (t⁻¹) ^ q := congrArg (fun x : A => x ^ q) h
        _ = (t ^ q)⁻¹ := by rw [inv_pow]
        _ = (t⁻¹)⁻¹ := by rw [h]
        _ = t := inv_inv t
  have hminus : t ^ (q ^ 2 - 1) = 1 := by
    apply (mul_right_cancel₀ ht)
    have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq.one_le
    calc
      t ^ (q ^ 2 - 1) * t = t ^ (q ^ 2) := by
        rw [← pow_succ, Nat.sub_add_cancel hq2pos]
      _ = t := hq2
      _ = 1 * t := by simp
  have hdiv : 7 ∣ q ^ 2 - 1 := hprim.dvd_of_pow_eq_one _ hminus
  exact ⟨t, hprim, hbt, hpair', hdiv⟩

theorem cubicRoot_mod_seven
    {q : ℕ} (hq : q.Prime) (beta : ZMod q)
    (hbeta : beta ^ 3 - 2 * beta ^ 2 - beta + 1 = 0)
    (hbeta3 : beta ≠ 3) :
    q % 7 = 1 ∨ q % 7 = 6 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨t, _, _, _, hdiv⟩ := cubicRoot_to_primitiveSeventhRoot hq beta hbeta hbeta3
  obtain ⟨k, hk⟩ := hdiv
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hmod : ((q : ZMod 7) ^ 2 = 1) := by
    have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq.one_le
    have hq2 : q ^ 2 = 7 * k + 1 :=
      (Nat.sub_eq_iff_eq_add hq2pos).mp hk
    calc
      (q : ZMod 7) ^ 2 = ((q ^ 2 : ℕ) : ZMod 7) := by norm_num
      _ = ((7 * k + 1 : ℕ) : ZMod 7) := by rw [hq2]
      _ = 1 := by
        calc
          ((7 * k + 1 : ℕ) : ZMod 7) =
              (7 : ZMod 7) * (k : ZMod 7) + 1 := by norm_num
          _ = 1 := by
            have h7 : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
            rw [h7]
            simp
  have hfac : ((q : ZMod 7) - 1) * ((q : ZMod 7) + 1) = 0 := by
    calc
      _ = (q : ZMod 7) ^ 2 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hmod
  rcases mul_eq_zero.mp hfac with h | h
  · left
    have : (q : ZMod 7) = 1 := sub_eq_zero.mp h
    exact (ZMod.natCast_eq_natCast_iff' q 1 7).mp this |>.trans (by norm_num)
  · right
    have : (q : ZMod 7) = -1 := by
      exact eq_neg_of_add_eq_zero_left h
    have h6 : (q : ZMod 7) = (6 : ZMod 7) := by
      calc
        (q : ZMod 7) = -1 := this
        _ = (6 : ZMod 7) := by
          have h7 : (7 : ZMod 7) = 0 := ZMod.natCast_self 7
          calc
            (-1 : ZMod 7) = -(7 : ZMod 7) + 6 := by ring
            _ = 6 := by rw [h7]; simp
    exact (ZMod.natCast_eq_natCast_iff' q 6 7).mp h6 |>.trans (by norm_num)

end Scratch
end
end DkMath.FLT.Seven
