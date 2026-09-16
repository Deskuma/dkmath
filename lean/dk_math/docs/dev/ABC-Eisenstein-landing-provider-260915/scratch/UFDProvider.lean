import DkMath.FLT.Three.EisensteinEuclidean
import DkMath.Lib.NumberTheory.EisensteinCoordinates
import Mathlib

/-!
Research scratch: squarefree extraction in a well-founded divisibility monoid,
then norm-squarefree extraction for the primitive cubic Eisenstein coordinate.
This does not use an ABC counting estimate.
-/

namespace ABCLandingScratch

noncomputable section

open DkMath.NumberTheory.TraceOneQuadratic

/- Every terminating square-factor extraction leaves a squarefree element.
Unique factorization is stronger than the assumptions needed for existence. -/
theorem exists_squarefree_mul_sq
    {R : Type*} [CommMonoidWithZero R] [WfDvdMonoid R]
    (a : R) (ha : a ≠ 0) :
    ∃ b c : R, Squarefree b ∧ a = b * c ^ 2 := by
  classical
  revert ha
  refine (wellFounded_dvdNotUnit (α := R)).induction
    (C := fun a : R => a ≠ 0 → ∃ b c : R, Squarefree b ∧ a = b * c ^ 2) a ?_
  intro a ih ha
  by_cases hs : Squarefree a
  · exact ⟨a, 1, hs, by simp⟩
  · obtain ⟨d, hd, hdu⟩ : ∃ d : R, ∃ _ : d * d ∣ a, ¬IsUnit d := by
      simpa only [Squarefree, not_forall] using hs
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by
      intro h
      simp only [h, mul_zero] at hq
      exact ha hq
    have hqa : DvdNotUnit q a := by
      refine ⟨hq0, d * d, ?_, ?_⟩
      · exact fun hu => hdu (isUnit_of_mul_isUnit_left hu)
      · rw [hq]
        ac_rfl
    obtain ⟨b, c, hb, hbc⟩ := ih q hqa hq0
    refine ⟨b, d * c, hb, ?_⟩
    simp only [hq, hbc, pow_two]
    ac_rfl

example : EuclideanDomain (TraceOneInt (-1)) := inferInstance
example : IsPrincipalIdealRing (TraceOneInt (-1)) := inferInstance
example : UniqueFactorizationMonoid (TraceOneInt (-1)) := inferInstance

theorem squarefree_conj {x : TraceOneInt (-1)} (hx : Squarefree x) :
    Squarefree (conj x) := by
  intro d hd
  obtain ⟨k, hk⟩ := hd
  have hdd : conj d * conj d ∣ x := by
    refine ⟨conj k, ?_⟩
    have h := congrArg conj hk
    simpa only [traceOne_conj_invol, traceOne_conj_mul] using h
  obtain ⟨u, hu⟩ := hx (conj d) hdd
  rw [isUnit_iff_dvd_one]
  refine ⟨conj (↑(u⁻¹) : TraceOneInt (-1)), ?_⟩
  have hmul : conj d * (↑(u⁻¹) : TraceOneInt (-1)) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  have h := congrArg conj hmul
  simpa only [traceOne_conj_mul, traceOne_conj_invol,
    show conj (1 : TraceOneInt (-1)) = 1 from rfl] using h.symm

theorem scalar_dvd_of_square_dvd_norm
    {b : TraceOneInt (-1)} (hb : Squarefree b) {d : ℤ}
    (hd : d * d ∣ norm b) : (d : TraceOneInt (-1)) ∣ b := by
  have hsq : (d : TraceOneInt (-1)) * (d : TraceOneInt (-1)) ∣ conj b * b := by
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : TraceOneInt (-1)), ?_⟩
    rw [mul_comm (conj b) b, traceOne_mul_conj]
    change ((norm b : ℤ) : TraceOneInt (-1)) = _
    simpa only [Int.cast_mul] using
      congrArg (fun z : ℤ => (z : TraceOneInt (-1))) hk
  exact (squarefree_conj hb).dvd_of_squarefree_of_mul_dvd_mul_right hsq

theorem squarefree_norm_of_dvd_cubicCoord
    {a : ℤ} {b : TraceOneInt (-1)} (hb : Squarefree b)
    (hba : b ∣ DkMath.Lib.NumberTheory.eisensteinCoord (a + 2) 1) :
    Squarefree (norm b) := by
  intro d hd
  obtain ⟨k, hk⟩ := (scalar_dvd_of_square_dvd_norm hb hd).trans hba
  have hs := congrArg TraceOneInt.snd hk
  change -(1 : ℤ) = d * k.snd + 0 * k.fst + 0 * k.snd at hs
  have hd1 : d ∣ (-1 : ℤ) := ⟨k.snd, by simpa using hs⟩
  exact isUnit_of_dvd_unit hd1 (isUnit_one.neg)

theorem exists_cubicCoord_squarefree_norm_mul_sq (a : ℤ) :
    ∃ b c : TraceOneInt (-1),
      Squarefree b ∧ Squarefree (norm b) ∧
      DkMath.Lib.NumberTheory.eisensteinCoord (a + 2) 1 = b * c ^ 2 := by
  have ha : DkMath.Lib.NumberTheory.eisensteinCoord (a + 2) 1 ≠ 0 := by
    intro h
    have hs := congrArg TraceOneInt.snd h
    norm_num at hs
  obtain ⟨b, c, hb, hbc⟩ := exists_squarefree_mul_sq
    (DkMath.Lib.NumberTheory.eisensteinCoord (a + 2) 1) ha
  exact ⟨b, c, hb, squarefree_norm_of_dvd_cubicCoord hb ⟨c ^ 2, hbc⟩, hbc⟩

theorem exists_cubicCoord_nat_squarefree_norm_mul_sq (a : ℕ) :
    ∃ b c : TraceOneInt (-1),
      Squarefree (norm b).natAbs ∧
      a ^ 2 + 3 * a + 3 = (norm b).natAbs * (norm c).natAbs ^ 2 ∧
      DkMath.Lib.NumberTheory.eisensteinCoord ((a : ℤ) + 2) 1 = b * c ^ 2 := by
  obtain ⟨b, c, _, hb, hbc⟩ := exists_cubicCoord_squarefree_norm_mul_sq (a : ℤ)
  refine ⟨b, c, Int.squarefree_natAbs.mpr hb, ?_, hbc⟩
  have hn : ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) = norm b * norm c ^ 2 := by
    calc
      ((a ^ 2 + 3 * a + 3 : ℕ) : ℤ) =
          norm (DkMath.Lib.NumberTheory.eisensteinCoord ((a : ℤ) + 2) 1) := by
        rw [DkMath.Lib.NumberTheory.norm_eisensteinCoord]
        push_cast
        ring
      _ = norm b * norm c ^ 2 := by
        rw [hbc, pow_two, traceOne_norm_mul, traceOne_norm_mul]
        ring
  simpa only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] using
    congrArg Int.natAbs hn

#print axioms exists_squarefree_mul_sq
#print axioms squarefree_norm_of_dvd_cubicCoord
#print axioms exists_cubicCoord_squarefree_norm_mul_sq
#print axioms exists_cubicCoord_nat_squarefree_norm_mul_sq

end

end ABCLandingScratch
