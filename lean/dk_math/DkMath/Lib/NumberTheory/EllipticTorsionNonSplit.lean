/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import DkMath.Lib.NumberTheory.EllipticTorsionGL2

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionNonSplit"

/-!
# p²の短完全列は加法群としても非分裂

非零のQ∈E[p]をp倍写像で持ち上げると、pP=Q≠0かつp²P=0となる。
従ってPの位数はp²である。一方、E[p]×E[p]の全ての点はp倍で零となるため、
両者の位数が同じでも加法群として同型にはならない。
また、E[p]からの加法準同型の像はp倍で消えるので、制限p倍写像の右逆にはなれない。
各段がZMod(pᵏ)上で自由であることと、異なる段を直和に分解できることは別の性質である。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- n-torsionの点自身もn倍で零になる。元の点への包含の単射性で証明する。 -/
theorem torsion_nsmul_self (n : ℕ) (P : Torsion E n) : n • P = 0 :=
  Subtype.ext (underlying_killed E P)

variable [CharZero K] [E.IsElliptic] (p : ℕ) [Fact p.Prime]

/-- 非零のp-torsion点の持ち上げは、p倍で零にはならない。 -/
theorem exists_prime_square_not_killed : ∃ P : Torsion E (p * p), p • P ≠ 0 := by
  let Q := torsionBasis E p 0
  obtain ⟨P, hP⟩ := (torsion_short_exact E p p (Fact.out : p.Prime).ne_zero).2.2 Q
  refine ⟨P, fun h => ?_⟩
  have hval := congrArg (fun T : Torsion E (p * p) => T.val) h
  have hz : torsionMultiply E p p P = 0 := Subtype.ext hval
  exact (torsionBasis E p).ne_zero 0 (hP.symm.trans hz)

/-- 同じ実際のp²-torsionの中に、位数ちょうどp²の点が存在する。 -/
theorem exists_prime_square_order : ∃ P : Torsion E (p * p), addOrderOf P = p ^ 2 := by
  obtain ⟨P, hP⟩ := exists_prime_square_not_killed E p
  refine ⟨P, addOrderOf_eq_prime_pow (n := 1) (by simpa only [pow_one] using hP) ?_⟩
  simpa [pow_two] using torsion_nsmul_self E (p * p) P

/-- p倍写像E[p²]→E[p]は、加法準同型である右逆を持たない。 -/
theorem prime_square_no_additive_section :
    ¬ ∃ s : Torsion E p →+ Torsion E (p * p),
      Function.RightInverse s (torsionMultiply E p p) := by
  rintro ⟨s, hs⟩
  let Q := torsionBasis E p 0
  have hz : p • s Q = 0 := by
    rw [← map_nsmul, torsion_nsmul_self, map_zero]
  have hm : torsionMultiply E p p (s Q) = 0 :=
    Subtype.ext (congrArg (fun T : Torsion E (p * p) => T.val) hz)
  exact (torsionBasis E p).ne_zero 0 ((hs Q).symm.trans hm)

/-- 同じ位数p⁴でも、E[p²]とE[p]×E[p]は加法群として同型でない。 -/
theorem prime_square_not_product :
    ¬ Nonempty (Torsion E (p * p) ≃+ (Torsion E p × Torsion E p)) := by
  rintro ⟨e⟩
  obtain ⟨P, hP⟩ := exists_prime_square_not_killed E p
  have hz : p • e P = 0 := Prod.ext (torsion_nsmul_self E p (e P).1) (torsion_nsmul_self E p (e P).2)
  apply hP
  apply e.injective
  rw [map_nsmul, hz, map_zero]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
