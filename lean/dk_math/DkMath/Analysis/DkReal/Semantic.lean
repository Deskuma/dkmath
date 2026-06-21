/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.CanonicalOrder

#print "file: DkMath.Analysis.DkReal.Semantic"

/-!
# Semantic real value of a DkReal representation

This module begins the noncomputable bridge from nested rational intervals to
Mathlib's `Real`.

The represented value is the supremum of the lower endpoints after casting
them to `Real`. Nestedness makes this sequence monotone, while every upper
endpoint bounds it. Consequently the supremum lies in every approximation
interval.

Representative independence permits quotient descent to `DkNNRealQ`.
The resulting semantic map preserves rational constants, nonnegative
addition, multiplication, natural powers, and order.

[TODO: semantic/order-reflection] Prove that semantic order reflects the
canonical quotient order. This requires recovering a nonnegative canonical
Gap from an inequality between semantic values.
-/

namespace DkMath.Analysis.DkReal

noncomputable section

/-- Lower endpoint of a representation, interpreted in Mathlib's `Real`. -/
def lowerReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  (x.interval n).lo

/-- Upper endpoint of a representation, interpreted in Mathlib's `Real`. -/
def upperReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  (x.interval n).hi

/-- Width of an approximation interval, interpreted in Mathlib's `Real`. -/
def widthReal (x : DkMath.Analysis.DkReal) (n : ℕ) : ℝ :=
  upperReal x n - lowerReal x n

/-- Cast lower endpoints form a monotone real sequence. -/
theorem lowerReal_monotone (x : DkMath.Analysis.DkReal) :
    Monotone (lowerReal x) := by
  intro n m hnm
  simp only [lowerReal]
  exact_mod_cast x.lo_mono hnm

/-- Every fixed upper endpoint bounds all cast lower endpoints. -/
theorem lowerReal_le_upperReal
    (x : DkMath.Analysis.DkReal) (n m : ℕ) :
    lowerReal x m ≤ upperReal x n := by
  simp only [lowerReal, upperReal]
  by_cases hmn : m ≤ n
  · exact_mod_cast
      (x.lo_mono hmn).trans (x.interval n).le_lo_hi
  · have hnm : n ≤ m := le_of_not_ge hmn
    exact_mod_cast
      (x.interval m).le_lo_hi.trans (x.hi_antitone hnm)

/-- The range of cast lower endpoints is bounded above. -/
theorem bddAbove_range_lowerReal (x : DkMath.Analysis.DkReal) :
    BddAbove (Set.range (lowerReal x)) := by
  refine ⟨upperReal x 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact lowerReal_le_upperReal x 0 n

/--
The semantic real represented by a nested interval sequence.

Completeness enters exactly here, through the conditionally complete order on
Mathlib's real numbers.
-/
def semanticValue (x : DkMath.Analysis.DkReal) : ℝ :=
  ⨆ n, lowerReal x n

/-- Every lower endpoint is below the represented semantic value. -/
theorem lowerReal_le_semanticValue
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    lowerReal x n ≤ semanticValue x := by
  exact le_ciSup (bddAbove_range_lowerReal x) n

/-- The represented semantic value is below every upper endpoint. -/
theorem semanticValue_le_upperReal
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    semanticValue x ≤ upperReal x n := by
  apply ciSup_le
  intro m
  exact lowerReal_le_upperReal x n m

/-- The semantic value belongs to every cast approximation interval. -/
theorem semanticValue_mem_interval
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    semanticValue x ∈ Set.Icc (lowerReal x n) (upperReal x n) :=
  ⟨lowerReal_le_semanticValue x n, semanticValue_le_upperReal x n⟩

/-- Cast interval widths tend to zero. -/
theorem tendsto_widthReal_zero (x : DkMath.Analysis.DkReal) :
    Filter.Tendsto (widthReal x) Filter.atTop (nhds 0) := by
  have hcast :=
    Rat.continuous_coe_real.continuousAt.tendsto.comp x.tendsto_width_zero
  convert hcast using 1
  · funext n
    simp [widthReal, upperReal, lowerReal, GapInterval.width]
  · simp

/-- Cast lower endpoints converge monotonically to the semantic value. -/
theorem tendsto_lowerReal_semanticValue (x : DkMath.Analysis.DkReal) :
    Filter.Tendsto (lowerReal x) Filter.atTop (nhds (semanticValue x)) := by
  exact tendsto_atTop_ciSup (lowerReal_monotone x) (bddAbove_range_lowerReal x)

/--
The semantic value is the unique real point contained in every approximation
interval.

Both candidate points lie in each interval, so their distance is bounded by
that interval's width. The widths tend to zero.
-/
theorem eq_semanticValue_of_mem_all_intervals
    (x : DkMath.Analysis.DkReal) (r : ℝ)
    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
    r = semanticValue x := by
  have hbound :
      ∀ n, |r - semanticValue x| ≤ widthReal x n := by
    intro n
    have hs := semanticValue_mem_interval x n
    rcases hr n with ⟨hrlo, hrhi⟩
    rcases hs with ⟨hslo, hshi⟩
    rw [abs_sub_le_iff]
    constructor <;> simp only [widthReal] <;> linarith
  have hzero :
      Filter.Tendsto (fun _ : ℕ => |r - semanticValue x|)
        Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound (tendsto_widthReal_zero x)
  have heq : |r - semanticValue x| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hzero
  exact sub_eq_zero.mp (abs_eq_zero.mp heq)

/--
Equivalent interval representations select the same semantic real.

The rational lower-endpoint difference tends to zero by representation
equivalence. Continuity of the rational embedding transfers that convergence
to `Real`, while the two lower-endpoint sequences converge to their respective
semantic values.
-/
theorem semanticValue_eq_of_equiv
    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
    semanticValue x = semanticValue y := by
  have hxyRat := equiv_tendsto_lo_sub_zero hxy
  have hxyReal :
      Filter.Tendsto
        (fun n => lowerReal x n - lowerReal y n)
        Filter.atTop (nhds 0) := by
    have hcast :=
      Rat.continuous_coe_real.continuousAt.tendsto.comp hxyRat
    convert hcast using 1
    · funext n
      simp [lowerReal]
    · simp
  have hsemantic :
      Filter.Tendsto
        (fun n => lowerReal x n - lowerReal y n)
        Filter.atTop (nhds (semanticValue x - semanticValue y)) :=
    (tendsto_lowerReal_semanticValue x).sub
      (tendsto_lowerReal_semanticValue y)
  have hzero : semanticValue x - semanticValue y = 0 :=
    tendsto_nhds_unique hsemantic hxyReal
  exact sub_eq_zero.mp hzero

/-- Embedded rationals have their expected semantic value. -/
@[simp]
theorem semanticValue_ofRat (q : ℚ) :
    semanticValue (DkMath.Analysis.DkReal.ofRat q) = q := by
  symm
  apply eq_semanticValue_of_mem_all_intervals
  intro n
  simp [lowerReal, upperReal]

/-- Semantic evaluation preserves representation addition. -/
theorem semanticValue_add
    (x y : DkMath.Analysis.DkReal) :
    semanticValue (add x y) = semanticValue x + semanticValue y := by
  symm
  apply eq_semanticValue_of_mem_all_intervals
  intro n
  have hx := semanticValue_mem_interval x n
  have hy := semanticValue_mem_interval y n
  constructor
  · simpa [lowerReal, add_interval, addApprox] using
      _root_.add_le_add hx.1 hy.1
  · simpa [upperReal, add_interval, addApprox] using
      _root_.add_le_add hx.2 hy.2

/-- A nonnegative representation has a nonnegative semantic value. -/
theorem semanticValue_nonneg
    {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
    0 ≤ semanticValue x := by
  have hlo : (0 : ℝ) ≤ lowerReal x 0 := by
    simp only [lowerReal]
    exact_mod_cast hx 0
  exact hlo.trans (lowerReal_le_semanticValue x 0)

/--
Semantic evaluation preserves multiplication on the nonnegative quadrant.

The product of the two semantic points lies in every stagewise endpoint
product interval, so semantic uniqueness identifies it with the represented
product.
-/
theorem semanticValue_mulNonneg
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
    semanticValue (mulNonneg x y hx hy) =
      semanticValue x * semanticValue y := by
  symm
  apply eq_semanticValue_of_mem_all_intervals
  intro n
  have hxi := semanticValue_mem_interval x n
  have hyi := semanticValue_mem_interval y n
  have hxlo : (0 : ℝ) ≤ lowerReal x n := by
    simp only [lowerReal]
    exact_mod_cast hx n
  have hylo : (0 : ℝ) ≤ lowerReal y n := by
    simp only [lowerReal]
    exact_mod_cast hy n
  constructor
  · have h :=
      mul_le_mul hxi.1 hyi.1 hylo (semanticValue_nonneg hx)
    simpa [lowerReal, mulNonneg_interval, mulNonnegApprox] using h
  · have hxsem := semanticValue_nonneg hx
    have h :=
      mul_le_mul hxi.2 hyi.2 (semanticValue_nonneg hy)
        (hxsem.trans hxi.2)
    simpa [upperReal, mulNonneg_interval, mulNonnegApprox] using h

/-- Semantic evaluation preserves natural powers of nonnegative representations. -/
theorem semanticValue_powNonneg
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    semanticValue (powNonneg d x hx) = semanticValue x ^ d := by
  induction d with
  | zero =>
      calc
        semanticValue (powNonneg 0 x hx)
            = semanticValue (DkMath.Analysis.DkReal.ofRat 1) := by
                apply semanticValue_eq_of_equiv
                apply equiv_of_interval_eq
                intro n
                exact powNonneg_zero_interval x hx n
        _ = 1 := by
          simp
        _ = semanticValue x ^ 0 := by rw [pow_zero]
  | succ d ih =>
      calc
        semanticValue (powNonneg (d + 1) x hx)
            =
          semanticValue
            (mulNonneg (powNonneg d x hx) x
              (nonnegative_powNonneg d hx) hx) :=
          semanticValue_eq_of_equiv
            (equiv_of_interval_eq (powNonneg_succ_interval d x hx))
        _ = semanticValue (powNonneg d x hx) * semanticValue x :=
          semanticValue_mulNonneg _ _ (nonnegative_powNonneg d hx) hx
        _ = semanticValue x ^ d * semanticValue x := by rw [ih]
        _ = semanticValue x ^ (d + 1) := by rw [pow_succ]

end

end DkMath.Analysis.DkReal

namespace DkMath.Analysis.DkNNRealQ

noncomputable section

/--
Semantic evaluation of a quotient-backed nonnegative DkMath real.

Representative independence follows from
`DkReal.semanticValue_eq_of_equiv`.
-/
def semanticValue (x : DkNNRealQ) : ℝ :=
  Quotient.liftOn x
    (fun a => DkReal.semanticValue a.val)
    (fun _ _ h => DkReal.semanticValue_eq_of_equiv h)

/-- Semantic evaluation computes on quotient constructors. -/
@[simp]
theorem semanticValue_mk (x : DkNNReal) :
    semanticValue (mk x) = DkReal.semanticValue x.val := rfl

/-- Embedded nonnegative rationals have their expected semantic value. -/
@[simp]
theorem semanticValue_ofRat (q : ℚ) (hq : 0 ≤ q) :
    semanticValue (ofRat q hq) = q :=
  DkReal.semanticValue_ofRat q

/-- Quotient zero evaluates to real zero. -/
@[simp]
theorem semanticValue_zero :
    semanticValue 0 = 0 := by
  change semanticValue (ofRat 0 le_rfl) = 0
  simp

/-- Quotient one evaluates to real one. -/
@[simp]
theorem semanticValue_one :
    semanticValue 1 = 1 := by
  change semanticValue (ofRat 1 (by norm_num : (0 : ℚ) ≤ 1)) = 1
  simp

/-- Semantic evaluation preserves quotient addition. -/
theorem semanticValue_add (x y : DkNNRealQ) :
    semanticValue (x + y) = semanticValue x + semanticValue y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  exact DkReal.semanticValue_add x.val y.val

/-- Quotient semantic values are nonnegative. -/
theorem semanticValue_nonneg (x : DkNNRealQ) :
    0 ≤ semanticValue x := by
  refine Quotient.inductionOn x ?_
  intro x
  exact DkReal.semanticValue_nonneg x.nonnegative

/-- Semantic evaluation preserves quotient multiplication. -/
theorem semanticValue_mul (x y : DkNNRealQ) :
    semanticValue (x * y) = semanticValue x * semanticValue y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  exact DkReal.semanticValue_mulNonneg
    x.val y.val x.nonnegative y.nonnegative

/-- Semantic evaluation preserves quotient natural powers. -/
theorem semanticValue_pow (x : DkNNRealQ) (d : ℕ) :
    semanticValue (x ^ d) = semanticValue x ^ d := by
  refine Quotient.inductionOn x ?_
  intro x
  exact DkReal.semanticValue_powNonneg d x.val x.nonnegative

/--
Semantic evaluation preserves the canonical quotient order.

If `x ≤ y`, canonical order supplies a nonnegative Gap `z` with
`y = x + z`. Additivity then turns the order claim into nonnegativity of the
semantic Gap.
-/
theorem semanticValue_mono
    {x y : DkNNRealQ} (hxy : x ≤ y) :
    semanticValue x ≤ semanticValue y := by
  obtain ⟨z, rfl⟩ := exists_add_of_le hxy
  rw [semanticValue_add]
  exact le_add_of_nonneg_right (semanticValue_nonneg z)

end

end DkMath.Analysis.DkNNRealQ
