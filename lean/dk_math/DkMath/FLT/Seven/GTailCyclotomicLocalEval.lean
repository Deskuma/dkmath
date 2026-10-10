/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier
import DkMath.Lib.NumberTheory.GTailSevenRealTraceResidue

#print "file: DkMath.FLT.Seven.GTailCyclotomicLocalEval"

/-!
# Packet-free cyclotomic residue evaluation

The source is the existing real-cubic and degree-six carrier. No signed-depth
packet, Eisenstein source map, or ideal transport is constructed here.
-/

namespace DkMath.FLT.Seven

open DkMath.Lib.NumberTheory

/-- Evaluate the actual signed integral cubic basis at the trace of a seventh root. -/
def evalRealFromSeventhRoot {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    SevenRealCubicInt →+* ZMod q where
  toFun x := (x.fst : ZMod q) + (x.snd : ZMod q) * seventhRootBeta r +
    (x.thd : ZMod q) * seventhRootBeta r ^ 2
  map_zero' := by norm_num
  map_one' := by norm_num
  map_add' x y := by
    simp only [SevenRealCubicInt.fst_add, SevenRealCubicInt.snd_add,
      SevenRealCubicInt.thd_add, Int.cast_add]
    ring
  map_mul' x y := by
    rcases x with ⟨x0, x1, x2⟩
    rcases y with ⟨y0, y1, y2⟩
    simp only [SevenRealCubicInt.fst_mul, SevenRealCubicInt.snd_mul,
      SevenRealCubicInt.thd_mul, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_ofNat]
    linear_combination
      -((x1 : ZMod q) * (y2 : ZMod q) + (x2 : ZMod q) * (y1 : ZMod q) +
        (x2 : ZMod q) * (y2 : ZMod q) * seventhRootBeta r +
        2 * (x2 : ZMod q) * (y2 : ZMod q)) * seventhRootBeta_cubic r hr0 hr7 hr1

@[simp] theorem evalRealFromSeventhRoot_alpha {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalRealFromSeventhRoot r hr0 hr7 hr1 SevenRealCubicInt.alpha = seventhRootBeta r := by
  norm_num [evalRealFromSeventhRoot, SevenRealCubicInt.alpha]

@[simp] theorem evalRealFromSeventhRoot_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (n : ℤ) :
    evalRealFromSeventhRoot r hr0 hr7 hr1 (n : SevenRealCubicInt) = (n : ZMod q) :=
  map_intCast _ n

open SevenCyclotomicDegreeSixInt

/-- Evaluate the existing degree-six carrier, with the checked cubic base and quadratic sign. -/
def evalCyclotomicFromSeventhRoot {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : SevenCyclotomicDegreeSixInt.Ring →+* ZMod q where
  toFun x := evalRealFromSeventhRoot r hr0 hr7 hr1 x.re +
    r * evalRealFromSeventhRoot r hr0 hr7 hr1 x.im
  map_zero' := by
    simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, map_zero, mul_zero, add_zero]
  map_one' := by
    simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_one, map_zero,
      mul_zero, add_zero]
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
    ring
  map_mul' x y := by
    have hr := seventhRootBeta_quadratic r hr0
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      map_neg, map_sub, map_one, evalRealFromSeventhRoot_alpha]
    linear_combination
      -(evalRealFromSeventhRoot r hr0 hr7 hr1 x.im *
        evalRealFromSeventhRoot r hr0 hr7 hr1 y.im) * hr

@[simp] theorem evalCyclotomicFromSeventhRoot_zeta {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 zeta = r := by
  simp [evalCyclotomicFromSeventhRoot, zeta]

@[simp] theorem evalCyclotomicFromSeventhRoot_ofReal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (x : SevenRealCubicInt) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal x) =
      evalRealFromSeventhRoot r hr0 hr7 hr1 x := by
  simp [evalCyclotomicFromSeventhRoot, ofReal, QuadraticAlgebra.algebraMap_eq]

@[simp] theorem evalCyclotomicFromSeventhRoot_alpha {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal SevenRealCubicInt.alpha) =
      seventhRootBeta r := by
  rw [evalCyclotomicFromSeventhRoot_ofReal, evalRealFromSeventhRoot_alpha]

/-- The coordinate-specific linear factor for the natural Tail ratio. -/
def gtailCyclotomicLinearFactor (c g : ℕ) : SevenCyclotomicDegreeSixInt.Ring :=
  ofReal ((c + g : ℕ) : SevenRealCubicInt) - zeta * ofReal (c : SevenRealCubicInt)

/-- A packet-free evaluation instantiated at the actual natural Tail ratio. -/
def gtailCyclotomicEval {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
  evalCyclotomicFromSeventhRoot (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
    (gtailSevenTailRatio_ne_one hc hg)

/-- The oriented Tail linear factor vanishes under its actual degree-six evaluation. -/
theorem gtailCyclotomicEval_linearFactor {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicEval c g hc hg hT (gtailCyclotomicLinearFactor c g) = 0 := by
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  simp only [gtailCyclotomicEval, gtailCyclotomicLinearFactor, map_sub, map_mul,
    evalCyclotomicFromSeventhRoot_zeta, map_natCast]
  push_cast
  apply sub_eq_zero.mpr
  dsimp only [gtailSevenTailRatio]
  exact (div_mul_cancel₀ _ hc0).symm

/-- Actual kernel membership, in the cyclotomic carrier alone. -/
theorem gtailCyclotomicLinearFactor_mem_ker {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicLinearFactor c g ∈ RingHom.ker (gtailCyclotomicEval c g hc hg hT) :=
  gtailCyclotomicEval_linearFactor c g hc hg hT

end DkMath.FLT.Seven
