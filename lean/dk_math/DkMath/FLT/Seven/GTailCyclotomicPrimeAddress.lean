/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicLocalEval

#print "file: DkMath.FLT.Seven.GTailCyclotomicPrimeAddress"

/-!
# Packet-free prime kernels and Tail root orientation

These kernels belong to the existing degree-six ring. Root separation is
witnessed by an integral element; no product over all roots is asserted.
-/

namespace DkMath.FLT.Seven

open DkMath.Lib.NumberTheory SevenCyclotomicDegreeSixInt

/-- The actual degree-six kernel of a supplied nontrivial seventh root. -/
def seventhRootKernel {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1)

@[simp] theorem mem_seventhRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ seventhRootKernel r hr0 hr7 hr1 ↔ evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 z = 0 :=
  RingHom.mem_ker

/-- Embedded natural representatives cover the residue field. -/
theorem evalCyclotomicFromSeventhRoot_surjective {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Function.Surjective (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1) := by
  intro z
  refine ⟨ofReal (z.val : SevenRealCubicInt), ?_⟩
  rw [evalCyclotomicFromSeventhRoot_ofReal]
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- Surjectivity onto the prime field makes the kernel maximal. -/
theorem seventhRootKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (seventhRootKernel r hr0 hr7 hr1).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (evalCyclotomicFromSeventhRoot_surjective r hr0 hr7 hr1)

/-- The maximal kernel is in particular a prime ideal. -/
theorem seventhRootKernel_isPrime {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (seventhRootKernel r hr0 hr7 hr1).IsPrime :=
  (seventhRootKernel_isMaximal r hr0 hr7 hr1).isPrime

/-- Contraction to the real cubic is its trace-evaluation kernel. -/
theorem seventhRootKernel_comap_ofReal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal.comap ofReal (seventhRootKernel r hr0 hr7 hr1) =
      RingHom.ker (evalRealFromSeventhRoot r hr0 hr7 hr1) := by
  ext z
  change evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal z) = 0 ↔
    evalRealFromSeventhRoot r hr0 hr7 hr1 z = 0
  rw [evalCyclotomicFromSeventhRoot_ofReal]

/-- Integer contraction is precisely the rational prime ideal. -/
theorem seventhRootKernel_comap_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
      (seventhRootKernel r hr0 hr7 hr1) = Ideal.span ({(q : ℤ)} : Set ℤ) := by
  ext z
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  change evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal (z : SevenRealCubicInt)) = 0 ↔ _
  rw [evalCyclotomicFromSeventhRoot_ofReal, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The quotient is the field with q elements. -/
theorem seventhRootKernel_cardQuot {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Submodule.cardQuot (seventhRootKernel r hr0 hr7 hr1) = q := by
  rw [Submodule.cardQuot_apply]
  calc
    Nat.card (SevenCyclotomicDegreeSixInt.Ring ⧸ seventhRootKernel r hr0 hr7 hr1) =
        Nat.card (ZMod q) := Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective
        (evalCyclotomicFromSeventhRoot_surjective r hr0 hr7 hr1)).toEquiv
    _ = q := Nat.card_zmod q

/-- Endpoint cancellation selects the unique admissible root of the Tail factor. -/
theorem evalCyclotomic_linearFactor_eq_zero_iff {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (c g : ℕ) (hc : ¬ q ∣ c) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 (gtailCyclotomicLinearFactor c g) = 0 ↔
      s = gtailSevenTailRatio q c g := by
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  simp only [gtailCyclotomicLinearFactor, map_sub, map_mul,
    evalCyclotomicFromSeventhRoot_zeta, map_natCast]
  push_cast
  rw [sub_eq_zero]
  dsimp only [gtailSevenTailRatio]
  exact ⟨fun h => (eq_div_iff hc0).mpr h.symm, fun h => ((eq_div_iff hc0).mp h).symm⟩

/-- An explicit integral witness separates two root kernels. -/
theorem seventhRootKernel_separating_element {q : ℕ} [Fact (Nat.Prime q)]
    (r s : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1) (hrs : r ≠ s) :
    zeta - ofReal (r.val : SevenRealCubicInt) ∈ seventhRootKernel r hr0 hr7 hr1 ∧
      zeta - ofReal (r.val : SevenRealCubicInt) ∉ seventhRootKernel s hs0 hs7 hs1 := by
  simp only [mem_seventhRootKernel_iff, map_sub, evalCyclotomicFromSeventhRoot_zeta,
    map_natCast, ZMod.natCast_zmod_val]
  exact ⟨sub_self r, sub_ne_zero.mpr hrs.symm⟩

/-- Kernel inequality follows from the exhibited element, not merely different maps. -/
theorem seventhRootKernel_ne {q : ℕ} [Fact (Nat.Prime q)]
    (r s : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1) (hrs : r ≠ s) :
    seventhRootKernel r hr0 hr7 hr1 ≠ seventhRootKernel s hs0 hs7 hs1 := by
  obtain ⟨hm, hn⟩ := seventhRootKernel_separating_element r s hr0 hr7 hr1 hs0 hs7 hs1 hrs
  intro h
  exact hn (h ▸ hm)

/-- The canonical Tail address contains its factor; every distinct admissible root excludes it. -/
theorem gtailCyclotomicLinearFactor_unique_address {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c)
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (hsr : s ≠ gtailSevenTailRatio q c g) :
    gtailCyclotomicLinearFactor c g ∈ seventhRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) ∧
      gtailCyclotomicLinearFactor c g ∉ seventhRootKernel s hs0 hs7 hs1 := by
  refine ⟨gtailCyclotomicLinearFactor_mem_ker c g hc hg hT, ?_⟩
  rw [mem_seventhRootKernel_iff, evalCyclotomic_linearFactor_eq_zero_iff s hs0 hs7 hs1 c g hc]
  exact hsr

end DkMath.FLT.Seven
