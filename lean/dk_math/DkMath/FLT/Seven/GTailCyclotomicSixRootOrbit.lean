/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailCyclotomicPrimeAddress

#print "file: DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit"

/-!
# Six explicit seventh-root slots

The supplied nontrivial root generates six distinct prime kernels. Selective
Tail membership does not identify their intersection or product with (q).
-/

namespace DkMath.FLT.Seven

open DkMath.Lib.NumberTheory

/-- Ascending positive proper powers of a supplied seventh root. -/
def sixSlotRoot {q : ℕ} (r : ZMod q) (i : Fin 6) : ZMod q := r ^ (i.val + 1)

/-- Prime exponent seven fixes the order of a nonidentity seventh root. -/
theorem seventhRoot_orderOf {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    orderOf r = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime hr7 hr1

@[simp] theorem sixSlotRoot_zero {q : ℕ} (r : ZMod q) : sixSlotRoot r 0 = r := by
  simp [sixSlotRoot]

/-- Every slot retains the seventh-power identity. -/
theorem sixSlotRoot_pow_seven {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (i : Fin 6) :
    sixSlotRoot r i ^ 7 = 1 := by
  rw [sixSlotRoot, ← pow_mul, Nat.mul_comm, pow_mul, hr7, one_pow]

/-- Powers of a nonzero root remain nonzero. -/
theorem sixSlotRoot_ne_zero {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (i : Fin 6) : sixSlotRoot r i ≠ 0 := pow_ne_zero _ hr0

/-- Exponents one through six cannot return to the identity at order seven. -/
theorem sixSlotRoot_ne_one {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i : Fin 6) : sixSlotRoot r i ≠ 1 := by
  have ho := seventhRoot_orderOf r hr7 hr1
  intro h
  have he : i.val + 1 = 0 := pow_injOn_Iio_orderOf
    (by change i.val + 1 < orderOf r; rw [ho]; omega)
    (by change 0 < orderOf r; rw [ho]; decide)
    (by simpa only [sixSlotRoot, pow_zero] using h)
  omega

/-- Genuine finite-order injectivity distinguishes the six exponents. -/
theorem sixSlotRoot_injective {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Function.Injective (sixSlotRoot r) := by
  have ho := seventhRoot_orderOf r hr7 hr1
  intro i j h
  have he : i.val + 1 = j.val + 1 := pow_injOn_Iio_orderOf
    (by change i.val + 1 < orderOf r; rw [ho]; omega)
    (by change j.val + 1 < orderOf r; rw [ho]; omega) h
  apply Fin.ext
  omega

/-- The actual degree-six prime kernel at one supplied root-power slot. -/
def sixRootKernel {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  seventhRootKernel (sixSlotRoot r i) (sixSlotRoot_ne_zero r hr0 i)
    (sixSlotRoot_pow_seven r hr7 i) (sixSlotRoot_ne_one r hr7 hr1 i)

@[simp] theorem mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ sixRootKernel r hr0 hr7 hr1 i ↔
      evalCyclotomicFromSeventhRoot (sixSlotRoot r i) (sixSlotRoot_ne_zero r hr0 i)
        (sixSlotRoot_pow_seven r hr7 i) (sixSlotRoot_ne_one r hr7 hr1 i) z = 0 :=
  mem_seventhRootKernel_iff _ _ _ _ z

/-- Each slot is maximal by the existing packet-free receiver. -/
theorem sixRootKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    (sixRootKernel r hr0 hr7 hr1 i).IsMaximal := seventhRootKernel_isMaximal _ _ _ _

/-- Each slot is prime by the existing packet-free receiver. -/
theorem sixRootKernel_isPrime {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    (sixRootKernel r hr0 hr7 hr1 i).IsPrime := seventhRootKernel_isPrime _ _ _ _

/-- All six prime slots contract to the same rational prime. -/
theorem sixRootKernel_comap_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
      (sixRootKernel r hr0 hr7 hr1 i) = Ideal.span ({(q : ℤ)} : Set ℤ) :=
  seventhRootKernel_comap_intCast _ _ _ _

/-- Every slot has residue cardinality q. -/
theorem sixRootKernel_cardQuot {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Submodule.cardQuot (sixRootKernel r hr0 hr7 hr1 i) = q := seventhRootKernel_cardQuot _ _ _ _

/-- The existing separating-element theorem distinguishes the slot kernels. -/
theorem sixRootKernel_ne {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i j : Fin 6) (hij : i ≠ j) :
    sixRootKernel r hr0 hr7 hr1 i ≠ sixRootKernel r hr0 hr7 hr1 j := by
  apply seventhRootKernel_ne
  exact fun h => hij (sixSlotRoot_injective r hr7 hr1 h)

/-- Distinct actual maximal ideals are comaximal. -/
theorem sixRootKernel_sup_eq_top {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i j : Fin 6) (hij : i ≠ j) :
    sixRootKernel r hr0 hr7 hr1 i ⊔ sixRootKernel r hr0 hr7 hr1 j = ⊤ := by
  let : (sixRootKernel r hr0 hr7 hr1 i).IsMaximal := sixRootKernel_isMaximal r hr0 hr7 hr1 i
  let : (sixRootKernel r hr0 hr7 hr1 j).IsMaximal := sixRootKernel_isMaximal r hr0 hr7 hr1 j
  exact (Ideal.isCoprime_of_isMaximal (sixRootKernel_ne r hr0 hr7 hr1 i j hij)).sup_eq

/-- Exactly the first of the six supplied root slots supports the actual Tail factor. -/
theorem gtailCyclotomicLinearFactor_mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicLinearFactor c g ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) i ↔ i = 0 := by
  rw [mem_sixRootKernel_iff, evalCyclotomic_linearFactor_eq_zero_iff _ _ _ _ c g hc]
  simpa only [sixSlotRoot_zero] using
    (show sixSlotRoot (gtailSevenTailRatio q c g) i =
        sixSlotRoot (gtailSevenTailRatio q c g) 0 ↔ i = 0 from
      (sixSlotRoot_injective _ (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg)).eq_iff)

/-- Membership in the first slot, as a direct receiver. -/
theorem gtailCyclotomicLinearFactor_mem_sixRootKernel_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicLinearFactor c g ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) 0 :=
  (gtailCyclotomicLinearFactor_mem_sixRootKernel_iff c g hc hg hT 0).mpr rfl

/-- The other five supplied slots exclude the Tail factor. -/
theorem gtailCyclotomicLinearFactor_not_mem_sixRootKernel {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) (i : Fin 6) (hi : i ≠ 0) :
    gtailCyclotomicLinearFactor c g ∉ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) i := by
  rw [gtailCyclotomicLinearFactor_mem_sixRootKernel_iff c g hc hg hT i]
  exact hi

end DkMath.FLT.Seven
