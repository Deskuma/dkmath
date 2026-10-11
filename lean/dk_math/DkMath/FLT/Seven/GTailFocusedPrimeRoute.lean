/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver

#print "file: DkMath.FLT.Seven.GTailFocusedPrimeRoute"

/-!
# Total focused prime routing

The Gap case has canonical ratio one. Only the Tail case feeds the existing
native common receiver. This conditional interface supplies no contradiction
or signed primitive descent reconstruction.
-/

namespace DkMath.FLT.Seven.GTailFocusedPrimeRoute

open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open GTailCommonReceiver GTailGenericPrimeReceiver

/-- Gap support makes the actual ratio one when its denominator is a unit. -/
theorem gap_ratio_eq_one {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hg : q ∣ g) : gtailSevenTailRatio q c g = 1 := by
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  have hg0 : (g : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff g q).mpr hg
  apply (div_eq_iff hc0).mpr
  simp only [hg0, add_zero, one_mul]

/-- These same Gap data fail the canonical nonidentity Tail-root guard. -/
theorem gap_nonidentity_guard_unavailable {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hg : q ∣ g) : ¬ (gtailSevenTailRatio q c g ≠ 1) := by
  exact fun h => h (gap_ratio_eq_one hc hg)

/-- Coordinate and endpoint units are obtained before either branch is selected. -/
theorem focused_coordinate_units {q a b c : ℕ} [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (¬ q ∣ a) ∧ (¬ q ∣ b) ∧ (¬ q ∣ a + b) ∧ (¬ q ∣ c) := by
  have hu := not_prime_dvd_coordinate_product_of_quadratic (Fact.out : Nat.Prime q) hcop hQ
  exact ⟨fun hd => hu (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _),
    fun hd => hu (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _),
    fun hd => hu (dvd_mul_of_dvd_right hd _),
    not_prime_dvd_endpoint_of_quadratic (Fact.out : Nat.Prime q) hcop hEq hQ⟩

/-- Every eligible quadratic prime routes to Gap or Tail, without an entry Tail premise. -/
theorem focused_prime_route {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c ∧ gtailSevenTailRatio q c g = 1) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g ∧ q ∣ GTail 7 1 g c) := by
  have hu := focused_coordinate_units hcop hEq hQ
  rcases prime_square_focused_allocation ha hb hcop hEq hfocus
    (Fact.out : Nat.Prime q) hq7 hQ with h | h
  · exact Or.inl ⟨h.1, h.2, gap_ratio_eq_one hu.2.2.2
      ((dvd_pow_self q (by decide : 2 ≠ 0)).trans h.1)⟩
  · exact Or.inr ⟨h.1, h.2, (dvd_pow_self q (by decide : 2 ≠ 0)).trans h.1⟩

/-- Only a proved Tail branch attaches the existing typed receiver and all bounded readouts. -/
theorem tail_receiver {q a b c g : ℕ} [Fact (Nat.Prime q)] (ha : 0 < a) (hbpos : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hfocus : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    let hT : q ∣ GTail 7 1 g c := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hT2
    let hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
    let J := nativeKernel a b c g hQ hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hT
    (J = Ideal.map fromEisenstein
      (eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hu.2.1)) ⊔
      Ideal.map fromCyclotomic (seventhRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT) (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
        (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1))) ∧
    (J.IsMaximal ∧
    Ideal.comap fromEisenstein J = eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
      (gtailSevenResidueRoot_polynomial hQ hu.2.1) ∧
    Ideal.comap fromCyclotomic J = seventhRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT) (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
      (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1) ∧
    fromEisenstein (gtailSevenNormCoord a b) ∈ J ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ∧
    padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
    Even (padicValNat q (GTail 7 1 g c)) ∧ q ^ 2 ∣ GTail 7 1 g c ∧
    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c) ∧
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) ∈ J ^ 2 ∧
    fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 2 ∧
    fromEisenstein (gtailSevenNormCoord a b) * fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 3 ∧
    fromEisenstein ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2) *
      fromCyclotomic (gtailCyclotomicFactor c g 0) ∈ J ^ 4) := by
  have hT : q ∣ GTail 7 1 g c := (dvd_pow_self q (by decide : 2 ≠ 0)).trans hT2
  exact ⟨pairedKernel_eq_sup _ _ _ _ _ _,
    focused_receiver a b c g ha hbpos hcop hEq hfocus hq7 hQ hT⟩

/-- An E coordinate with unit b differs from every coefficient-ring image in C. -/
theorem norm_image_ne_cyclotomic {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (a b : ℕ) (hb : ¬ q ∣ b) (u : SevenCyclotomicDegreeSixInt.Ring) :
    fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic u := by
  intro h
  have him : ((b : ℤ) : SevenCyclotomicDegreeSixInt.Ring) = 0 := by
    simpa [fromEisenstein, fromCyclotomic, QuadraticAlgebra.algebraMap_eq,
      gtailSevenNormCoord_eq] using congrArg (fun x : Carrier => x.im) h
  have he := congrArg (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1) him
  have hb0 : (b : ZMod q) = 0 := by
    simpa only [map_intCast, map_natCast, map_zero, Int.cast_natCast] using he
  exact hb ((ZMod.natCast_eq_zero_iff b q).mp hb0)

/-- The actual Tail source images stay distinct even though both residues vanish. -/
theorem tail_source_images_ne {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c)
    (hfocus : a + b = c + g) (hq7 : q ≠ 7)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic (gtailCyclotomicFactor c g 0) := by
  have hu := focused_norm_depth_guards hcop hEq hfocus hq7 hQ hT
  exact norm_image_ne_cyclotomic (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT) (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
    (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1) a b hu.2.1 _

end DkMath.FLT.Seven.GTailFocusedPrimeRoute
