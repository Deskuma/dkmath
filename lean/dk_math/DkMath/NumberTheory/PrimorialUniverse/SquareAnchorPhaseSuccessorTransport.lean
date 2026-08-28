/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexCenterTransport
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOrbit
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport"

/-!
# Square-anchor canonical phase transport

PUU-L027 turns the static center/radius normal form into a successor law for
the moving square anchor.  The canonical old representative is `n % M`,
whereas the square-value coordinate remains `n^2 % M`.  The resulting finite
transport records the period carry, center drift, and the two dynamic phase
sheets without making an escape or prime-existence claim.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-! ## Canonical phase representative -/

/-- The canonical old-period anchor coordinate of the moving anchor `n`. -/
def squareAnchorPhaseRepresentative (S : Finset ℕ) (n : ℕ) : ℕ :=
  primeBasisWheelProjection S n

/-- The canonical representative lies in the square-phase fiber of `n`. -/
theorem squareAnchorPhaseRepresentative_mem_phaseFiber
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseRepresentative S n ∈ squareAnchorPhaseFiber S n := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  apply mem_squareAnchorPhaseFiber.mpr
  constructor
  · exact Nat.mod_lt n hMpos
  · change n ^ 2 % finitePrimeBasisProduct S =
      (n % finitePrimeBasisProduct S) ^ 2 % finitePrimeBasisProduct S
    exact Nat.pow_mod n 2 (finitePrimeBasisProduct S)

/-- The square-value projection is the square of the canonical representative. -/
theorem squareAnchorWheelProjection_eq_representative_square
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorWheelProjection S n =
      (squareAnchorPhaseRepresentative S n) ^ 2 %
        finitePrimeBasisProduct S := by
  change n ^ 2 % finitePrimeBasisProduct S =
    (n % finitePrimeBasisProduct S) ^ 2 % finitePrimeBasisProduct S
  exact Nat.pow_mod n 2 (finitePrimeBasisProduct S)

/-! ## Successor and carry -/

/-- The canonical representative advances by `+1` modulo the old period. -/
theorem squareAnchorPhaseRepresentative_succ
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseRepresentative S (n + 1) =
      (squareAnchorPhaseRepresentative S n + 1) %
        finitePrimeBasisProduct S := by
  simp [squareAnchorPhaseRepresentative, primeBasisWheelProjection,
    Nat.add_mod]

/-- The carry records a wrap of the canonical representative at the old period. -/
def squareAnchorPhaseStepCarry (S : Finset ℕ) (n : ℕ) : ℕ :=
  (squareAnchorPhaseRepresentative S n + 1) /
    finitePrimeBasisProduct S

/-- The representative successor decomposes into residue plus one period carry. -/
theorem squareAnchorPhaseRepresentative_succ_decomposition
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseRepresentative S n + 1 =
      squareAnchorPhaseRepresentative S (n + 1) +
        squareAnchorPhaseStepCarry S n * finitePrimeBasisProduct S := by
  have hdecomp := Nat.mod_add_div'
    (squareAnchorPhaseRepresentative S n + 1) (finitePrimeBasisProduct S)
  rw [squareAnchorPhaseRepresentative_succ hS n]
  exact hdecomp.symm

/-- The finite-wheel carry is always either zero or one. -/
theorem squareAnchorPhaseStepCarry_le_one
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseStepCarry S n ≤ 1 := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hrlt : squareAnchorPhaseRepresentative S n <
      finitePrimeBasisProduct S := by
    exact Nat.mod_lt n hMpos
  have hsum_le : squareAnchorPhaseRepresentative S n + 1 ≤
      finitePrimeBasisProduct S := by omega
  have hcarry_lt : squareAnchorPhaseStepCarry S n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hMpos).2
    omega
  omega

/-- Carry one is exactly the representative wrap branch. -/
theorem squareAnchorPhaseStepCarry_eq_one_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseStepCarry S n = 1 ↔
      squareAnchorPhaseRepresentative S n + 1 =
        finitePrimeBasisProduct S := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hrlt : squareAnchorPhaseRepresentative S n <
      finitePrimeBasisProduct S := by
    exact Nat.mod_lt n hMpos
  have hdecomp := squareAnchorPhaseRepresentative_succ_decomposition hS n
  constructor
  · intro hcarry
    rw [hcarry] at hdecomp
    have hnextlt : squareAnchorPhaseRepresentative S (n + 1) <
        finitePrimeBasisProduct S := Nat.mod_lt _ hMpos
    omega
  · intro hwrap
    dsimp [squareAnchorPhaseStepCarry]
    rw [hwrap, Nat.div_self hMpos]

/-- Carry zero is exactly the non-wrapping branch. -/
theorem squareAnchorPhaseStepCarry_eq_zero_iff
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseStepCarry S n = 0 ↔
      squareAnchorPhaseRepresentative S n + 1 <
        finitePrimeBasisProduct S := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hrlt : squareAnchorPhaseRepresentative S n <
      finitePrimeBasisProduct S := by
    exact Nat.mod_lt n hMpos
  have hdecomp := squareAnchorPhaseRepresentative_succ_decomposition hS n
  constructor
  · intro hcarry
    rw [hcarry] at hdecomp
    have hnextlt : squareAnchorPhaseRepresentative S (n + 1) <
        finitePrimeBasisProduct S := Nat.mod_lt _ hMpos
    omega
  · intro hlt
    exact Nat.div_eq_of_lt hlt

/-! ## Moving center and radius -/

/-- The canonical deleted center over the moving square anchor. -/
noncomputable def squareAnchorFreshPrimeCenter
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  freshPrimeDeletedCenterCoord S q (squareAnchorPhaseRepresentative S n)

/-- The phase radius attached to the moving anchor `n`. -/
noncomputable def squareAnchorFreshPrimeRadius
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  freshPrimePhaseRadius S q n

/-- The moving radius advances by the unit inverse-period coordinate. -/
theorem squareAnchorFreshPrimeRadius_succ
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S)
    {q n : ℕ} :
    squareAnchorFreshPrimeRadius S q (n + 1) -
        squareAnchorFreshPrimeRadius S q n =
      freshPrimePhaseRadius S q 1 := by
  simp [squareAnchorFreshPrimeRadius, freshPrimePhaseRadius]
  ring

/-- The moving deleted center obeys the carry-corrected transport law. -/
theorem squareAnchorFreshPrimeCenter_succ
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q n : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    squareAnchorFreshPrimeCenter S q (n + 1) -
        squareAnchorFreshPrimeCenter S q n =
      (squareAnchorPhaseStepCarry S n : ZMod q) -
        freshPrimePhaseRadius S q 1 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hdecomp := squareAnchorPhaseRepresentative_succ_decomposition hS n
  have hdecompZ :
      (squareAnchorPhaseRepresentative S n : ZMod q) + 1 =
        (squareAnchorPhaseRepresentative S (n + 1) : ZMod q) +
          (squareAnchorPhaseStepCarry S n : ZMod q) *
            (finitePrimeBasisProduct S : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
      congrArg (fun x : ℕ => (x : ZMod q)) hdecomp
  have hcenter := freshPrime_deleted_center_transport
    (S := S) (q := q)
    (b₁ := squareAnchorPhaseRepresentative S n)
    (b₂ := squareAnchorPhaseRepresentative S (n + 1))
  have hMi : (finitePrimeBasisProduct S : ZMod q) *
      (finitePrimeBasisProduct S : ZMod q)⁻¹ = 1 :=
    mul_inv_cancel₀ hM
  unfold squareAnchorFreshPrimeCenter
  rw [hcenter]
  calc
    ((squareAnchorPhaseRepresentative S n : ZMod q) -
        (squareAnchorPhaseRepresentative S (n + 1) : ZMod q)) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ =
        ((squareAnchorPhaseStepCarry S n : ZMod q) *
            (finitePrimeBasisProduct S : ZMod q) - 1) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
      have hdiffZ :
          (squareAnchorPhaseRepresentative S n : ZMod q) -
              (squareAnchorPhaseRepresentative S (n + 1) : ZMod q) =
            (squareAnchorPhaseStepCarry S n : ZMod q) *
                (finitePrimeBasisProduct S : ZMod q) - 1 := by
        linear_combination hdecompZ
      rw [hdiffZ]
    _ = (squareAnchorPhaseStepCarry S n : ZMod q) -
        (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
      calc
        ((squareAnchorPhaseStepCarry S n : ZMod q) *
              (finitePrimeBasisProduct S : ZMod q) - 1) *
            (finitePrimeBasisProduct S : ZMod q)⁻¹ =
          (squareAnchorPhaseStepCarry S n : ZMod q) *
              ((finitePrimeBasisProduct S : ZMod q) *
                (finitePrimeBasisProduct S : ZMod q)⁻¹) -
            1 * (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
              rw [sub_mul, mul_assoc]
        _ = (squareAnchorPhaseStepCarry S n : ZMod q) -
            (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
              rw [hMi, mul_one, one_mul]
    _ = (squareAnchorPhaseStepCarry S n : ZMod q) -
        freshPrimePhaseRadius S q 1 := by
      simp [freshPrimePhaseRadius]

/-! ## Dynamic phase coordinates -/

/-- The plus phase coordinate attached to the moving anchor. -/
noncomputable def squareAnchorFreshPrimePlus
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  squareAnchorFreshPrimeCenter S q n + squareAnchorFreshPrimeRadius S q n

/-- The minus phase coordinate attached to the moving anchor. -/
noncomputable def squareAnchorFreshPrimeMinus
    (S : Finset ℕ) (q n : ℕ) : ZMod q :=
  squareAnchorFreshPrimeCenter S q n - squareAnchorFreshPrimeRadius S q n

/-- The plus sheet moves exactly by the period carry. -/
theorem squareAnchorFreshPrimePlus_succ
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q n : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    squareAnchorFreshPrimePlus S q (n + 1) -
        squareAnchorFreshPrimePlus S q n =
      (squareAnchorPhaseStepCarry S n : ZMod q) := by
  have hc := squareAnchorFreshPrimeCenter_succ hS (q := q) (n := n) hq hqS
  have hr := squareAnchorFreshPrimeRadius_succ hS (q := q) (n := n)
  unfold squareAnchorFreshPrimePlus
  linear_combination hc + hr

/-- The minus sheet has the carry drift minus twice the unit radius. -/
theorem squareAnchorFreshPrimeMinus_succ
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q n : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    squareAnchorFreshPrimeMinus S q (n + 1) -
        squareAnchorFreshPrimeMinus S q n =
      (squareAnchorPhaseStepCarry S n : ZMod q) -
        2 * freshPrimePhaseRadius S q 1 := by
  have hc := squareAnchorFreshPrimeCenter_succ hS (q := q) (n := n) hq hqS
  have hr := squareAnchorFreshPrimeRadius_succ hS (q := q) (n := n)
  unfold squareAnchorFreshPrimeMinus
  linear_combination hc - hr

/-! ## Connection with distinguished fresh-prime lift witnesses -/

/-- A deleted witness over the canonical representative is the moving center. -/
theorem squareAnchorFreshPrimeDeletedIndex_eq_center
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q n jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hzero : IsFreshPrimeDeletedLiftIndex S q
      (squareAnchorPhaseRepresentative S n) jzero) :
    (jzero : ZMod q) = squareAnchorFreshPrimeCenter S q n := by
  exact freshPrime_deleted_index_eq_centerCoord hS hq hqS hzero

/-- A plus witness over the canonical representative is the moving plus sheet. -/
theorem squareAnchorFreshPrimePlus_eq_of_witness
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a n jplus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hplus : IsFreshPrimePlusLiftIndex S q a
      (squareAnchorPhaseRepresentative S n) jplus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q
      (squareAnchorPhaseRepresentative S n) jzero) :
    (jplus : ZMod q) = squareAnchorFreshPrimeCenter S q n +
      squareAnchorFreshPrimeRadius S q a := by
  exact freshPrime_plus_index_eq_centerCoord_add_radius hS hq hqS hplus hzero

/-- A minus witness over the canonical representative is the moving minus sheet. -/
theorem squareAnchorFreshPrimeMinus_eq_of_witness
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a n jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hminus : IsFreshPrimeMinusLiftIndex S q a
      (squareAnchorPhaseRepresentative S n) jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q
      (squareAnchorPhaseRepresentative S n) jzero) :
    (jminus : ZMod q) = squareAnchorFreshPrimeCenter S q n -
      squareAnchorFreshPrimeRadius S q a := by
  exact freshPrime_minus_index_eq_centerCoord_sub_radius hS hq hqS hminus hzero

/-! ## Visible non-wrap / wrap regression -/

/-- The `{2, 3}` representative orbit exhibits both carry branches at `q = 5`. -/
theorem squareAnchorPhaseSuccessorTransport_two_three_four_five_six_regression :
    squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 4 = 4 ∧
      squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 5 = 5 ∧
      squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 6 = 0 ∧
      squareAnchorPhaseStepCarry ({2, 3} : Finset ℕ) 4 = 0 ∧
      squareAnchorPhaseStepCarry ({2, 3} : Finset ℕ) 5 = 1 ∧
      squareAnchorFreshPrimeCenter ({2, 3} : Finset ℕ) 5 5 -
          squareAnchorFreshPrimeCenter ({2, 3} : Finset ℕ) 5 4 =
        -freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      squareAnchorFreshPrimeCenter ({2, 3} : Finset ℕ) 5 6 -
          squareAnchorFreshPrimeCenter ({2, 3} : Finset ℕ) 5 5 =
        (1 : ZMod 5) - freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 5 -
          squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 =
        (0 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 6 -
          squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 5 =
        (1 : ZMod 5) ∧
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 5 -
          squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 4 =
        -2 * freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 ∧
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 6 -
          squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 5 =
        (1 : ZMod 5) - 2 * freshPrimePhaseRadius ({2, 3} : Finset ℕ) 5 1 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hrep4 : squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 4 = 4 := by
    norm_num [squareAnchorPhaseRepresentative, primeBasisWheelProjection,
      finitePrimeBasisProduct]
  have hrep5 : squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 5 = 5 := by
    norm_num [squareAnchorPhaseRepresentative, primeBasisWheelProjection,
      finitePrimeBasisProduct]
  have hrep6 : squareAnchorPhaseRepresentative ({2, 3} : Finset ℕ) 6 = 0 := by
    norm_num [squareAnchorPhaseRepresentative, primeBasisWheelProjection,
      finitePrimeBasisProduct]
  have hcarry4 : squareAnchorPhaseStepCarry ({2, 3} : Finset ℕ) 4 = 0 := by
    norm_num [squareAnchorPhaseStepCarry, squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, finitePrimeBasisProduct]
  have hcarry5 : squareAnchorPhaseStepCarry ({2, 3} : Finset ℕ) 5 = 1 := by
    norm_num [squareAnchorPhaseStepCarry, squareAnchorPhaseRepresentative,
      primeBasisWheelProjection, finitePrimeBasisProduct]
  have hc4 := squareAnchorFreshPrimeCenter_succ hS
    (q := 5) (n := 4) (by norm_num) (by simp)
  have hc5 := squareAnchorFreshPrimeCenter_succ hS
    (q := 5) (n := 5) (by norm_num) (by simp)
  have hp4 := squareAnchorFreshPrimePlus_succ hS
    (q := 5) (n := 4) (by norm_num) (by simp)
  have hp5 := squareAnchorFreshPrimePlus_succ hS
    (q := 5) (n := 5) (by norm_num) (by simp)
  have hm4 := squareAnchorFreshPrimeMinus_succ hS
    (q := 5) (n := 4) (by norm_num) (by simp)
  have hm5 := squareAnchorFreshPrimeMinus_succ hS
    (q := 5) (n := 5) (by norm_num) (by simp)
  refine ⟨hrep4, hrep5, hrep6, hcarry4, hcarry5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcarry4] using hc4
  · simpa [hcarry5] using hc5
  · simpa [hcarry4] using hp4
  · simpa [hcarry5] using hp5
  · simpa [hcarry4] using hm4
  · simpa [hcarry5] using hm5

end DkMath.NumberTheory.PrimorialUniverse
