/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhasePeriodTransport"

/-!
# Square-anchor old-period monodromy

PUU-L028 packages the one-step transport of L027 into the Euclidean block
quotient of the old wheel.  If `M` is the old product, the canonical anchor
is `n % M`, the dynamic plus sheet is `(n / M : ZMod q)`, and one old-period
turn fixes the center while translating the two sheets by `(+1, -1)`.  These
are finite provider-side identities; no escape or prime-existence statement
is part of this module.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

/-- The Euclidean block number of `n` for the old finite prime basis. -/
def squareAnchorPhaseBlockQuotient (S : Finset ℕ) (n : ℕ) : ℕ :=
  n / finitePrimeBasisProduct S

/-- The canonical representative and block quotient give the exact Euclidean
decomposition of the moving anchor parameter. -/
theorem squareAnchorPhaseRepresentative_add_blockQuotient
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n : ℕ) :
    n = squareAnchorPhaseRepresentative S n +
      squareAnchorPhaseBlockQuotient S n * finitePrimeBasisProduct S := by
  simpa [squareAnchorPhaseRepresentative, squareAnchorPhaseBlockQuotient,
    primeBasisWheelProjection] using
    (Nat.mod_add_div' n (finitePrimeBasisProduct S)).symm

/-- The dynamic plus sheet is exactly the old-period block quotient modulo the
fresh prime. -/
theorem squareAnchorFreshPrimePlus_eq_blockQuotient
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimePlus S q n =
      (squareAnchorPhaseBlockQuotient S n : ZMod q) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hdecomp := squareAnchorPhaseRepresentative_add_blockQuotient hS n
  have hdecompZ :
      (n : ZMod q) =
        (squareAnchorPhaseRepresentative S n : ZMod q) +
          (squareAnchorPhaseBlockQuotient S n : ZMod q) *
            (finitePrimeBasisProduct S : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun x : ℕ => (x : ZMod q)) hdecomp
  have hMi : (finitePrimeBasisProduct S : ZMod q) *
      (finitePrimeBasisProduct S : ZMod q)⁻¹ = 1 :=
    mul_inv_cancel₀ hM
  unfold squareAnchorFreshPrimePlus squareAnchorFreshPrimeCenter
    squareAnchorFreshPrimeRadius freshPrimeDeletedCenterCoord
  calc
    -(squareAnchorPhaseRepresentative S n : ZMod q) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ +
        (n : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹ =
      ((n : ZMod q) - (squareAnchorPhaseRepresentative S n : ZMod q)) *
        (finitePrimeBasisProduct S : ZMod q)⁻¹ := by ring
    _ = ((squareAnchorPhaseBlockQuotient S n : ZMod q) *
          (finitePrimeBasisProduct S : ZMod q)) *
        (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
      have hdiff :
          (n : ZMod q) - (squareAnchorPhaseRepresentative S n : ZMod q) =
            (squareAnchorPhaseBlockQuotient S n : ZMod q) *
              (finitePrimeBasisProduct S : ZMod q) := by
        linear_combination hdecompZ
      rw [hdiff]
    _ = (squareAnchorPhaseBlockQuotient S n : ZMod q) := by
      rw [mul_assoc, hMi, mul_one]

/-- The L027 carry is the exact increment of the Euclidean block quotient. -/
theorem squareAnchorPhaseBlockQuotient_succ
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseBlockQuotient S (n + 1) =
      squareAnchorPhaseBlockQuotient S n + squareAnchorPhaseStepCarry S n := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  have hdecomp := squareAnchorPhaseRepresentative_add_blockQuotient hS n
  have hcarry := squareAnchorPhaseRepresentative_succ_decomposition hS n
  have hnext : n + 1 = squareAnchorPhaseRepresentative S (n + 1) +
      (squareAnchorPhaseBlockQuotient S n + squareAnchorPhaseStepCarry S n) *
        finitePrimeBasisProduct S := by
    calc
      n + 1 = (squareAnchorPhaseRepresentative S n +
          squareAnchorPhaseBlockQuotient S n * finitePrimeBasisProduct S) + 1 := by
            rw [← hdecomp]
      _ = (squareAnchorPhaseRepresentative S n + 1) +
          squareAnchorPhaseBlockQuotient S n * finitePrimeBasisProduct S := by omega
      _ = (squareAnchorPhaseRepresentative S (n + 1) +
          squareAnchorPhaseStepCarry S n * finitePrimeBasisProduct S) +
          squareAnchorPhaseBlockQuotient S n * finitePrimeBasisProduct S := by
            rw [hcarry]
      _ = squareAnchorPhaseRepresentative S (n + 1) +
          (squareAnchorPhaseBlockQuotient S n + squareAnchorPhaseStepCarry S n) *
            finitePrimeBasisProduct S := by ring
  have hstd := (Nat.mod_add_div' (n + 1) (finitePrimeBasisProduct S)).symm
  have hrem : (n + 1) % finitePrimeBasisProduct S =
      squareAnchorPhaseRepresentative S (n + 1) := by
    rfl
  have hprod :
      ((n + 1) / finitePrimeBasisProduct S) * finitePrimeBasisProduct S =
        (squareAnchorPhaseBlockQuotient S n + squareAnchorPhaseStepCarry S n) *
          finitePrimeBasisProduct S := by
    apply Nat.add_left_cancel (n := squareAnchorPhaseRepresentative S (n + 1))
    calc
      squareAnchorPhaseRepresentative S (n + 1) +
          ((n + 1) / finitePrimeBasisProduct S) * finitePrimeBasisProduct S = n + 1 := by
            rw [← hrem]
            exact hstd.symm
      _ = squareAnchorPhaseRepresentative S (n + 1) +
          (squareAnchorPhaseBlockQuotient S n + squareAnchorPhaseStepCarry S n) *
            finitePrimeBasisProduct S := hnext
  exact Nat.mul_right_cancel hMpos hprod

/-- The canonical representative returns after one old wheel period. -/
theorem squareAnchorPhaseRepresentative_add_period
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseRepresentative S
        (n + finitePrimeBasisProduct S) =
      squareAnchorPhaseRepresentative S n := by
  simp [squareAnchorPhaseRepresentative, primeBasisWheelProjection]

/-- The block quotient increases by one after one old wheel period. -/
theorem squareAnchorPhaseBlockQuotient_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n : ℕ) :
    squareAnchorPhaseBlockQuotient S
        (n + finitePrimeBasisProduct S) =
    squareAnchorPhaseBlockQuotient S n + 1 := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  simpa [squareAnchorPhaseBlockQuotient] using
    (Nat.add_mul_div_right n 1 hMpos)

/-- After one old-period turn, the deleted center is unchanged. -/
theorem squareAnchorFreshPrimeCenter_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (_hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeCenter S q (n + finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeCenter S q n := by
  rw [squareAnchorFreshPrimeCenter, squareAnchorFreshPrimeCenter,
    squareAnchorPhaseRepresentative_add_period hS]

/-- After one old-period turn, the radius advances by one fresh-prime unit. -/
theorem squareAnchorFreshPrimeRadius_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeRadius S q (n + finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeRadius S q n + 1 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  unfold squareAnchorFreshPrimeRadius freshPrimePhaseRadius
  have hMi : (finitePrimeBasisProduct S : ZMod q) *
      (finitePrimeBasisProduct S : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hM
  calc
    ((n + finitePrimeBasisProduct S : ℕ) : ZMod q) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ =
        ((n : ZMod q) + (finitePrimeBasisProduct S : ZMod q)) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
            norm_num [Nat.cast_add]
    _ = (n : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹ + 1 := by
      rw [add_mul, hMi]

/-- One old-period turn translates the plus sheet by `+1`. -/
theorem squareAnchorFreshPrimePlus_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimePlus S q (n + finitePrimeBasisProduct S) =
      squareAnchorFreshPrimePlus S q n + 1 := by
  rw [squareAnchorFreshPrimePlus, squareAnchorFreshPrimePlus,
    squareAnchorFreshPrimeCenter_add_period hS hq hqS,
    squareAnchorFreshPrimeRadius_add_period hS hq hqS]
  ring

/-- One old-period turn translates the minus sheet by `-1`. -/
theorem squareAnchorFreshPrimeMinus_add_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeMinus S q (n + finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeMinus S q n - 1 := by
  rw [squareAnchorFreshPrimeMinus, squareAnchorFreshPrimeMinus,
    squareAnchorFreshPrimeCenter_add_period hS hq hqS,
    squareAnchorFreshPrimeRadius_add_period hS hq hqS]
  ring

/-- The canonical representative is invariant under any integral number of
old-period turns. -/
theorem squareAnchorPhaseRepresentative_add_mul_period
    {S : Finset ℕ} (_hS : IsFinitePrimeBasis S) (n k : ℕ) :
    squareAnchorPhaseRepresentative S
        (n + k * finitePrimeBasisProduct S) =
      squareAnchorPhaseRepresentative S n := by
  simp [squareAnchorPhaseRepresentative, primeBasisWheelProjection]

/-- The block quotient records the number of old-period turns. -/
theorem squareAnchorPhaseBlockQuotient_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S) (n k : ℕ) :
    squareAnchorPhaseBlockQuotient S
        (n + k * finitePrimeBasisProduct S) =
      squareAnchorPhaseBlockQuotient S n + k := by
  have hMpos : 0 < finitePrimeBasisProduct S :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
  simpa [squareAnchorPhaseBlockQuotient] using
    (Nat.add_mul_div_right n k hMpos)

/-- The deleted center is invariant under any integral number of old-period
turns. -/
theorem squareAnchorFreshPrimeCenter_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (_hq : Nat.Prime q) (_hqS : q ∉ S) (n k : ℕ) :
    squareAnchorFreshPrimeCenter S q (n + k * finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeCenter S q n := by
  rw [squareAnchorFreshPrimeCenter, squareAnchorFreshPrimeCenter,
    squareAnchorPhaseRepresentative_add_mul_period hS]

/-- The radius gains `k` fresh-prime units over `k` old-period turns. -/
theorem squareAnchorFreshPrimeRadius_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n k : ℕ) :
    squareAnchorFreshPrimeRadius S q (n + k * finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeRadius S q n + (k : ZMod q) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hM : (finitePrimeBasisProduct S : ZMod q) ≠ 0 :=
    finitePrimeBasisProduct_cast_ne_zero_of_freshPrime hS hq hqS
  have hMi : (finitePrimeBasisProduct S : ZMod q) *
      (finitePrimeBasisProduct S : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hM
  unfold squareAnchorFreshPrimeRadius freshPrimePhaseRadius
  calc
    ((n + k * finitePrimeBasisProduct S : ℕ) : ZMod q) *
          (finitePrimeBasisProduct S : ZMod q)⁻¹ =
        ((n : ZMod q) + (k : ZMod q) *
          (finitePrimeBasisProduct S : ZMod q)) *
            (finitePrimeBasisProduct S : ZMod q)⁻¹ := by
              norm_num [Nat.cast_add, Nat.cast_mul]
    _ = (n : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹ +
        (k : ZMod q) := by
      rw [add_mul, mul_assoc, hMi, mul_one]

/-- The plus sheet gains `k` over `k` old-period turns. -/
theorem squareAnchorFreshPrimePlus_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n k : ℕ) :
    squareAnchorFreshPrimePlus S q (n + k * finitePrimeBasisProduct S) =
      squareAnchorFreshPrimePlus S q n + (k : ZMod q) := by
  rw [squareAnchorFreshPrimePlus, squareAnchorFreshPrimePlus,
    squareAnchorFreshPrimeCenter_add_mul_period hS hq hqS,
    squareAnchorFreshPrimeRadius_add_mul_period hS hq hqS]
  ring

/-- The minus sheet loses `k` over `k` old-period turns. -/
theorem squareAnchorFreshPrimeMinus_add_mul_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n k : ℕ) :
    squareAnchorFreshPrimeMinus S q (n + k * finitePrimeBasisProduct S) =
      squareAnchorFreshPrimeMinus S q n - (k : ZMod q) := by
  rw [squareAnchorFreshPrimeMinus, squareAnchorFreshPrimeMinus,
    squareAnchorFreshPrimeCenter_add_mul_period hS hq hqS,
    squareAnchorFreshPrimeRadius_add_mul_period hS hq hqS]
  ring

/-- The enlarged fresh-prime basis period is the old period repeated `q`
times. -/
theorem squareAnchorPhaseEnlargedPeriod_eq_q_mul_oldPeriod
    {S : Finset ℕ} {q : ℕ} (hqS : q ∉ S) :
    finitePrimeBasisProduct (insert q S) =
      q * finitePrimeBasisProduct S :=
  finitePrimeBasisProduct_insert hqS

/-- The deleted center closes at the fresh-prime enlarged period. -/
theorem squareAnchorFreshPrimeCenter_add_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeCenter S q
        (n + finitePrimeBasisProduct (insert q S)) =
      squareAnchorFreshPrimeCenter S q n := by
  rw [finitePrimeBasisProduct_insert hqS]
  exact squareAnchorFreshPrimeCenter_add_mul_period hS hq hqS n q

/-- The radius closes at the fresh-prime enlarged period. -/
theorem squareAnchorFreshPrimeRadius_add_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeRadius S q
        (n + finitePrimeBasisProduct (insert q S)) =
      squareAnchorFreshPrimeRadius S q n := by
  rw [finitePrimeBasisProduct_insert hqS]
  simpa using squareAnchorFreshPrimeRadius_add_mul_period hS hq hqS n q

/-- The plus sheet closes at the fresh-prime enlarged period. -/
theorem squareAnchorFreshPrimePlus_add_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimePlus S q
        (n + finitePrimeBasisProduct (insert q S)) =
      squareAnchorFreshPrimePlus S q n := by
  rw [finitePrimeBasisProduct_insert hqS]
  simpa using squareAnchorFreshPrimePlus_add_mul_period hS hq hqS n q

/-- The minus sheet closes at the fresh-prime enlarged period. -/
theorem squareAnchorFreshPrimeMinus_add_enlarged_period
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) (n : ℕ) :
    squareAnchorFreshPrimeMinus S q
        (n + finitePrimeBasisProduct (insert q S)) =
      squareAnchorFreshPrimeMinus S q n := by
  rw [finitePrimeBasisProduct_insert hqS]
  simpa using squareAnchorFreshPrimeMinus_add_mul_period hS hq hqS n q

/-- The `{2, 3}` old period and fresh prime `5` display the block quotient
sequence and the `(+1, -1)` monodromy, including closure after five turns. -/
theorem squareAnchorPhasePeriodTransport_two_three_four_regression :
    squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 = (0 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 10 = (1 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 16 = (2 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 34 = (0 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 (4 + 6) -
          squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 = (1 : ZMod 5) ∧
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 (4 + 6) -
          squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 4 = (-1 : ZMod 5) ∧
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 (4 + 30) =
        squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 ∧
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 (4 + 30) =
        squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 4 := by
  have hS : IsFinitePrimeBasis ({2, 3} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  have hq : Nat.Prime 5 := by norm_num
  have hqS : 5 ∉ ({2, 3} : Finset ℕ) := by simp
  have hfive : (5 : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff 5 5).mpr (dvd_refl 5)
  have hp4 := squareAnchorFreshPrimePlus_eq_blockQuotient hS hq hqS 4
  have hp4' : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 =
      (0 : ZMod 5) := by
    simpa [squareAnchorPhaseBlockQuotient, finitePrimeBasisProduct] using hp4
  have hp10transport := squareAnchorFreshPrimePlus_add_period hS hq hqS 4
  have hp10 : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 10 =
      (1 : ZMod 5) := by
    norm_num [finitePrimeBasisProduct] at hp10transport
    simpa [hp4'] using hp10transport
  have hp16transport := squareAnchorFreshPrimePlus_add_mul_period
    hS hq hqS 4 2
  have hp16 : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 16 =
      (2 : ZMod 5) := by
    norm_num [finitePrimeBasisProduct] at hp16transport
    simpa [hp4'] using hp16transport
  have hp34transport := squareAnchorFreshPrimePlus_add_mul_period
    hS hq hqS 4 5
  have hp34 : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 34 =
      (0 : ZMod 5) := by
    norm_num [finitePrimeBasisProduct] at hp34transport
    rw [hfive] at hp34transport
    simpa [hp4'] using hp34transport
  have hm10transport := squareAnchorFreshPrimeMinus_add_period hS hq hqS 4
  have hp6diff : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 (4 + 6) -
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 = (1 : ZMod 5) := by
    norm_num [finitePrimeBasisProduct] at hp10transport
    rw [hp10transport]
    ring
  have hm6diff : squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 (4 + 6) -
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 4 = (-1 : ZMod 5) := by
    norm_num [finitePrimeBasisProduct] at hm10transport
    rw [hm10transport]
    ring
  have hp30close := squareAnchorFreshPrimePlus_add_mul_period hS hq hqS 4 5
  have hm30close := squareAnchorFreshPrimeMinus_add_mul_period hS hq hqS 4 5
  have hp30 : squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 (4 + 30) =
      squareAnchorFreshPrimePlus ({2, 3} : Finset ℕ) 5 4 := by
    norm_num [finitePrimeBasisProduct] at hp30close
    rw [hfive] at hp30close
    simpa using hp30close
  have hm30 : squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 (4 + 30) =
      squareAnchorFreshPrimeMinus ({2, 3} : Finset ℕ) 5 4 := by
    norm_num [finitePrimeBasisProduct] at hm30close
    rw [hfive] at hm30close
    simpa using hm30close
  exact ⟨hp4', hp10, hp16, hp34, hp6diff, hm6diff, hp30, hm30⟩

end DkMath.NumberTheory.PrimorialUniverse
