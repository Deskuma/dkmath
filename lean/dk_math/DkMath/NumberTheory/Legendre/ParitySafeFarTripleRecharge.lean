/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge"

/-!
## ParitySafeFarTripleRecharge

PRIM-L044 sharpens the L043 far-triple cofactor packet.  The complementary
cofactor is returned to the first-half coprime packet at the same anchor, and
each prime divisor is returned to a half-scale active-prime set as well as to
the candidate support.  The nontrivial-cofactor disjunction is then translated
to the existing PRIM-L018 prime-square incidence or kept as an explicit fourth
direction.

This is a finite recharge and provenance statement.  It does not make the
cofactor or its prime divisor an injective residual coordinate, does not give
`SquareOffsetsFullyCovered` at a smaller anchor, and does not prove a global
cardinality contradiction or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal

/-! ### PRIM-L044.1: half-scale active-prime world -/

/-- The half-scale active-prime world at the original anchor.

The filter is deliberately same-anchor finite data; its definition does not
turn a cofactor into a new square anchor.
-/
noncomputable def paritySafeHalfScaleActivePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter (fun u => 2 * u < n + 2)

/-- The membership characterization of the half-scale active world. -/
@[simp] theorem mem_paritySafeHalfScaleActivePrimes
    {n u : ℕ} :
    u ∈ paritySafeHalfScaleActivePrimes n ↔
      u ∈ squareAnchorOddActivePrimes n ∧ 2 * u < n + 2 := by
  simp [paritySafeHalfScaleActivePrimes]

/-! ### PRIM-L044.2: same-anchor coprime-base return -/

/-- The far cofactor is a first-half coprime packet coordinate at anchor `n`.

The conclusion is a membership statement at the original anchor.  It is not
an assertion that the cofactor itself is a new anchor for a descent.
-/
theorem paritySafeFarTripleCofactor_mem_coprimeBase
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactor n r q s ∈
      squareAnchorCoprimeBaseOffsets n := by
  have hpacket := paritySafeFarTripleCofactor_packet hinc hfar
  rcases hpacket with ⟨htpos, _, _, htsmall, htcop⟩
  apply mem_squareAnchorCoprimeBaseOffsets.mpr
  exact ⟨by omega, htsmall.le,
    (coprime_two_mul_iff_coprime_and_odd.mp htcop).1⟩

/-! ### PRIM-L044.3: prime divisors return at half scale -/

/-- A prime divisor of the far cofactor returns to the same support and
half-scale active-prime world. -/
theorem paritySafeFarTripleCofactor_prime_divisor_halfScale_return
    {n r q s u : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (huprime : Nat.Prime u)
    (hut : u ∣ paritySafeFarTripleCofactor n r q s) :
    u ∈ paritySafeHalfScaleActivePrimes n ∧
      u ∈ paritySafeActiveSupport n r := by
  have hpacket := paritySafeFarTripleCofactor_packet hinc hfar
  rcases hpacket with ⟨htpos, _, hthalf, htsmall, _⟩
  have hreturn :=
    paritySafeFarTripleCofactor_prime_divisor_return hinc hfar huprime hut
  have hutle : u ≤ paritySafeFarTripleCofactor n r q s :=
    Nat.le_of_dvd htpos hut
  have huhalf : 2 * u < n + 2 := by omega
  exact ⟨mem_paritySafeHalfScaleActivePrimes.mpr ⟨hreturn.1, huhalf⟩,
    hreturn.2⟩

/-! ### PRIM-L044.4: recharge to the L018 depth ledger -/

/-- The L043 depth/new-direction split, with its first three branches placed
back into the actual L018 coprime prime-square incidences.

The fourth branch remains a witness rather than a global charge: no
injectivity from residual incidences to cofactors or returned primes is
claimed here.
-/
theorem paritySafeFarTripleCofactor_depthLedger_or_halfScaleNewDirection
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (ht : 1 < paritySafeFarTripleCofactor n r q s) :
    r ∈ squareAnchorCoprimePrimeSquareOffsets n p ∨
      r ∈ squareAnchorCoprimePrimeSquareOffsets n q ∨
      r ∈ squareAnchorCoprimePrimeSquareOffsets n s ∨
      ∃ u, Nat.Prime u ∧
        u ∣ paritySafeFarTripleCofactor n r q s ∧
        u ∈ paritySafeHalfScaleActivePrimes n ∧
        u ∈ paritySafeActiveSupport n r ∧
        u ≠ p ∧ u ≠ q ∧ u ≠ s ∧
        p * q * s * u ∣ n ^ 2 + r := by
  subst p
  have hr : r ∈ squareAnchorCoprimeOffsets n :=
    (mem_squareAnchorOddPointCoprimeOffsets.mp
      (paritySafeCanonicalResidualTripleIncidence_packet hinc).1).1
  have hsplit := paritySafeFarTripleCofactor_depth_or_new_direction
    hinc hfar rfl ht
  rcases hsplit with hpdiv | hqdiv | hsdiv | hnew
  · exact Or.inl (mem_squareAnchorCoprimePrimeSquareOffsets.mpr ⟨hr, hpdiv⟩)
  · exact Or.inr (Or.inl
      (mem_squareAnchorCoprimePrimeSquareOffsets.mpr ⟨hr, hqdiv⟩))
  · exact Or.inr (Or.inr (Or.inl
      (mem_squareAnchorCoprimePrimeSquareOffsets.mpr ⟨hr, hsdiv⟩)))
  · rcases hnew with ⟨u, huprime, hut, huactive, husupport, hup, huq, hus,
      hproduct⟩
    have hhalf :=
      paritySafeFarTripleCofactor_prime_divisor_halfScale_return
        hinc hfar huprime hut
    exact Or.inr (Or.inr (Or.inr
      ⟨u, huprime, hut, hhalf.1, husupport, hup, huq, hus, hproduct⟩))

/-! ### PRIM-L044.6: noninjective recharge witness -/

/-- Two far factorizations can have the same cofactor and returned
half-scale prime.  This arithmetic beam blocks a global injective recharge
interpretation; it intentionally does not expand residual-set membership. -/
theorem paritySafeHalfScaleReturn_false_beam_arithmetic :
    62 ^ 2 + 41 = 3 * 5 * 37 * 7 ∧
      62 ^ 2 + 83 = 3 * 11 * 17 * 7 ∧
      2 * 62 < 3 * 5 * 37 ∧
      2 * 62 < 3 * 11 * 17 ∧
      (62 ^ 2 + 41) / (3 * 5 * 37) = 7 ∧
      (62 ^ 2 + 83) / (3 * 11 * 17) = 7 ∧
      2 * 7 < 62 + 2 := by
  norm_num

end DkMath.NumberTheory.Legendre
