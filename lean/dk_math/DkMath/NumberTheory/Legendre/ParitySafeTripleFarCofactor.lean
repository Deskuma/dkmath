/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate

#print "file: DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor"

/-!
## ParitySafeTripleFarCofactor

This module extracts the complementary cofactor of an L042 far triple.  The
large triple product compresses the cofactor into the half-scale interval
`2 * t < n + 2`; reduced-residue inheritance then returns every prime divisor
of `t` to the same parity-safe active old-prime world.  A nontrivial cofactor
therefore yields either repeated depth in one of the three existing directions
or a fourth distinct active direction.

The result is a finite cofactor/compression bridge.  It is not a smaller-anchor
full-cover reconstruction, an injective cofactor parametrization, or a proof of
Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal

/-! ### PRIM-L043.1--4: far cofactor packet and old-support return -/

/-- The complementary factor of a far canonical triple product. -/
noncomputable def paritySafeFarTripleCofactor (n r q s : ℕ) : ℕ :=
  (n ^ 2 + r) /
    (paritySafeCanonicalSupportPrime n r * q * s)

@[simp] theorem paritySafeFarTripleCofactor_eq_div
    (n r q s : ℕ) :
    paritySafeFarTripleCofactor n r q s =
      (n ^ 2 + r) /
        (paritySafeCanonicalSupportPrime n r * q * s) := rfl

/--
The far cofactor packet: positivity, exact factorization, half-scale
compression, strict anchor-smallness, and reduced-residue inheritance.
-/
theorem paritySafeFarTripleCofactor_packet
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    0 < paritySafeFarTripleCofactor n r q s ∧
      paritySafeCanonicalSupportPrime n r * q * s *
          paritySafeFarTripleCofactor n r q s = n ^ 2 + r ∧
      2 * paritySafeFarTripleCofactor n r q s < n + 2 ∧
      paritySafeFarTripleCofactor n r q s < n ∧
      Nat.Coprime (2 * n) (paritySafeFarTripleCofactor n r q s) := by
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨hr, hp, hq, hs, hpq, hps, hqs, hdiv, hcopm⟩
  have hfar' := (Finset.mem_filter.mp hfar).2
  have hlarge : 2 * n <
      paritySafeCanonicalSupportPrime n r * q * s := by
    simpa [paritySafeTripleProductModulus] using hfar'
  have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr
  have hnpos : 0 < n := by
    dsimp [SquareOffset] at hoff
    omega
  have hNpos : 0 < n ^ 2 + r := by
    dsimp [SquareOffset] at hoff
    omega
  have hNle : n ^ 2 + r ≤ n * (n + 2) := by
    dsimp [SquareOffset] at hoff
    nlinarith
  have hfactor : paritySafeCanonicalSupportPrime n r * q * s *
      paritySafeFarTripleCofactor n r q s = n ^ 2 + r := by
    unfold paritySafeFarTripleCofactor
    exact Nat.mul_div_cancel' hdiv
  have htpos : 0 < paritySafeFarTripleCofactor n r q s := by
    by_contra ht
    have htzero : paritySafeFarTripleCofactor n r q s = 0 :=
      Nat.eq_zero_of_not_pos ht
    rw [htzero] at hfactor
    omega
  have hscaled :
      (2 * n) * paritySafeFarTripleCofactor n r q s <
        n * (n + 2) := by
    calc
      (2 * n) * paritySafeFarTripleCofactor n r q s <
          (paritySafeCanonicalSupportPrime n r * q * s) *
            paritySafeFarTripleCofactor n r q s :=
        Nat.mul_lt_mul_of_pos_right hlarge htpos
      _ = n ^ 2 + r := hfactor
      _ ≤ n * (n + 2) := hNle
  have hhalf : 2 * paritySafeFarTripleCofactor n r q s < n + 2 := by
    nlinarith
  have hqge3 : 3 ≤ q := by
    have hq' := mem_squareAnchorOddActivePrimes.mp hq
    have hq2 : 2 ≤ q := hq'.1.two_le
    omega
  have hnlarge : 3 ≤ n :=
    le_trans hqge3 (mem_squareAnchorOddActivePrimes.mp hq).2.1
  have hsmall : paritySafeFarTripleCofactor n r q s < n := by
    omega
  have hcopN : Nat.Coprime (2 * n) (n ^ 2 + r) :=
    (mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hr).2
  have htdiv : paritySafeFarTripleCofactor n r q s ∣ n ^ 2 + r := by
    refine ⟨paritySafeCanonicalSupportPrime n r * q * s, ?_⟩
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfactor.symm
  have htCoprime : Nat.Coprime (2 * n)
      (paritySafeFarTripleCofactor n r q s) :=
    Nat.Coprime.coprime_dvd_right htdiv hcopN
  exact ⟨htpos, hfactor, hhalf, hsmall, htCoprime⟩

/--
Every prime divisor of a far cofactor returns to the active old-prime world
and to the candidate's parity-safe active support.
-/
theorem paritySafeFarTripleCofactor_prime_divisor_return
    {n r q s u : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (huprime : Nat.Prime u)
    (hut : u ∣ paritySafeFarTripleCofactor n r q s) :
    u ∈ squareAnchorOddActivePrimes n ∧
      u ∈ paritySafeActiveSupport n r := by
  have hpacket := paritySafeFarTripleCofactor_packet hinc hfar
  rcases hpacket with ⟨htpos, hfactor, hhalf, hsmall, hcop⟩
  have hutle : u ≤ paritySafeFarTripleCofactor n r q s :=
    Nat.le_of_dvd htpos hut
  have hunle : u ≤ n := hutle.trans hsmall.le
  have hcopu : Nat.Coprime u (2 * n) :=
    (Nat.Coprime.coprime_dvd_right hut hcop).symm
  have hnot2n : ¬ u ∣ 2 * n :=
    (Nat.Prime.coprime_iff_not_dvd huprime).mp hcopu
  have hun : ¬ u ∣ n := by
    intro hud
    apply hnot2n
    exact dvd_mul_of_dvd_right hud 2
  have hu2 : u ≠ 2 := by
    intro hu
    subst u
    apply hnot2n
    exact dvd_mul_right 2 n
  have huN : u ∣ n ^ 2 + r := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_right hut _
  have hactive : u ∈ squareAnchorOddActivePrimes n :=
    mem_squareAnchorOddActivePrimes.mpr ⟨huprime, hunle, hun, hu2⟩
  have hcandidate :=
    (paritySafeCanonicalResidualTripleIncidence_packet hinc).1
  have hsupport :=
    squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
      hcandidate
  have husupport : u ∈ squareOffsetAnchorNondivisorSupport n r :=
    mem_squareOffsetAnchorNondivisorSupport.mpr ⟨huprime, hunle, hun, huN⟩
  exact ⟨hactive, by rw [← hsupport]; exact husupport⟩

/-! ### PRIM-L043.5: terminal / nontrivial cofactor split -/

/-- A far cofactor is exactly one or strictly larger than one. -/
theorem paritySafeFarTripleCofactor_one_or_nontrivial
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeFarTripleCofactor n r q s = 1 ∨
      1 < paritySafeFarTripleCofactor n r q s := by
  have htpos := (paritySafeFarTripleCofactor_packet hinc hfar).1
  omega

/-- If the far cofactor is one, the triple product is the complete point. -/
theorem paritySafeFarTripleCofactor_eq_one_factorization
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (ht : paritySafeFarTripleCofactor n r q s = 1) :
    paritySafeCanonicalSupportPrime n r * q * s = n ^ 2 + r := by
  have hfactor := (paritySafeFarTripleCofactor_packet hinc hfar).2.1
  calc
    paritySafeCanonicalSupportPrime n r * q * s =
        paritySafeCanonicalSupportPrime n r * q * s *
          paritySafeFarTripleCofactor n r q s := by rw [ht]; simp
    _ = n ^ 2 + r := hfactor

/-! ### PRIM-L043.6: depth or a new active direction -/

/--
A nontrivial far cofactor returns either a square depth in `p`, `q`, or `s`,
or a fourth distinct active direction whose product divides the complete point.
-/
theorem paritySafeFarTripleCofactor_depth_or_new_direction
    {n r p q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateFarTriples n)
    (hp : p = paritySafeCanonicalSupportPrime n r)
    (ht : 1 < paritySafeFarTripleCofactor n r q s) :
    p ^ 2 ∣ n ^ 2 + r ∨
      q ^ 2 ∣ n ^ 2 + r ∨
      s ^ 2 ∣ n ^ 2 + r ∨
      ∃ u, Nat.Prime u ∧
        u ∣ paritySafeFarTripleCofactor n r q s ∧
        u ∈ squareAnchorOddActivePrimes n ∧
        u ∈ paritySafeActiveSupport n r ∧
        u ≠ p ∧ u ≠ q ∧ u ≠ s ∧
        p * q * s * u ∣ n ^ 2 + r := by
  subst p
  obtain ⟨u, huprime, hut⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt ht)
  have hreturn :=
    paritySafeFarTripleCofactor_prime_divisor_return hinc hfar huprime hut
  rcases hreturn with ⟨huactive, husupport⟩
  by_cases hup : u = paritySafeCanonicalSupportPrime n r
  · left
    subst u
    have hpdiv : paritySafeCanonicalSupportPrime n r ∣
        paritySafeCanonicalSupportPrime n r * q * s := by
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hdvd := Nat.mul_dvd_mul hpdiv hut
    rw [(paritySafeFarTripleCofactor_packet hinc hfar).2.1] at hdvd
    simpa [pow_two] using hdvd
  · by_cases huq : u = q
    · right; left
      subst u
      have hqdiv : q ∣ paritySafeCanonicalSupportPrime n r * q * s := by
        have hqp : q ∣ paritySafeCanonicalSupportPrime n r * q :=
          dvd_mul_of_dvd_right (dvd_refl q) _
        exact dvd_mul_of_dvd_left hqp _
      have hdvd := Nat.mul_dvd_mul hqdiv hut
      rw [(paritySafeFarTripleCofactor_packet hinc hfar).2.1] at hdvd
      simpa [pow_two] using hdvd
    · by_cases hus : u = s
      · right; right; left
        subst u
        have hsdiv : s ∣ paritySafeCanonicalSupportPrime n r * q * s := by
          exact dvd_mul_of_dvd_right (dvd_refl s) _
        have hdvd := Nat.mul_dvd_mul hsdiv hut
        rw [(paritySafeFarTripleCofactor_packet hinc hfar).2.1] at hdvd
        simpa [pow_two] using hdvd
      · right; right; right
        refine ⟨u, huprime, hut, huactive, husupport, hup, huq, hus, ?_⟩
        have hdvd := Nat.mul_dvd_mul (dvd_refl
          (paritySafeCanonicalSupportPrime n r * q * s)) hut
        rw [(paritySafeFarTripleCofactor_packet hinc hfar).2.1] at hdvd
        exact hdvd

/-! ### PRIM-L043.7: supplied arithmetic false beam -/

/--
The two supplied complete-point factorizations have the same cofactor `1` and
both products are beyond the half-window.  This is the arithmetic obstruction
to treating the cofactor as an injective residual coordinate; residual-set
membership is intentionally not duplicated here.
-/
theorem paritySafeFarTripleCofactor_false_beam_arithmetic :
    25 ^ 2 + 2 = 3 * 11 * 19 ∧
      25 ^ 2 + 38 = 3 * 13 * 17 ∧
      50 < 3 * 11 * 19 ∧
      50 < 3 * 13 * 17 ∧
      (25 ^ 2 + 2) / (3 * 11 * 19) = 1 ∧
      (25 ^ 2 + 38) / (3 * 13 * 17) = 1 := by
  norm_num

end DkMath.NumberTheory.Legendre
