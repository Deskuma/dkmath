/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

#print "file: DkMath.NumberGeometry.Phase.TwoPrime"

/-!
# General signed `2 * p` phases

This module isolates the algebraic phase packet used by the later
fourteen-phase calibration. It has no dependency on NumberGeometry gauges,
prime-scale dynamics, cyclotomic FLT files, or a particular coordinate model.
-/

namespace DkMath.NumberGeometry.Phase

/-!
The half-turn identity is available from Mathlib once the ambient ring has no
zero divisors and `p` is positive: `IsPrimitiveRoot.pow` gives a primitive
second root and `IsPrimitiveRoot.eq_neg_one_of_two_right` identifies it with
`-1`. The packet below keeps positivity explicit so all phase identities can
remain direct and reusable.
-/

/-- A positive primitive `2 * p` phase in a commutative domain-like ring. -/
structure TwoPrimePhase (R : Type*) [CommRing R] [NoZeroDivisors R] (p : ℕ) where
  /-- The phase generator. -/
  eta : R
  /-- The phase index is positive. -/
  positive : 0 < p
  /-- The generator has exact multiplicative order `2 * p`. -/
  primitive : IsPrimitiveRoot eta (2 * p)

namespace TwoPrimePhase

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {p : ℕ}

/-- The `p`-th power of a primitive `2 * p` phase is the half-turn `-1`. -/
theorem halfTurn (P : TwoPrimePhase R p) : P.eta ^ p = -1 := by
  have hhalf : IsPrimitiveRoot (P.eta ^ p) 2 := by
    exact P.primitive.pow (Nat.mul_pos (by decide) P.positive) (by ring)
  exact hhalf.eq_neg_one_of_two_right

/-- A primitive `2 * p` phase completes its full turn after `2 * p` powers. -/
theorem fullTurn (P : TwoPrimePhase R p) : P.eta ^ (2 * p) = 1 :=
  P.primitive.pow_eq_one

/-- The even phase indexed by a natural number. -/
def evenPhase (P : TwoPrimePhase R p) (j : ℕ) : R :=
  P.eta ^ (2 * j)

/-- The odd phase indexed by a natural number. -/
def oddPhase (P : TwoPrimePhase R p) (j : ℕ) : R :=
  P.eta ^ (2 * j + 1)

/-- The even exponent is a multiple of the full `2 * p` turn. -/
private theorem evenExponent_fullTurn (P : TwoPrimePhase R p) (j : ℕ) :
    P.eta ^ (2 * j * p) = 1 := by
  calc
    P.eta ^ (2 * j * p) = P.eta ^ ((2 * p) * j) := by
      congr 1; ring
    _ = (P.eta ^ (2 * p)) ^ j := by rw [pow_mul]
    _ = 1 := by rw [P.fullTurn, one_pow]

/-- Every even phase has `p`-th power `1`. -/
theorem evenPhase_pow (P : TwoPrimePhase R p) (j : ℕ) :
    (P.evenPhase j) ^ p = 1 := by
  rw [evenPhase, ← pow_mul]
  exact evenExponent_fullTurn P j

/-- Every odd phase has `p`-th power `-1`. -/
theorem oddPhase_pow (P : TwoPrimePhase R p) (j : ℕ) :
    (P.oddPhase j) ^ p = -1 := by
  rw [oddPhase, ← pow_mul]
  calc
    P.eta ^ ((2 * j + 1) * p) =
        P.eta ^ (2 * j * p) * P.eta ^ p := by
      rw [← pow_add]
      congr 1; ring
    _ = 1 * (-1) := by rw [evenExponent_fullTurn P j, P.halfTurn]
    _ = -1 := one_mul _

/-- The primitive `p`-phase generator obtained by squaring the `2 * p` phase. -/
def zeta (P : TwoPrimePhase R p) : R :=
  P.eta ^ 2

/-- The squared generator has trivial `p`-th power. -/
theorem zeta_pow_p (P : TwoPrimePhase R p) : P.zeta ^ p = 1 := by
  rw [zeta, ← pow_mul]
  exact P.fullTurn

/-- Even phases are powers of the squared generator. -/
theorem evenPhase_eq_zeta_pow (P : TwoPrimePhase R p) (j : ℕ) :
    P.evenPhase j = P.zeta ^ j := by
  simp [evenPhase, zeta, pow_mul]

/-- Odd phases are the original generator times a squared-generator power. -/
theorem oddPhase_eq_eta_mul_zeta_pow (P : TwoPrimePhase R p) (j : ℕ) :
    P.oddPhase j = P.eta * P.zeta ^ j := by
  calc
    P.oddPhase j = P.eta ^ 1 * P.eta ^ (2 * j) := by
      rw [oddPhase, ← pow_add]
      congr 1; ring
    _ = P.eta * P.zeta ^ j := by
      simp [zeta, pow_mul]

/-- The squared generator is primitive of order `p`. -/
theorem zeta_isPrimitiveRoot (P : TwoPrimePhase R p) (hp : Nat.Prime p) :
    IsPrimitiveRoot P.zeta p := by
  have hpos : 0 < p := hp.pos
  exact P.primitive.pow (Nat.mul_pos (by decide) hpos) (by ring)

/-- The even phase restricted to the finite index set `Fin p`. -/
def evenPhaseFin (P : TwoPrimePhase R p) (j : Fin p) : R :=
  P.evenPhase j.val

/-- The odd phase restricted to the finite index set `Fin p`. -/
def oddPhaseFin (P : TwoPrimePhase R p) (j : Fin p) : R :=
  P.oddPhase j.val

/-- The finite even sector has no repetitions. -/
theorem evenPhaseFin_injective (P : TwoPrimePhase R p) :
    Function.Injective P.evenPhaseFin := by
  intro i j hij
  apply Fin.ext
  have hval : 2 * i.val = 2 * j.val := by
    apply P.primitive.pow_inj (i := 2 * i.val) (j := 2 * j.val)
    · omega
    · omega
    · simpa [evenPhaseFin, evenPhase] using hij
  omega

/-- The finite odd sector has no repetitions. -/
theorem oddPhaseFin_injective (P : TwoPrimePhase R p) :
    Function.Injective P.oddPhaseFin := by
  intro i j hij
  apply Fin.ext
  have hval : 2 * i.val + 1 = 2 * j.val + 1 := by
    apply P.primitive.pow_inj (i := 2 * i.val + 1) (j := 2 * j.val + 1)
    · omega
    · omega
    · simpa [oddPhaseFin, oddPhase] using hij
  omega

/-- An even finite phase cannot equal an odd finite phase. -/
theorem evenPhaseFin_ne_oddPhaseFin (P : TwoPrimePhase R p)
    (i j : Fin p) : P.evenPhaseFin i ≠ P.oddPhaseFin j := by
  intro hij
  have hpow : P.eta ^ (2 * i.val) = P.eta ^ (2 * j.val + 1) := by
    simpa [evenPhaseFin, oddPhaseFin, evenPhase, oddPhase] using hij
  have hexponent : 2 * i.val = 2 * j.val + 1 := by
    apply P.primitive.pow_inj
    · omega
    · omega
    · exact hpow
  omega

/-- An even phase multiple satisfies the difference equation `X^p - Y^p = 0`. -/
theorem even_signed_equation (P : TwoPrimePhase R p) (j : ℕ) (Y : R) :
    (P.evenPhase j * Y) ^ p - Y ^ p = 0 := by
  rw [mul_pow, P.evenPhase_pow]
  ring

/-- An odd phase multiple satisfies the sum equation `X^p + Y^p = 0`. -/
theorem odd_signed_equation (P : TwoPrimePhase R p) (j : ℕ) (Y : R) :
    (P.oddPhase j * Y) ^ p + Y ^ p = 0 := by
  rw [mul_pow, P.oddPhase_pow]
  ring

end TwoPrimePhase

/-! ## Canonical complex witness -/

noncomputable section

/-- The canonical complex phase `exp (2 * π * I / (2 * p))`. -/
def complexEta (p : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (2 * p))

/-- The canonical complex phase is primitive of order `2 * p`. -/
theorem complexEta_isPrimitiveRoot {p : ℕ} (hp : 0 < p) :
    IsPrimitiveRoot (complexEta p) (2 * p) := by
  simpa [complexEta] using Complex.isPrimitiveRoot_exp (2 * p) (by omega)

/-- The canonical complex phase packet. -/
def complexTwoPrimePhase (p : ℕ) (hp : 0 < p) : TwoPrimePhase ℂ p where
  eta := complexEta p
  positive := hp
  primitive := complexEta_isPrimitiveRoot hp

/-- The canonical complex phase has the required half-turn. -/
theorem complexEta_pow_eq_neg_one {p : ℕ} (hp : 0 < p) :
    complexEta p ^ p = -1 := by
  exact (complexTwoPrimePhase p hp).halfTurn

end

end DkMath.NumberGeometry.Phase
