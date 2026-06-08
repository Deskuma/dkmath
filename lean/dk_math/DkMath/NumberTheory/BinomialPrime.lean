/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Choose.Dvd

#print "file: DkMath.NumberTheory.BinomialPrime"

namespace DkMath
namespace NumberTheory

/-!
## Prime rows in Pascal's triangle

This file records the first stable divisibility layer for the binomial roadmap:
if `p` is prime, then every inner coefficient in row `p` is divisible by `p`.

The converse direction is intentionally left to a later file/checkpoint, where
we can decide whether to use a mathlib theorem or prove the composite witness
directly.
-/

/-- All inner binomial coefficients in row `d` are divisible by `m`. -/
def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k

/--
A prime support channel visible across every inner coefficient of row `d`.

This is the observational form: the row is produced by Pascal addition, but the
inner row carries the multiplicative support prime `p`.
-/
def InnerRowSupportPrime (d p : ℕ) : Prop :=
  p.Prime ∧ AllInnerChooseDivisible d p

/--
A support prime born from the row index itself.

This deliberately does not assert that `d` is prime. Prime powers can also make
their base prime appear across all inner coefficients, so the reverse direction
is kept out of this first observation layer.
-/
def RowBirthPrime (d p : ℕ) : Prop :=
  InnerRowSupportPrime d p ∧ p ∣ d

/--
Prime rows carry their prime modulus through every inner binomial coefficient.
-/
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  intro k hk0 hkp
  exact hp.dvd_choose_self hk0.ne' hkp

/--
Alias phrased as a row theorem. This is the API shape used by the weighted
binomial layer.
-/
theorem prime_dvd_inner_choose
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k :=
  prime_allInnerChooseDivisible_self hp k hk0 hkp

/--
Unpack `AllInnerChooseDivisible` at a concrete inner index.
-/
theorem allInnerChooseDivisible_dvd_choose
    {d m k : ℕ}
    (h : AllInnerChooseDivisible d m) (hk0 : 0 < k) (hkd : k < d) :
    m ∣ Nat.choose d k :=
  h k hk0 hkd

/--
Unpack an inner support prime at a concrete index.
-/
theorem innerRowSupportPrime_dvd_choose
    {d p k : ℕ}
    (h : InnerRowSupportPrime d p) (hk0 : 0 < k) (hkd : k < d) :
    p ∣ Nat.choose d k :=
  h.2 k hk0 hkd

/-- The support prime stored by `InnerRowSupportPrime` is prime. -/
theorem innerRowSupportPrime_prime
    {d p : ℕ} (h : InnerRowSupportPrime d p) :
    p.Prime :=
  h.1

/--
A prime row carries its own row prime through all inner coefficients.
-/
theorem prime_innerRowSupportPrime_self
    {p : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime p p :=
  ⟨hp, prime_allInnerChooseDivisible_self hp⟩

/--
A prime row births its own support prime from the row index.
-/
theorem prime_rowBirthPrime_self
    {p : ℕ} (hp : p.Prime) :
    RowBirthPrime p p :=
  ⟨prime_innerRowSupportPrime_self hp, dvd_rfl⟩

/--
Unpack `RowBirthPrime` to the inner support-prime observation.
-/
theorem rowBirthPrime_innerRowSupportPrime
    {d p : ℕ} (h : RowBirthPrime d p) :
    InnerRowSupportPrime d p :=
  h.1

/-- The support prime stored by `RowBirthPrime` is prime. -/
theorem rowBirthPrime_prime
    {d p : ℕ} (h : RowBirthPrime d p) :
    p.Prime :=
  h.1.1

/-- The support prime stored by `RowBirthPrime` divides the row index. -/
theorem rowBirthPrime_dvd_row
    {d p : ℕ} (h : RowBirthPrime d p) :
    p ∣ d :=
  h.2

/--
Unpack a row-birth support prime at a concrete inner index.
-/
theorem rowBirthPrime_dvd_choose
    {d p k : ℕ}
    (h : RowBirthPrime d p) (hk0 : 0 < k) (hkd : k < d) :
    p ∣ Nat.choose d k :=
  innerRowSupportPrime_dvd_choose h.1 hk0 hkd

-- examples

section samples

example {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k := by
  exact prime_dvd_inner_choose hp hk0 hkp

example {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  exact prime_allInnerChooseDivisible_self hp

end samples

end NumberTheory
end DkMath
