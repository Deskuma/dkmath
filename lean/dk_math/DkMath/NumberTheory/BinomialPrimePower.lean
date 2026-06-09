/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.BinomialPrime
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.NumberTheory.BinomialPrimePower"

namespace DkMath
namespace NumberTheory

/-!
## Prime-power rows in Pascal's triangle

Prime rows are the first visible layer of binomial divisibility.  Prime-power
rows keep the same support prime across the whole inner row; the exponent of
that support is measured by the usual `padicValNat`/factorization layer.
-/

/--
A prime-power row whose base prime is visible across every inner binomial
coefficient.
-/
def PrimePowerRowSupport (p n : ℕ) : Prop :=
  p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p

/--
All inner coefficients in row `d` have exactly the same `p`-adic height `h`.

This is a stricter beam filter than mere divisibility: not only does `p`
divide every inner coefficient, the visible `p`-support has uniform height.
-/
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h

/--
All inner coefficients satisfying a filter predicate have the same `p`-adic
height.

This is the `p^n` sieve shape: the whole beam need not have uniform height, but
a selected layer of indices can.
-/
def FilteredBeamHeight (d p h : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ k, 0 < k → k < d → P k →
    padicValNat p (Nat.choose d k) = h

/--
A filtered beam-height observation gives a divisibility statement for any
requested layer below that height.

This is the basic bridge from the p-adic observation language back to ordinary
divisibility of binomial coefficients.
-/
theorem FilteredBeamHeight.dvd_choose_of_height_ge
    {d p h : ℕ} {P : ℕ → Prop}
    (hp : p.Prime) (H : FilteredBeamHeight d p h P)
    {k r : ℕ} (hk0 : 0 < k) (hkd : k < d) (hPk : P k)
    (hr : r ≤ h) :
    p ^ r ∣ Nat.choose d k := by
  have hchoose_ne : Nat.choose d k ≠ 0 := Nat.choose_ne_zero hkd.le
  have hv : padicValNat p (Nat.choose d k) = h := H k hk0 hkd hPk
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne r).mp (by omega)

/--
A uniform beam-height observation gives a divisibility statement for any
requested layer below that height.
-/
theorem UniformBeamHeight.dvd_choose_of_height_ge
    {d p h k r : ℕ} (hp : p.Prime) (H : UniformBeamHeight d p h)
    (hk0 : 0 < k) (hkd : k < d) (hr : r ≤ h) :
    p ^ r ∣ Nat.choose d k := by
  exact
    (FilteredBeamHeight.dvd_choose_of_height_ge
      (P := fun _ => True) hp (by intro j hj0 hjd _; exact H j hj0 hjd)
      hk0 hkd trivial hr)

/--
The beam-birth boundary for `p`.

Rows below `p` have no visible `p`-height, while row `p` has uniform height
`1`.  The prime theorem below proves that prime numbers satisfy this boundary.
-/
def BeamBirthBoundary (p : ℕ) : Prop :=
  (∀ d, d < p → UniformBeamHeight d p 0) ∧
    UniformBeamHeight p p 1

/--
A concrete obstruction to beam-birth behavior at row `p`.

This isolates the witness needed for the reverse direction: to refute a
boundary at a composite row, it suffices to find one inner coefficient whose
`p`-height is not `1`.
-/
def BeamBirthBoundaryObstruction (p : ℕ) : Prop :=
  ∃ k, 0 < k ∧ k < p ∧ padicValNat p (Nat.choose p k) ≠ 1

/--
The pre-birth alternation visible just before a prime row.

Row `p - 1` is not a divisibility beam for `p`; instead, when viewed modulo
`p`, its coefficients alternate as `1, -1, 1, -1, ...`.
-/
def PrimePrebirthAlternation (p : ℕ) : Prop :=
  ∀ k, k ≤ p - 1 →
    ((Nat.choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k)

/--
Every inner coefficient of row `p^n` is divisible by `p`.

This is the support-level `p^n` filter.  It deliberately records only the first
divisibility layer; exact exponents are handled by the `padicValNat` lemmas
below.
-/
theorem prime_power_allInnerChooseDivisible
    {p n : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible (p ^ n) p := by
  intro k hk0 hkp
  exact hp.dvd_choose_pow hk0.ne' (ne_of_lt hkp)

/--
Prime-power rows carry their base prime through every inner coefficient.
-/
theorem prime_power_innerRowSupportPrime
    {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  ⟨hp, prime_power_allInnerChooseDivisible hp⟩

/--
Positive prime-power rows birth their base support prime from the row index.
-/
theorem prime_power_rowBirthPrime
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    RowBirthPrime (p ^ n) p := by
  refine ⟨prime_power_innerRowSupportPrime hp, ?_⟩
  refine ⟨p ^ (n - 1), ?_⟩
  have hs : (n - 1).succ = n := by omega
  rw [Nat.mul_comm, ← Nat.pow_succ, hs]

/--
Package the support observation and the positive exponent together.
-/
theorem prime_power_rowSupport
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    PrimePowerRowSupport p n :=
  ⟨hp, hn, prime_power_innerRowSupportPrime hp⟩

/--
Kummer's prime-power binomial valuation in `padicValNat` form.

Mathlib proves this first as a `Nat.factorization` identity; this lemma exposes
the same statement through the ABC valuation API used elsewhere in DkMath.
-/
theorem padicValNat_choose_prime_pow
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k := by
  have hfac := Nat.factorization_choose_prime_pow hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
Kummer's prime-power binomial valuation in additive form.

This is often the most convenient formulation for filters: the support carried
by the coefficient plus the support already present in the index is exactly the
row exponent.
-/
theorem padicValNat_choose_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n := by
  have hfac := Nat.factorization_choose_prime_pow_add_factorization hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac

/--
Prime-power row filter.

If the requested layer `r` plus the `p`-support already present in the index
fits inside the row exponent `n`, then the binomial coefficient carries `p^r`.
-/
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k := by
  have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
  have hvchoose :
      padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k :=
    padicValNat_choose_prime_pow hp hkn hk0
  have hr_le : r ≤ padicValNat p (Nat.choose (p ^ n) k) := by
    rw [hvchoose]
    omega
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne r).mp hr_le

/--
Positive uniform beam height implies ordinary inner coefficient divisibility.

This is the bridge from the stricter p-adic height view back to the older
`AllInnerChooseDivisible` support view.
-/
theorem UniformBeamHeight.allInnerChooseDivisible
    {d p h : ℕ} (hp : p.Prime) (hh : 0 < h)
    (H : UniformBeamHeight d p h) :
    AllInnerChooseDivisible d p := by
  intro k hk0 hkd
  have hk_le : k ≤ d := hkd.le
  have hchoose_ne : Nat.choose d k ≠ 0 := Nat.choose_ne_zero hk_le
  have hv : padicValNat p (Nat.choose d k) = h := H k hk0 hkd
  simpa using
    (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne 1).mp (by omega)

/--
Uniform beam height refines an inner row support prime when the height is
positive.
-/
theorem UniformBeamHeight.innerRowSupportPrime
    {d p h : ℕ} (hp : p.Prime) (hh : 0 < h)
    (H : UniformBeamHeight d p h) :
    InnerRowSupportPrime d p :=
  ⟨hp, H.allInnerChooseDivisible hp hh⟩

/--
Below row `p`, the prime `p` is absent from every beam coefficient.

This gives the lower side of the `p`-boundary: before the prime row, the
`p`-adic beam height is uniformly zero.
-/
theorem below_prime_uniformBeamHeight_zero
    {d p : ℕ} (hp : p.Prime) (hdp : d < p) :
    UniformBeamHeight d p 0 := by
  intro k _hk0 _hkd
  have hfac : (Nat.choose d k).factorization p = 0 :=
    Nat.factorization_choose_eq_zero_of_lt hdp
  rw [Nat.factorization_def (Nat.choose d k) hp] at hfac
  exact hfac

/--
No row below `p` contains `p` in an inner binomial coefficient.
-/
theorem below_prime_not_dvd_inner_choose
    {d p k : ℕ} (hp : p.Prime) (hdp : d < p)
    (hk0 : 0 < k) (hkd : k < d) :
    ¬ p ∣ Nat.choose d k := by
  have H : UniformBeamHeight d p 0 :=
    below_prime_uniformBeamHeight_zero hp hdp
  have hk_le : k ≤ d := hkd.le
  have hchoose_ne : Nat.choose d k ≠ 0 := Nat.choose_ne_zero hk_le
  have hv : padicValNat p (Nat.choose d k) = 0 := H k hk0 hkd
  exact (DkMath.ABC.padicValNat_eq_zero_iff hp hchoose_ne).mp hv

/--
Prime rows have uniform beam height `1` at their own prime.
-/
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 := by
  intro k hk0 hkp
  have hkp_le : k ≤ p := hkp.le
  have hk_ne : k ≠ 0 := hk0.ne'
  have hpk : ¬ p ∣ k := by
    intro hdiv
    have hple : p ≤ k := Nat.le_of_dvd hk0 hdiv
    omega
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk_ne).mpr hpk
  have hkp_pow : k ≤ p ^ 1 := by simpa using hkp_le
  simpa [hvk] using
    (padicValNat_choose_prime_pow (p := p) (n := 1) (k := k) hp hkp_pow hk_ne)

/--
Prime rows satisfy the beam-birth boundary.
-/
theorem prime_beamBirthBoundary
    {p : ℕ} (hp : p.Prime) :
    BeamBirthBoundary p :=
  ⟨fun _ hdp => below_prime_uniformBeamHeight_zero hp hdp,
    prime_uniformBeamHeight_self hp⟩

/--
In the row before a prime row, adjacent coefficients are negatives modulo the
prime.

This is the local step behind the visible alternating pattern in row `p - 1`.
-/
theorem prime_prebirthAlternation_step
    {p k : ℕ} (hp : p.Prime) (hk : k + 1 < p) :
    ((Nat.choose (p - 1) (k + 1) : ZMod p) =
      - (Nat.choose (p - 1) k : ZMod p)) := by
  have hpascal :
      Nat.choose p (k + 1) =
        Nat.choose (p - 1) k + Nat.choose (p - 1) (k + 1) := by
    simpa using Nat.choose_succ_right p k hp.pos
  have hdiv : p ∣ Nat.choose p (k + 1) :=
    prime_dvd_inner_choose hp (Nat.succ_pos k) hk
  have hzero : ((Nat.choose p (k + 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum :
      (Nat.choose (p - 1) k : ZMod p) +
        (Nat.choose (p - 1) (k + 1) : ZMod p) = 0 := by
    simpa [hpascal, Nat.cast_add] using hzero
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum)

/--
Prime rows have a pre-birth alternation one row below them.

Modulo `p`, row `p - 1` is exactly the coefficient pattern of `(1 - 1)^(p-1)`:
the `k`-th coefficient is `(-1)^k`.
-/
theorem prime_prebirthAlternation
    {p : ℕ} (hp : p.Prime) :
    PrimePrebirthAlternation p := by
  intro k
  induction k with
  | zero =>
      intro _hk
      simp
  | succ k ih =>
      intro hk
      have hk_prev : k ≤ p - 1 := by omega
      have hk_lt : k + 1 < p := by omega
      calc
        (Nat.choose (p - 1) (k + 1) : ZMod p)
            = - (Nat.choose (p - 1) k : ZMod p) :=
              prime_prebirthAlternation_step hp hk_lt
        _ = - ((-1 : ZMod p) ^ k) := by rw [ih hk_prev]
        _ = (-1 : ZMod p) ^ (k + 1) := by
              rw [pow_succ]
              ring

/-- The lower side of a packaged beam-birth boundary. -/
theorem BeamBirthBoundary.below
    {p d : ℕ} (H : BeamBirthBoundary p) (hdp : d < p) :
    UniformBeamHeight d p 0 :=
  H.1 d hdp

/-- The birth-row side of a packaged beam-birth boundary. -/
theorem BeamBirthBoundary.self
    {p : ℕ} (H : BeamBirthBoundary p) :
    UniformBeamHeight p p 1 :=
  H.2

/--
For a known prime, a beam-birth boundary recovers the older inner support-prime
view.
-/
theorem BeamBirthBoundary.innerRowSupportPrime
    {p : ℕ} (hp : p.Prime) (H : BeamBirthBoundary p) :
    InnerRowSupportPrime p p :=
  H.self.innerRowSupportPrime hp (by norm_num)

/--
Any concrete obstruction rules out the beam-birth boundary.
-/
theorem not_beamBirthBoundary_of_obstruction
    {p : ℕ} (h : BeamBirthBoundaryObstruction p) :
    ¬ BeamBirthBoundary p := by
  rintro H
  rcases h with ⟨k, hk0, hkp, hk_ne⟩
  exact hk_ne (H.self k hk0 hkp)

/--
The prime boundary has no obstruction.
-/
theorem not_obstruction_of_prime
    {p : ℕ} (hp : p.Prime) :
    ¬ BeamBirthBoundaryObstruction p := by
  exact fun h => not_beamBirthBoundary_of_obstruction h (prime_beamBirthBoundary hp)

/--
Prime rows recover their inner support prime through the uniform-height bridge.
-/
theorem prime_innerRowSupportPrime_self_of_uniformBeamHeight
    {p : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime p p :=
  (prime_uniformBeamHeight_self hp).innerRowSupportPrime hp (by norm_num)

/--
In row `p^n`, the indices not divisible by `p` all have coefficient height
exactly `n`.

This is the first filtered `p^n` sieve: the full beam has varying height, but
the `p`-unit index layer is uniform.
-/
theorem prime_power_unitFilteredBeamHeight
    {p n : ℕ} (hp : p.Prime) :
    FilteredBeamHeight (p ^ n) p n (fun k => ¬ p ∣ k) := by
  intro k hk0 hkp hpk
  have hk_le : k ≤ p ^ n := hkp.le
  have hk_ne : k ≠ 0 := hk0.ne'
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk_ne).mpr hpk
  rw [padicValNat_choose_prime_pow hp hk_le hk_ne, hvk, Nat.sub_zero]

/--
If the inner index is a `p`-unit, the row `p^n` coefficient carries the full
`p^n` divisibility.
-/
theorem prime_power_dvd_choose_of_not_dvd_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0).mpr hpk
  exact prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 (by omega)

/--
The unit-index layer of a prime-power row carries the full `p^n` divisibility,
derived through the filtered beam-height interface.
-/
theorem prime_power_unitFilteredBeamHeight_dvd_choose
    {p n k : ℕ} (hp : p.Prime)
    (hk0 : 0 < k) (hkp : k < p ^ n) (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  exact
    (prime_power_unitFilteredBeamHeight (p := p) (n := n) hp).dvd_choose_of_height_ge
      hp hk0 hkp hpk le_rfl

section samples

example {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  prime_power_innerRowSupportPrime hp

example {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k :=
  prime_power_dvd_choose_of_not_dvd_index hp hkn hk0 hpk

example {p n k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p ^ n)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k :=
  prime_power_unitFilteredBeamHeight_dvd_choose hp hk0 hkp hpk

example {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k :=
  prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 hr

example {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 :=
  prime_uniformBeamHeight_self hp

example {p : ℕ} (hp : p.Prime) :
    BeamBirthBoundary p :=
  prime_beamBirthBoundary hp

example {d p : ℕ} (hp : p.Prime) (hdp : d < p) :
    UniformBeamHeight d p 0 :=
  below_prime_uniformBeamHeight_zero hp hdp

example {p n : ℕ} (hp : p.Prime) :
    FilteredBeamHeight (p ^ n) p n (fun k => ¬ p ∣ k) :=
  prime_power_unitFilteredBeamHeight hp

end samples

end NumberTheory
end DkMath
