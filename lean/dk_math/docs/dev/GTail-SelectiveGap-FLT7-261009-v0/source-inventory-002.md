# Source inventory 002 — before implementation

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Working tree was clean at the start. Module paths are relative to `lean/dk_math`.
No repository AGENTS.md was found in the preceding checkpoint or current scan.

## Existing neutral interfaces

Read `DkMath/Lib/Cosmic/GTailSelection.lean` and
`DkMathTest/CosmicFormula/GTailSelection.lean` in their current styled form.
Namespace is `DkMath.CosmicFormula`. All selection declarations have implicit
`{R : Type*} [CommSemiring R]`:

```lean
selectedTerm (d k : ℕ) (x u : R) : R
selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) : R
selectedGap (d : ℕ) (S : Finset ℕ) (x u : R) : R
selectedGap_add_selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) :
  (x+u)^d = selectedGap d S x u + selectedBody d S x u
selectedBody_singleton (d k : ℕ) (x u : R) (hk : k ≤ d) :
  selectedBody d {k} x u = selectedTerm d k x u
selectedBody_Ico (d r : ℕ) (x u : R) (hr : r ≤ d) :
  selectedBody d (Finset.Ico r (d+1)) x u = x^r * GTail d r x u
selectedGap_Ico (d r : ℕ) (x u : R) (hr : r ≤ d) :
  selectedGap d (Finset.Ico r (d+1)) x u =
    ∑ j ∈ Finset.range r, (Nat.choose d j : R)*x^j*u^(d-j)
```

Empty/full identities and bounded complement swap already exist; no new copies
are needed. Body and Gap sum over filters of `range (d+1)`. Indices count `x^k`.

Also read the four canonical modules:

- `GTail.lean`: `GTail {R} [CommSemiring R] (d r : ℕ) (x u : R) : R`;
  `add_pow_eq_prefix_add_xpow_mul_GTail {R} [CommSemiring R]
  (d r : ℕ) (x u : R) (hr : r ≤ d)` gives prefix plus `x^r*GTail`;
  `higher_tail_eq_pow_mul_GTail` gives the subtraction version with `[CommRing R]`;
  `GTail_rec` has the same semiring arguments and `hr : r < d`.
- `GTailPascal.lean`: `GTail_split_at {R} [CommSemiring R]
  (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d)` gives the first
  `s-r` normalized layers plus `x^(s-r)*GTail d s x u`.
- `GTailBoundary.lean`: `gcd_GTail_eq_gcd_boundary (d r x u : ℕ)
  (hr : r ≤ d)` gives `gcd x (GTail ...) = gcd x (choose d r*u^(d-r))`;
  `gcd_GTail_eq_gcd_choose` adds `(hcop : Nat.Coprime x u)` and removes `u`.
  This is an evaluated gcd under hypotheses, not coefficient content.
- `GTailNat.lean`: `pow_dvd_higher_tail (d r x u : ℕ) (hr : r ≤ d)`;
  `GTail_not_dvd_of_head_unit_of_prime_dvd_x {p d r x u : ℕ}
  (_hp : Nat.Prime p) (hr : r < d)
  (hhead : ¬ p ∣ Nat.choose d r*u^(d-r)) (hpx : p ∣ x)`.

## Existing coefficient gcd / Mathlib APIs

Repository search found `DkMath/NumberTheory/PascalPrebirthBoundary.lean`:
`pascalInnerCommonDivisor (N : ℕ) : ℕ := (Icc 1 (N-1)).gcd (Nat.choose N)`
and `pascalInnerCommonDivisor_eq_self_of_prime {N : ℕ} (h : N.Prime)`.
That owner imports broader ABC/number-theory dependencies. We do not import it
into Lib or duplicate its whole-row classification. The new content interface
is for arbitrary active selections, including sparse subsets.

Mathlib source inspected:

- `Algebra/GCDMonoid/Finset.lean`: `Finset.gcd (s : Finset β) (f : β → α) : α`
  under `[CommMonoidWithZero α] [NormalizedGCDMonoid α]`;
  `gcd_empty`, `gcd_dvd (hb : b ∈ s) : s.gcd f ∣ f b`,
  `dvd_gcd_iff : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b`.
  Nat instances are supplied by its imports; empty gcd is 0.
- `Data/Nat/Choose/Dvd.lean`: `Nat.Prime.dvd_choose_self
  (hp : Nat.Prime p) (hk : k ≠ 0) (hkp : k < p) : p ∣ Nat.choose p k`.
- `Data/Nat/Choose/Lucas.lean`: `Choose.gcd_choose_eq_minFac_of_isPrimePow`
  classifies the full inner row. Not required for arbitrary selection: prime
  divisibility plus a retained coefficient `choose p 1 = p` suffices.
- `Algebra/BigOperators/Ring/Finset.lean`: `Finset.dvd_sum
  (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i`.
  Existing sum multiplication and `pow_add` suffice for the semiring factor.
- `Data/Finset/Max.lean`: `min'`, `max'` on nonempty finsets;
  `min'_le`, `le_max'`, `max'_mem`, `min'_le_max'` permit a min/max corollary.
- `RingTheory/Polynomial/Content.lean`: `Polynomial.content` is defined for
  `[CommRing R] [NormalizedGCDMonoid R]` as `p.support.gcd p.coeff`;
  `content_dvd_coeff` and `dvd_content_iff_C_dvd` are univariate polynomial
  interfaces. No univariate carrier is needed or introduced here. The natural
  gcd of raw active Pascal coefficients remains distinct from evaluated values.

## Minimal additions planned

`DkMath.Lib.Cosmic.GTailFactor` will directly import selection, finite gcd,
finite extrema, and prime choose divisibility. Define `activeSelectedIndices`,
`selectedResidual`, and `coeffGCD`. Prove the factor under `i ≤ j ≤ d` and
`∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j`, its min/max corollary,
and natural divisibility. Add coefficient gcd divisibility, empty convention,
endpoint gcd=1, and combined coefficient/monomial divisor.

Prime exactness is an adapter for arbitrary active interior subsets retaining
index 1, then specialize to `Ico 1 p`, including p=2. This reuses Mathlib's
prime coefficient theorem; no new GTail recursion, full Pascal classification,
FLT imports, transport, degree-seven norm factorization, or façade export.
