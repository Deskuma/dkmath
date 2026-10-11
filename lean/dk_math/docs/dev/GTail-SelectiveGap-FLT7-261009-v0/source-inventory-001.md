# Source inventory 001

Inspected on `feature/GTail-SelectiveGap-FLT7-261009-v0`, before implementation.
No pre-existing workspace changes or AGENTS.md files were found.

## Existing source

All paths below are relative to `lean/dk_math`.

- `DkMath/Lib/Cosmic/GTail.lean`: namespace `DkMath.CosmicFormula`.
  `GTail {R} [CommSemiring R] (d r : ℕ) (x u : R) : R`
  is `∑ k ∈ range (d+1-r), (choose d (r+k) : R)*x^k*u^(d-(r+k))`.
  `add_pow_eq_prefix_add_xpow_mul_GTail {R} [CommSemiring R]
  (d r : ℕ) (x u : R) (hr : r ≤ d)` states
  `(x+u)^d = (∑ j ∈ range r, (choose d j : R)*x^j*u^(d-j)) + x^r*GTail d r x u`.
  `higher_tail_eq_pow_mul_GTail` has the same arguments with `[CommRing R]`
  and states the corresponding subtraction equality.
  `GTail_rec` uses `hr : r < d`; `GTail_zero_eq_add_pow` and
  `GTail_self_eq_one` have no range assumptions.
- `GTailPascal.lean`: `GTail_split_at {R} [CommSemiring R]
  (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d)` splits the
  normalized tail into the first `s-r` layers and `x^(s-r)*GTail d s x u`.
- `GTailBoundary.lean`: natural-number `gcd_GTail_eq_gcd_boundary
  (d r x u : ℕ) (hr : r ≤ d)`; `gcd_GTail_eq_gcd_choose` additionally
  takes `hcop : Nat.Coprime x u`. These are arithmetic downstream APIs.
- `GTailNat.lean`: `pow_dvd_higher_tail (d r x u : ℕ) (hr : r ≤ d)`;
  `GTail_not_dvd_of_head_unit_of_prime_dvd_x` requires prime `p`, `r<d`,
  a nondivisible head, and `p ∣ x`. Neither defines selection.
- `DkMath/Lib.lean` and `DkMath/Lib/README.md`: inspected existing exports
  and Cosmic family. Selection remains a direct import at Step 001;
  façade/README promotion belongs to Step 007.
- Search of `DkMath/Lib` found no `selectedBody`, `selectedGap`, or
  `selectedTerm` definitions. Existing filtration is interval-specific.

## Mathlib reuse and planned signatures

`Mathlib/Data/Nat/Choose/Sum.lean` supplies
`add_pow [CommSemiring R] (x y : R) (n : ℕ)` with summands
`x^i*y^(n-i)*(choose n i : R)`; multiplication is reordered only.
Finite filter partition, sum congruence, and `sum_Ico_add'` supply the
selection and interval adapter. No GTail recursion is replaced.

New definitions in `DkMath.CosmicFormula`, all over `[CommSemiring R]`:

- `selectedTerm (d k : ℕ) (x u : R) : R := (choose d k : R)*x^k*u^(d-k)`.
- `selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) : R`: sum over
  `(range (d+1)).filter (fun k => k ∈ S)`.
- `selectedGap`: same range filtered by `k ∉ S`.

Planned theorems: exact balance; empty/full bodies and gaps; bounded
complement swap; singleton extraction with `k ≤ d`; interval body equals
`x^r*GTail d r x u` and interval gap equals the prefix sum under `r ≤ d`.
All selection definitions ignore indices outside `range (d+1)`.
