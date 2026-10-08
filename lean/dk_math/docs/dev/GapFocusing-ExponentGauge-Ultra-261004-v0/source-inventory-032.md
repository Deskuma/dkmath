# Source inventory 032 - Least-factor quotient receivers

Instruction 032 is the bounded contract. The live checkout starts clean after
committed checkpoint 031. Earlier modules and reports are inspected and reused.

## Existing arithmetic receivers

- Mathlib.Data.Nat.Prime.Defs supplies minFac_prime, minFac_dvd,
  minFac_le_of_dvd, minFac_le_div, minFac_sq_le_self and le_minFac.
  They give primality, exact factorization, ordered factors, the square-root
  cutoff and all-prime-divisor restrictions without extra research hypotheses.
- Nat.div_lt_iff_lt_mul and Nat.le_div_iff_mul_le give the exact complementary
  interval A/r<m<=B/r for r>0. Natural floor endpoints and strict lower
  endpoint must be retained.
- Nat.le_sqrt' turns r^2<=B into r<=sqrt(B).
- Nat.Coprime.coprime_dvd_left transfers the existing wheel exclusion to both
  factors. Nat.Coprime.mul_left proves the converse product exclusion.
- Nat.not_prime_mul proves each covering pair product is composite for
  r>=2 and m>=r. A pair cover can therefore have duplicate products, but
  cannot introduce a prime product.
- Finset.sum_image and sum_le_sum_of_subset_of_nonneg support canonical
  injection into a larger weighted cover. No new general sum transport API
  is needed.

## Existing DkMath receivers and limits

GnomonCofactorSieve already supplies the endpoint carrier, reservation bridge,
V=Q+E, Q<=W<=G and the exact old-budget excess. These are reused unchanged.
The finite prime basis is the existing PrimorialUniverse basis, not a newly
created wheel type. minFac is outside its members; it exceeds a numeric cutoff
only if all primes through that cutoff are covered. A basis with gaps does not
justify comparison with its maximum.

ParitySafeSqrtRoughFactorization proves square-scale factor and complement
classification for canonicalRoughCandidates and active shell support. Its
candidate, cutoff and active-label hypotheses are different from the 031
cofactor windows. Importing that research stack would not identify the present
carrier. The elementary minFac receivers are enough, and the new production
module imports only GnomonCofactorSieve.

## Chosen bounded implementation

Canonical q routes to (minFac(q),q/minFac(q)), which reconstructs q and is
injective per window. Drop the condition that every prime divisor of m is at
least r, retain r prime/coprime, r<=sqrt(B), m>=r, the exact quotient endpoints
and m coprime. This is a finite factor-pair overcover, not the exact minFac sum.
Its weighted sum F bounds E without using Q or carry membership.

The upper-error direction V-F<=Q is explicitly proved. For a valid upper
singleton refinement, retain only diagonal products r*r as a certainly-
composite, distinct-product lower witness L<=E. One corrected envelope
U=min(W,V-L) and one old-ledger consumer are implemented. This does not enlarge
the fixed wheel and does not classify every composite away.
