# ABC Eisenstein factor counting — report-000

## Scope and branch audit

- Repository: `Deskuma/dkmath`
- Branch: `research/ABC-Eisenstein-factor-counting-260915-v0`
- HEAD at inventory time: `c951d9841515ac8885bc5900691ec6501995bcc5`
- Working tree at inventory time: clean
- Lean build directory: `lean/dk_math`
- Governing document: `instruction-000.md` in this directory

This report records the theorem surface before adding counting-specific
production declarations.  The attached instruction is treated as a bounded
research contract; the user request is to continue the investigation after
the branch change and to record findings incrementally.

## Existing provider and coordinate API

`DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider` already proves the
factor-existence statement
`GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor`.
For every shell witness `a` it supplies `beta gamma : TraceOneInt (-1)` with

```text
natAbs (norm beta) = oddPart M * S
natAbs (norm gamma) = evenPart M
eisensteinCoord ((a : ℤ) + 2) 1 = beta * gamma^2,
```

where `M = GNExcessCubicFullRepeatedModulus a` and
`S = GNExcessCubicComplement a`.  The provider is imported from the current
branch and is left unchanged.

`DkMath.Lib.NumberTheory.EisensteinCoordinates` fixes the production
coordinates
`eisensteinCoord m n = (m,-n)` and proves the multiplication, square, norm,
and coefficient consequences.  In particular, an explicit factor equality
gives the exact equation

```text
b * (2*m*n - n^2) + c * (m^2 - 2*m*n) = 1
```

and `IsCoprime (2*m*n - n^2) (m^2 - 2*m*n)`.

## Existing exact finite identities

The current ABC surface already contains the following kernel-checked finite
identities and injections.

1. `GNExcessCubicRealizedIncidence` defines the shell witness spaces,
   exact full-repeated fibers, and the witness count.  Its fiber disjointness
   theorem gives the exact sum of full-repeated fiber cardinalities.
2. `GNExcessCubicComplementIncidence` defines the canonical pair `(M,S)`,
   proves the pair is injective, and proves the exact sum over complement
   fibers.  The represented `(M,S)` incidence-pair space has cardinality
   exactly equal to the witness count.
3. `GNExcessCubicRealizedDyadic` gives the dyadic shell decomposition and
   moment inequalities conditional on shell-card bounds.
4. `GNExcessCubicSquarefulPell` and `GNExcessCubicPrimitivePell` provide
   squareful/parity/Pell identities and primitive necessary conditions, but
   explicitly no Pell solution count or density estimate.
5. `GNExcessCubicIncidenceObstruction` records necessary weighted incidence
   conditions; it does not provide incidence sparsity.
6. `GNExcessCubicEisensteinFactorConsequences` proves coefficient-one,
   coefficient-coprimality, and norm identities for an explicitly supplied
   factor pair.  These are conditional consequences, not a finite count.

Thus the existing `(M,S)` relation is already an exact cardinality-preserving
encoding of shell witnesses.  A factor-pair relation can improve the count
only after a new finite fiber/cardinality restriction is proved.

## Quantitative gaps exposed by the inventory

- No existing theorem parametrizes all coefficient-one solutions for fixed
  `(m,n)` by a one-dimensional integer parameter.
- No existing theorem gives a strict bound on the number of admissible
  `beta` for fixed `gamma` and fixed residual norm `T`.
- No existing finite set bounds the number of `gamma` representations of a
  given `evenPart M` in a way that is compared to the `(M,S)` incidence space.
- The norm API supplies the positive-definite polynomial identity, but the
  square-root coordinate bounds needed for a finite factor space have not
  yet been specialized to the provider data.

The next investigation step is therefore the balanced-line comparison
theorem, followed by finite norm-box experiments and a direct multiplicity
comparison with the existing incidence frontiers.

## Balanced-line result (scratch, kernel checked)

`scratch/BalancedLine.lean` proves the exact two-solution comparison

```lean
∃ k : ℤ, b' - b = k * R ∧ c' - c = -k * Q
```

from `IsCoprime Q R` and two equations `b*Q+c*R=1` and
`b'*Q+c'*R=1`.  The proof extracts Bezout coefficients `u,v` with
`u*Q+v*R=1`, sets
`k = (b'-b)*v - (c'-c)*u`, and checks both coordinates by polynomial
normalization.  The scratch file builds with `lake env lean` and has no
`sorry`/`admit`/custom axiom.  This confirms the requested signs for the
production coordinate convention.

This result reduces a fixed-`gamma` beta search to one integer parameter, but
it is only a parametrization.  A kernel proof that the resulting quadratic
norm polynomial has at most two integral roots, together with a bound on the
number of gamma representations of `d`, is still needed before this can imply
a shell-cardinality inequality.

## Deterministic finite diagnostic

`scratch/Diagnostics.py` extends the earlier exact coordinate scan and stores
its JSON output in `scratch/Diagnostics-results.json`.  The run covers all
cubic coefficient-one values `0 ≤ a ≤ 2000`; it does not assert shell
membership.  It records:

- prescribed norm factorization failures: `0`;
- provider-compatible landing pairs including unit associates: exactly `6`
  for each of the `2001` values;
- fixed `(gamma,T)` coefficient-line fiber sizes: histogram
  `0 ↦ 24`, `1 ↦ 1560`, `2 ↦ 11226`, with observed maximum `2`;
- the six landing pairs are the visible Eisenstein unit multiplicity, while
  the norm shell for `gamma` commonly has twelve coordinate representations.
- the gamma representation histogram is `6 ↦ 1871`, `12 ↦ 127`,
  `18 ↦ 2`, `24 ↦ 1`; summing the coefficient-line fibers gives `24012`
  admissible `(a,gamma,beta)` records against `2001` scanned cubic values.

The observed bound `2` is evidence for the ellipse/line picture only; it is
not promoted to a theorem.  In particular, counting all factor pairs with
units does not produce a smaller space than the exact `(M,S)` pair, whose
cardinality is already exactly the witness count.

The same scratch Lean file also kernel-checks the reusable positive-definite
inequality
`x^2 + y^2 ≤ 2 * (x^2 - x*y + y^2)`.  It is the correct starting point for
square-root coordinate bounds, but no natural-number box/cardinality estimate
was added because it would not change the Outcome-B comparison without the
missing fiber and gamma-representation bounds.

## Validation and classification

The provider source and all existing ABC/Lib surfaces were left unchanged.
Focused validation succeeded:

```text
lake env lean docs/dev/ABC-Eisenstein-factor-counting-260915-v0/scratch/BalancedLine.lean   exit 0
lake build DkMath.ABC                                                               exit 0
lake build DkMath.Lib                                                               exit 0
```

The provider theorem remains available with its prior kernel-checked axiom
profile.  Since the new balanced-line fact is currently only a scratch
parametrization and the factor-pair scan carries six unit associates per
coefficient-one value, no strict RHS improvement over the existing incidence
ledger has been established.

**Outcome B — structural normalization only.**  The branch now has a checked
one-dimensional balanced-line normal form for future work, but this checkpoint
does not justify a new production counting module or a shell-count bound.
