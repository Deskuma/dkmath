# GMPT-004 — Petal-path turnover capacity audit

## Scope and result

GMPT-000 through GMPT-003 were audited at their current validated boundary.
The audit compares the finite Petal-path support localization with the
existing Legendre adjacent-shell and parity-safe capacity ledgers.  It does
not introduce a new capacity API.

The path information gives an exact factor-level restatement of the existing
prime-divisor filter.  It does not supply a strict cardinality reduction,
deleted support channel, injection into a smaller capacity space, or a new
full-cover inequality.

## Phase 1 — exact path-to-turnover consequence

The relevant existing theorems are:

- `DkMath.NumberTheory.MultiGauge.oddGnomon_petalFold`:
  `oddGnomon (petalFold a bs) = oddGnomon a * (bs.map oddGnomon).prod`;
- `DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_lower_iff`;
- `DkMath.NumberTheory.Legendre.mem_reindexed_primeSupport_inter_lower_petalMul_iff`;
- `DkMath.NumberTheory.MultiGauge.exists_petalFactor_dvd_of_start_escape_of_end_caught`.

For `n = petalFold a bs`, `hr : SquareOffset n r`, `hlow : r < n + 1`, and
prime `q`, the strongest unconditional lower-turnover consequence is the
following exact membership expansion:

```text
q ∈ squareOffsetPrimeSupport n r ∩
    squareOffsetPrimeSupport (n + 1)
      (successorThresholdInsert n r)
↔
q ∈ squareOffsetPrimeSupport n r ∧
  (q ∣ oddGnomon a ∨ ∃ b ∈ bs, q ∣ oddGnomon b).
```

This follows by applying `mem_reindexed_primeSupport_inter_lower_iff`, then
expanding `oddGnomon (petalFold a bs)` and repeatedly applying
`Nat.Prime.dvd_mul`.  Under
`¬ q ∣ oddGnomon a` and `∀ b ∈ bs, ¬ q ∣ oddGnomon b`, the lower common
support is absent.  This is a precise qualitative support-localization result,
but it remains a divisibility restatement.

The one-step instance is already implemented by
`mem_reindexed_primeSupport_inter_lower_petalMul_iff` and
`common_lower_dvd_gnomonPetalTransition_numerator_of_not_dvd_first`.

## Phase 2 — cardinality test

Let

```text
S := squareOffsetPrimeSupport n r
    ∩ squareOffsetPrimeSupport (n + 1)
        (successorThresholdInsert n r).
```

The existing exact theorem identifies `S` with

```text
(squareOffsetPrimeSupport n r).filter (fun q => q ∣ oddGnomon n).
```

For every prime `q`, the Petal path gives only the equivalent predicate

```text
q ∣ oddGnomon a ∨ ∃ b ∈ bs, q ∣ oddGnomon b.
```

Consequently, filtering the same support by the factor union has the same
members as filtering by `q ∣ oddGnomon n`.  A sum of the factor-support
cardinalities is generally weaker because repeated factors can overlap; a
union bound is merely an alternate presentation of the same filtered set.
No strict smaller right-hand side or non-overlap theorem for the factor
channels is available.

Diagnostics make the boundary concrete:

- `oddGnomon 30 = 61` is prime, and the existing theorem
  `disjoint_reindexed_primeSupport_lower_30` already gives the lower
  disjointness result;
- `petalMul 1 2 = 7` and `oddGnomon 7 = 15 = 3 * 5`, so the two factor
  channels expose `{3, 5}`, exactly the prime support of the product;
- `petalMul 1 1 = 4` and `oddGnomon 4 = 9`, where two repeated factor
  occurrences expose only `{3}`.  The naive sum bound counts occurrences and
  is weaker, not sharper.

These are finite diagnostics, not a theorem of impossibility.

## Phase 3 — atomic endpoint test

`DkMath.Gnomon.prime_oddGnomon_iff_petalAtom` gives

```text
PetalAtom n ↔ Nat.Prime (oddGnomon n).
```

The existing theorem
`disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon` already consumes
the right-hand side directly.  Replacing its prime hypothesis by the
equivalent `PetalAtom` hypothesis changes the vocabulary only; it does not
reduce `paritySafeSupportExcess`, pair overlap, or any capacity term.

No theorem was found that makes distinct factor channels pairwise disjoint,
or that excludes a composite endpoint family from the existing support
ledger.  Petal atomicity therefore supplies normalization/transport only at
this checkpoint.

## Phase 4 — interface with the full-cover frontier

The audited production layers and their current quantities are:

| Layer | Existing exact interface | GMPT-003 effect |
| --- | --- | --- |
| Local support | `mem_reindexed_primeSupport_inter_lower_iff`, `mem_reindexed_primeSupport_inter_lower_petalMul_iff` | Yes; exact factor localization only |
| Pair-overlap ledger | `paritySafePrimePairOverlapCount_eq_outsideCollision_add_collisionMass` | No new containment or injection |
| Incidence count | `paritySafeIncidenceConservation`, `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence` | No connection to Petal factor channels |
| Residual capacity | `paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_fiberExcess_add_collisionResidualPairSlack` | No reduction of fiber or slack terms |
| Full-cover candidate balance | `two_mul_pairOverlap_add_threeCollision_add_threeCandidate_le_fullCoverCapacity` and its totient forms | No changed left/right quantity |

The related slack frontier also remains unchanged:
`paritySafeLowCostResidualCapacity_eq_mass_add_slack` and
`paritySafeFullCoverRequiredLowCostSlack_le_two_capacitySlack` have no Petal
support hypothesis.  The capacity modules are co-exported by
`DkMath.NumberTheory.Legendre`, but no production theorem links the Petal
path to `paritySafeSupportExcess`,
`paritySafePrimePairOverlapCount`,
`paritySafeLowCostResidualCapacity`, or
`paritySafeRechargeExactDepthResidualPairCapacityExcess`.

Thus the new information touches local support only.  It does not yet touch
the pair-overlap ledger, incidence count, residual capacity, or full-cover
candidate balance.

## Missing bridge for a future strict gain

A strict result would require at least one explicit new theorem of one of
these forms:

1. pairwise disjointness of distinct factor-support channels under a stated
   hypothesis; or
2. an injection from the relevant surviving lower-common-support seats into a
   strictly smaller Petal-factor support space; or
3. a proved containment from the Petal-localized support into one of the
   existing capacity terms with a strict numerical/cardinality bound.

The current path API proves none of these, and the factor-product identity
alone cannot provide them.

## Validation

The current branch was checked with:

```text
lake build DkMath.NumberTheory.MultiGauge
lake build DkMath.NumberTheory.Legendre
```

The audit added documentation only; no production Lean module or facade was
changed.  No new axiom or forbidden proof construct was introduced.

Outcome B — STRUCTURAL NORMALIZATION ONLY
