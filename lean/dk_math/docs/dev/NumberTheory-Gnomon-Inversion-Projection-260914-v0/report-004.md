# GNIP-004 report — successor gnomon balance / support firewall

## 1. Outcome

**A — STRUCTURAL FIREWALL FOUND.**

The `n -> n + 1` open-shell growth is exactly two seats, and the fresh prime
threshold controls exactly those two seats.  The natural threshold-skipping
reindex is formally placed in the threshold-free successor shell, but it does
not preserve old-basis coverage.  Its common-support channels are controlled
by the exact point displacement: `oddGnomon n` in the lower region and
`2 * (n + 1)` in the upper region.

This is an anti-preservation/firewall result.  It is not a support transport
theorem, full-cover propagation theorem, or proof of Legendre's conjecture.

## 2. Files added or changed

```text
DkMath/NumberTheory/Legendre/GnomonSuccessor.lean   added
DkMath/NumberTheory/Legendre.lean                   exports GnomonSuccessor
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-004.md
                                                       added
```

The existing shell, gnomon, and successor decomposition definitions were not
modified.

## 3. Theorem inventory

Shell and threshold balance:

```text
card_squareOffsets_succ_add_two
oddGnomon_succ_add_two
successorThresholdOffsets
successorThresholdOffsets_subset_squareOffsets_succ
card_successorThresholdOffsets
mem_successorThresholdOffsets_iff_threshold_dvd
card_squareOffsets_succ_sdiff_threshold
```

The exact finite balance is:

```text
(squareOffsets (n + 1)).card = (squareOffsets n).card + 2
card {n + 1, 2 * (n + 1)} = 2
card (squareOffsets (n + 1) \ {n + 1, 2 * (n + 1)}) =
  card (squareOffsets n)
```

Under `Nat.Prime (n + 1)`, existing
`successorThresholdPrime_dvd_iff` identifies those two seats exactly with
divisibility by the fresh threshold.

The candidate seat map is:

```text
successorThresholdInsert n r := if r < n + 1 then r else r + 1
```

Its pointwise shell result is
`successorThresholdInsert_mem_sdiff`: every old `SquareOffset n r` maps into
the threshold-removed successor shell.  No larger custom equivalence
framework was introduced; coverage already fails pointwise at the required
30→31 witnesses below.

## 4. Same-offset firewall

The principal new theorem is:

```text
dvd_oddGnomon_of_dvd_adjacent_square_points
```

It proves, for arbitrary natural `q`,

```text
q ∣ n^2 + r ∧ q ∣ (n + 1)^2 + r
  -> q ∣ oddGnomon n.
```

This follows from the subtraction-free identity

```text
(n + 1)^2 + r = (n^2 + r) + oddGnomon n.
```

`oldPrime_not_common_sameOffset` gives the old-prime support form: an old
prime direction not dividing the unit gnomon cannot cover the same offset at
both anchors.

## 5. Candidate reindex firewall

The two exact additive displacement theorems are:

```text
successorThresholdInsert_lower_additive_displacement
successorThresholdInsert_upper_additive_displacement
```

They state respectively:

```text
r < n + 1:
  (n + 1)^2 + insert(r) = (n^2 + r) + oddGnomon n

n + 1 ≤ r:
  (n + 1)^2 + insert(r) = (n^2 + r) + 2 * (n + 1)
```

The corresponding divisor restrictions are proved by:

```text
dvd_oddGnomon_of_dvd_reindexed_lower_common
dvd_two_mul_succ_of_dvd_reindexed_upper_common
```

Thus the natural cardinality-preserving coordinate has a support firewall,
not support preservation.

## 6. Required 30 -> 31 regression

The following are kernel-checked:

```text
oddGnomon 30 = 61
oddGnomon 31 = 63
(squareOffsets 30).card = 60
(squareOffsets 31).card = 62
primeScalesUpTo 31 = insert 31 (primeScalesUpTo 30)
successorThresholdOffsets 30 = {31, 62}
card (squareOffsets 31 \ successorThresholdOffsets 30) = 60
```

Coverage is falsified in both directions for the canonical reindex:

```text
30, r = 6:
  30^2 + 6 = 906 is old-basis covered;
  31^2 + 6 = 967 is old-basis unreserved.

30, r = 7:
  30^2 + 7 = 907 is old-basis unreserved;
  31^2 + 7 = 968 is old-basis covered.
```

These are the named kernel-checked theorems
`successor_reindex_30_6_mismatch` and
`successor_reindex_30_7_mismatch`.  The cover witnesses in the covered cases
are supplied by the old prime `2`; the unreserved cases are checked against
the complete finite `primeScalesUpTo 30` definition.

For lower-half common old support, the specialization
`oldPrime_30_not_common_lower_reindex` uses `61` and `q ≤ 30` to exclude every
old prime channel.  For the upper half,
`oldPrime_30_common_upper_reindex_dvd_62` proves divisibility by `62 = 2*31`;
among old primes at most `30`, only the channel `2` can remain.

## 7. Answers to the checkpoint questions

1. **Yes.** The shell gains exactly two seats, and a fresh threshold prime
   reserves exactly `31` and `62` at 30→31.
2. **No.** The candidate map lands in the threshold-free shell but does not
   preserve old-basis coverage; both 30→31 directions have explicit mismatches.
3. **Exact displacement controls it.** It is `oddGnomon n` below the split and
   `2*(n+1)` above it.
4. **Yes.** `oddGnomon n` is an exact same-offset persistence firewall.
5. **At 30→31:** no old prime can persist in the lower inserted region; the
   upper region can retain only `2`.
6. **No.** None of these finite identities implies full-cover propagation or
   full-cover failure, and no Legendre provider is added.
7. The production source does contain the separate real API
   `DkMath.CosmicFormula.Projection.Pi`, `U`, and
   `cosmicProjection_gap_eq` for `Pi P + 1 = U P`.  There is no current exact
   bridge from that real observer to this discrete successor-support firewall;
   the relation is therefore **NOT CONNECTED** in GNIP-004.  No new real or
   rational theory was introduced.
8. A bounded GNIP-005 is justified only as a finite support-image audit:
   test whether the old prime-support sets under
   `successorThresholdInsert` admit an exact image/intersection description,
   stopping at the firewall if they do not.  It must not be promoted to a
   full-cover or Legendre route.

## 8. Dependencies and validation

The new module imports only:

```text
DkMath.NumberTheory.Legendre.GnomonBridge
DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
Mathlib.Tactic
```

Validation from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.Legendre.GnomonSuccessor
Build completed successfully (8697 jobs).

lake build DkMath.NumberTheory.Legendre
Build completed successfully (8775 jobs).

lake build DkMath.Gnomon
Build completed successfully (8658 jobs).

git diff --check
passed with no diagnostics.
```

The changed Lean files were scanned for `sorry`, `admit`, and `axiom`; no
matches were found.  No new axiom or provider predicate was introduced.
