# instruction-000 — LGF-000 exact reindexed support intersection

## Goal

Return the completed GNIP successor firewall to the Legendre application layer by proving an **exact support-intersection formula** for the canonical threshold-skipping reindex.

This checkpoint must stay below the full-cover frontier.  Do not attempt to prove Legendre's conjecture, full-cover failure, or a global capacity contradiction yet.

The intended new information is:

```text
old support ∩ successor support
=
old support filtered by the prime divisors of the exact reindex displacement.
```

For the lower half the displacement is `oddGnomon n`; for the upper half it is `2*(n+1)`.

---

## Read first

```text
DkMath/NumberTheory/Legendre/GnomonSuccessor.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/OldSupportGcd.lean
DkMath/NumberTheory/Legendre/FreshCollisionMatching.lean
DkMath/NumberTheory/Legendre/Frontier.lean
DkMath/NumberTheory/Legendre/ParitySafeFullCoverCapacityFrontier.lean
```

Important boundary:

- `OldSupportGcd` controls support intersections between **two seats in one fixed shell** through their seat gap.
- This checkpoint controls support intersections between **canonically paired seats in adjacent shells** through the successor displacement.

Do not duplicate `OldSupportGcd` under a new name.

---

## 1. Preferred production module

Create:

```text
DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean
```

Preferred imports:

```text
DkMath.NumberTheory.Legendre.GnomonSuccessor
```

Add another existing import only if needed for a theorem actually used.

If production theorems are obtained, export this module from:

```text
DkMath/NumberTheory/Legendre.lean
```

---

## 2. Lower-region exact intersection

For an old shell seat `r` with `r < n+1`, prove an exact membership theorem and preferably the corresponding Finset equality.

Target shape:

```lean
theorem mem_reindexed_primeSupport_inter_lower_iff
    {n r q : ℕ}
    (hr : SquareOffset n r)
    (hlow : r < n + 1) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧
        q ∣ DkMath.Gnomon.oddGnomon n
```

The key proof directions are:

```text
common support -> common divisibility -> GNIP firewall -> q | oddGnomon n

old support + q | oddGnomon n
  -> q divides old point and displacement
  -> q divides successor point
  -> q belongs to successor bounded support
```

Then prove the finite-set identity, orientation-adjusted as needed:

```lean
squareOffsetPrimeSupport n r ∩
    squareOffsetPrimeSupport (n+1) (successorThresholdInsert n r)
  =
(squareOffsetPrimeSupport n r).filter
  (fun q => q ∣ DkMath.Gnomon.oddGnomon n)
```

Do not replace the exact equality by only a subset theorem unless Lean/API friction makes the reverse direction genuinely blocked.

---

## 3. Upper-region exact intersection

For `n+1 ≤ r`, prove the analogous exact result with displacement `2*(n+1)`:

```lean
theorem mem_reindexed_primeSupport_inter_upper_iff
    {n r q : ℕ}
    (hr : SquareOffset n r)
    (hupp : n + 1 ≤ r) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1)
          (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧
        q ∣ 2 * (n + 1)
```

and the corresponding Finset equality with a divisibility filter.

---

## 4. Prime-threshold collapse of the upper channel

Under:

```text
Nat.Prime (n+1)
```

an old prime `q ≤ n` dividing `2*(n+1)` can only be `2`.

Prove a small reusable theorem such as:

```lean
theorem oldPrime_dvd_two_mul_succ_iff_eq_two
    {n q : ℕ}
    (hsucc : Nat.Prime (n + 1))
    (hq : Nat.Prime q)
    (hqle : q ≤ n) :
    q ∣ 2 * (n + 1) ↔ q = 2
```

or an implication if the reverse direction needs a harmless side condition.  Prefer the exact iff if it is true as stated.

Use it to sharpen the upper support intersection to an exact `q = 2` filter under a prime threshold:

```text
old support ∩ successor support
=
old support filtered by (q = 2).
```

A singleton-intersection form is also acceptable if cleaner.

---

## 5. Lower disjointness when the unit gnomon is fresh prime

Prove the structural corollary:

```text
Nat.Prime (oddGnomon n)
-> Disjoint
     (squareOffsetPrimeSupport n r)
     (squareOffsetPrimeSupport (n+1)
       (successorThresholdInsert n r))
```

for lower-region `r`.

Reason:

```text
q in old support -> q ≤ n
q divides oddGnomon n
oddGnomon n = 2*n+1 > n
oddGnomon n prime
```

so no old prime can divide the gnomon.

Do not assume `oddGnomon n` is prime globally; this is a conditional theorem.

Also consider the more general source theorem:

```text
SupportDisjointFrom (primeScalesUpTo n) (oddGnomon n)
-> reindexed supports are Disjoint
```

if it is easy and avoids baking primality into the main API.  The prime corollary can then specialize it.

---

## 6. Upper disjointness after removing parity channel

Under `Nat.Prime (n+1)`, the only possible persistent old prime in the upper region is `2`.

Prove a corollary of the form:

```text
¬ 2 ∣ n^2 + r
-> Disjoint oldSupport successorSupport
```

for upper-region `r` and prime threshold `n+1`.

An equivalent odd-point assumption is acceptable if already available in the repository and avoids duplicate parity vocabulary.

Do **not** import the entire parity-safe capacity stack merely to prove this elementary corollary.

---

## 7. Required `30 -> 31` regressions

Kernel-check the exact support-turnover consequences.

### Lower half

For every old seat `r` with:

```text
SquareOffset 30 r
r < 31
```

prove the old and successor prime-support sets are disjoint.

This should use:

```text
oddGnomon 30 = 61
Nat.Prime 61
```

not brute-force enumeration of every support set.

### Upper half

For:

```text
31 ≤ r
SquareOffset 30 r
```

prove any common prime-support member is `2`.

Preferred membership theorem:

```text
q ∈ oldSupport ∩ successorSupport -> q = 2
```

Optionally add the exact finite-set filter by `q = 2` if already obtained generically.

Do not claim upper support is always nonempty or always `{2}`; it depends on the parity of the actual point.

---

## 8. Audit against the current full-cover frontier

After implementing the exact support intersection, inspect—but do not yet modify—the current frontier/capacity modules and answer:

1. Does the new adjacent-shell intersection theorem already occur in equivalent form elsewhere?
2. Does it immediately imply `¬ SquareOffsetsFullyCovered n` for any general `n`? Expected: no.
3. Under simultaneous full cover of `n` and `n+1`, does it force a meaningful lower bound on support turnover / incidence that is not already in the parity-safe ledger?
4. Is there a single bounded next target for LGF-001?

Potential LGF-001 only if justified:

```text
a two-shell incidence / turnover ledger that charges
persistent support only to prime divisors of oddGnomon n and to 2.
```

Do not create LGF-001 merely because the theorem is aesthetically interesting.

---

## 9. Outcome policy

Use one of:

```text
A — EXACT TURNOVER LAW ESTABLISHED
    Lower and upper support intersections are exact displacement filters;
    prime-threshold upper channel collapses to 2; useful disjointness
    corollaries are obtained.

B — FIREWALL SUBSET ONLY
    Only one-way restrictions can be proved; exact reverse membership is
    blocked. Record the exact obstruction.

C — ALREADY SUBSUMED / NO NEW APPLICATION INFORMATION
    Existing production theorems already give the same support-intersection
    statement at the same semantic level.
```

Outcome A still does not imply Legendre.

---

## 10. Validation

Run focused builds:

```text
lake build DkMath.NumberTheory.Legendre.GnomonSupportTurnover
lake build DkMath.NumberTheory.Legendre
```

and:

```text
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
```

Create:

```text
docs/dev/NumberTheory-Legendre-GnomonFirewall-260915-v0/report-000.md
```

Report theorem inventory, exact vs one-way results, 30→31 regressions, overlap with existing modules, and whether LGF-001 is justified.
