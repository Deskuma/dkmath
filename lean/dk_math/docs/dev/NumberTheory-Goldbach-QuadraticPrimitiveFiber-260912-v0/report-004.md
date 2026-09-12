# QP-004 — oriented CRT and actual interval geometry

Predecessor: QP-003 commit `57d72d21d`.

## Kernel-checked geometry

`orientedResidue n p q u` means `u=+n mod p`, `u=-n mod q`.
`oriented_iff_raw` uses the existing production left/right congruence theorems
and requires `u≤n` for natural subtraction.
`oriented_crt` constructs the unique representative in `[0,p*q)` as
`Nat.chineseRemainder hc n (-(n : ZMod q)).val`. Only nonzero coprime moduli
are needed. Computationally its value is
`(n + p*((-2*n*inverse(p,q)) mod q)) mod (p*q)`.

`oriented_modEq` proves any two seats in that orientation are equal modulo
`p*q`. `oriented_spacing` yields spacing at least `p*q`.
`oriented_at_most_one` applies to the actual interval when `n-1≤p*q`.
`oriented_parity_spacing` adds modulus two and yields `2*p*q` for odd p,q.
These conclusions apply also to proper obstructions because they are subsets
of raw waves; endpoint exceptions can delete occupancies.

The reverse orientation is the negative residue modulo `p*q`.
`orientations_exclusive` proves disjointness whenever even one of the two
moduli does not divide `2*n`; the reduced prime world satisfies this.
For distinct odd primes the two residues coincide exactly when both divide n
(the converse/combined iff is an elementary coordinate calculation, numerically
checked in the script, not a separately named Lean theorem here).

## Normalization period and counts

One must not count primitive/parity membership as a predicate on residues
modulo odd `p*q`: adding `p*q` flips parity and can change gcd(n,u).
A kernel regression uses n=34, p=3,q=5, offsets 1 and 16 to show the issue.
The script uses the valid full period `2*n*p*q`. For reduced odd primes the
CRT permutation of the `2*n` lifts gives `phi(2*n)` normalized residues per
orientation, and hence twice that for the two orientations; if either prime
divides n the normalized occupancy is zero. This count is an arithmetic
derivation and a finite numerical check, **not a kernel-checked universal
cardinality theorem in this scratch file**. It is not a short-fiber count.

Executed scan: centers 0..500, 21,192 oriented interval tests; 120 full-period
orientation tests restricted to centers 2..40. `numeric/qp-004-waves.json`
retains the wave diagnostics. All CRT, spacing, and full-period count checks
passed. The full-period scan uses raw congruences, never truncated natural
subtraction beyond the admissible interval.

- First normalized raw LR endpoint exception: n=13, p=5,q=3,u=8 (5,21).
  The raw seat is absent from proper LR occupancy because its left endpoint
  equals five. This also illustrates occupied at-most-one geometry.
- First repeated normalized orientation: n=34,p=3,q=5,u=1,31.
- `sharp_spacing_regression`: n=47,p=3,q=5,u=8,38, both **proper**, with
  endpoints (39,55) and (9,85). The `2*p*q` spacing is sharp.
- `cardinality_not_width_regression`: n=50 has 19 normalized candidates,
  fewer than 7*3=21, but its orientation p=7,q=3 contains u=1,43.
  The second seat has an endpoint exception. Thus compressed candidate
  cardinality cannot replace geometric width in even a raw occupancy claim.

## Information audit

These are useful explicit scratch corollaries, but the arithmetic content is
already contained in production `goldbach_primeWorld_crt` and the CRT bijection
inside `goldbach_card_primeWorld`. The latter proof explicitly uses injectivity
of residue coordinates and bounded representatives. Adding prime two is the
existing parity coordinate. No stronger information follows just from the
numerical value of the full-period count; the **underlying bijection**, rather
than its cardinality alone, supplies spacing. Endpoint exceptions are already
present in the production proper ledger. No new short-fiber survival estimate
has resulted.

Validation: focused scratch `lake build` exited 0 (8692 jobs, 7.7 seconds).
Python command was the QP-002 command with `--select 5,31,35` and JSON output
`/tmp/qp-004-full.json`; its `waves` member was saved as the committed snapshot.
A draft regression mistakenly used center 16 instead of 34; kernel `decide`
rejected it, and the corrected congruence example passed. A Decidable instance
was added for the scratch oriented observer. `git diff --check` passed.
