# instruction-016 — LUNA exceptional-three sector normalization

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-016**.

LUNA-015 froze the primitive Pell support packet:

~~~text
y = 2*a+3

T = oddPart M * S

y^2 + 3 = 4*T*d^2

Coprime y d

gcd(y,T) divides 3.
~~~

The remaining local ambiguity is now exactly the exceptional prime 3.

LUNA-016 should freeze that ambiguity completely by splitting the canonical
fixed-T conic into two exact sectors:

~~~text
non-three sector:
  3 does not divide a
  gcd(y,T) = 1

three sector:
  3 divides a
  gcd(y,T) = 3
~~~

and by normalizing the three sector after dividing its forced factor of 3.

No counting, density, or incidence estimate is part of this checkpoint.

---

## Repository

~~~text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
campaign:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
~~~

Read first:

~~~text
report-015.md
report-014.md
report-013.md
report-008.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicPrimitivePell.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessCubicComplementPell.lean
~~~

Treat current production Lean as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-016.md.

Report exact arithmetic declarations, verification, and the remaining research
boundary.

---

# Part I — cubic quadratic modulo three

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicThreeSector.lean
~~~

Freeze the elementary equivalence for

~~~text
F(a) = a^2 + 3*a + 3.
~~~

Prove:

~~~text
3 divides F(a) iff 3 divides a.
~~~

Recommended theorem:

~~~lean
three_dvd_cubicQuadratic_iff
~~~

Use direct modular arithmetic or divisibility arithmetic.

Do not use computational search.

Also expose, if useful:

~~~text
3 divides (2*a+3) iff 3 divides a.
~~~

Recommended theorem:

~~~lean
three_dvd_pellY_iff
~~~

This should be elementary.

---

# Part II — exact 3-adic depth of F(a)

LUNA-008 already proves:

~~~text
not 9 divides F(a).
~~~

Combine it with Part I.

For 3 | a, prove:

~~~text
3 divides F(a)
not 9 divides F(a).
~~~

Recommended theorem:

~~~lean
cubicQuadratic_three_exact_depth_one
~~~

A valuation theorem is optional.  A simple divisibility packet is enough.

Do not introduce general p-adic machinery.

---

# Part III — realized modulus is prime-to-three

For every realized large modulus M, prove:

~~~text
Nat.Coprime M 3
~~~

or equivalently:

~~~text
not 3 divides M.
~~~

Recommended theorem names:

~~~lean
GNExcessCubicRealizedLargeModulusSpace_not_three_dvd
GNExcessCubicRealizedLargeModulusSpace_coprime_three
~~~

This follows immediately from the production prime-support theorem:

~~~text
prime q divides M -> q % 3 = 1.
~~~

Do not redo factorization.

Also derive, if useful:

~~~text
not 3 divides oddPart M
not 3 divides evenPart M
not 3 divides squarefulQuotient M.
~~~

These are short coordinate consumers and may live in the same module.

---

# Part IV — complement carries the entire factor 3

For a canonical shell witness a, let

~~~text
M := FullRepeatedModulus a
S := GNExcessCubicComplement a.
~~~

Production gives:

~~~text
M*S = F(a)
Coprime M S.
~~~

Using Part III, prove the exact equivalence:

~~~text
3 divides S iff 3 divides a.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_complement_iff
~~~

Proof:

~~~text
3 | S -> 3 | M*S = F(a) -> 3 | a

3 | a -> 3 | F(a) = M*S
and 3 does not divide M
-> Euclid gives 3 | S.
~~~

Also prove:

~~~text
not 9 divides S.
~~~

This follows because S divides F(a), or from squarefree S.

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitness_not_nine_dvd_complement
~~~

The exact-depth-one interpretation of the exceptional factor should be
documented.

---

# Part V — Pell parameter carries factor 3 exactly with the complement

For a represented pair (M,S), recall:

~~~text
T = oddPart M * S.
~~~

Since 3 does not divide oddPart M, prove:

~~~text
3 divides T iff 3 divides S.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePair_three_dvd_pellParameter_iff
~~~

Then combine with Part IV to obtain the witness form:

~~~text
3 divides T iff 3 divides a.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellWitness_three_dvd_pellParameter_iff
~~~

Be explicit about which T expression is used:

~~~text
oddPart M * S
~~~

or the fixed PellParameterFiber coordinate.

---

# Part VI — exact gcd classification

LUNA-015 proves:

~~~text
gcd(y,T) divides 3.
~~~

Promote the exact classification:

~~~text
gcd(y,T) = 1 or gcd(y,T) = 3.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_eq_one_or_three
~~~

Then prove the sharp sector theorem:

~~~text
gcd(y,T) = 3 iff 3 divides a
~~~

and equivalently:

~~~text
gcd(y,T) = 3 iff 3 divides S
gcd(y,T) = 3 iff 3 divides T.
~~~

Recommended theorem family:

~~~lean
..._gcd_eq_three_iff_three_dvd_witness
..._gcd_eq_three_iff_three_dvd_complement
..._gcd_eq_three_iff_three_dvd_pellParameter
~~~

The proof should use:

- gcd divides 3,
- positivity of gcd,
- Part I / IV / V,
- gcd divisibility iff common divisibility.

Do not classify by a numerical residue table beyond what is necessary.

---

# Part VII — non-three primitive sector

For a fixed-T fiber witness a with:

~~~text
not 3 divides a,
~~~

prove the packet:

~~~text
not 3 divides y
not 3 divides T
Nat.gcd y T = 1
Nat.Coprime y T

y^2 + 3 = 4*T*d^2

Coprime y d
Coprime T d
~~~

The final Coprime T d should be proved only if it follows cleanly from existing
facts.

Check carefully:

~~~text
T = r*S
d = r*u
~~~

so r divides both T and d.

Therefore T and d are **not** generally coprime.

Do not assert false coprimality.

The required packet should instead keep the known true facts:

~~~text
Coprime y d
Nat.Coprime y T
Squarefree T
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet
~~~

This is the clean fully primitive y-versus-T sector.

---

# Part VIII — three-sector quotient coordinates

For a fixed-T fiber witness with:

~~~text
3 divides a,
~~~

define or expose the exact quotients:

~~~text
y3 := (2*a+3) / 3
S3 := S / 3
T3 := T / 3.
~~~

Use ordinary Nat division only after proving divisibility.

Definitions may be local lets or named functions.

Recommended named helpers, if useful:

~~~lean
GNExcessCubicThreeSectorY
GNExcessCubicThreeSectorComplement
GNExcessCubicThreeSectorPellParameter
~~~

Do not add definitions unless they materially improve consumers.

---

# Part IX — three-sector reconstruction

Prove the exact reconstruction:

~~~text
2*a+3 = 3*y3

S = 3*S3

T = 3*T3.
~~~

Also prove:

~~~text
not 3 divides S3
not 3 divides T3.
~~~

Why:

- S is squarefree,
- 3 divides S exactly once,
- oddPart M is prime-to-three,
- T = oddPart M*S.

If convenient, prove:

~~~text
Squarefree S3
Squarefree T3.
~~~

These are useful and should follow from squarefree divisors.

---

# Part X — normalized three-sector conic

This is the main LUNA-016 theorem.

Start from:

~~~text
y^2 + 3 = 4*T*d^2

y = 3*y3
T = 3*T3.
~~~

Derive the exact natural equation:

~~~text
3*y3^2 + 1 = 4*T3*d^2.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_equation
~~~

This is the correctly normalized exceptional-three conic.

Do not incorrectly divide the original equation by 9.

Only the common factor 3 is removed from the whole equation:

~~~text
9*y3^2 + 3 = 12*T3*d^2
=> 3*y3^2 + 1 = 4*T3*d^2.
~~~

Use exact Nat arithmetic.

---

# Part XI — normalized three-sector primitive gcd

Prove, if clean:

~~~text
Nat.Coprime y3 T3.
~~~

This should follow from:

~~~text
gcd(y,T) = 3
y = 3*y3
T = 3*T3
~~~

after cancelling the common factor 3.

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_coprime
~~~

If Mathlib cancellation API makes this awkward, it is acceptable to prove by
prime-divisor contradiction.

This theorem has high value because it shows the exceptional sector becomes
fully primitive after the forced 3 is stripped.

Also inherit:

~~~text
Nat.Coprime y3 d
~~~

from Coprime y d and y3 | y.

Do not claim Coprime T3 d.

---

# Part XII — two-sector normal-form packet

Expose one theorem that classifies every fixed-T fiber witness into exactly one
of two normal forms.

Conceptually:

~~~text
either

  not 3 divides a
  Nat.Coprime y T
  y^2 + 3 = 4*T*d^2

or

  3 divides a
  y = 3*y3
  T = 3*T3
  Nat.Coprime y3 T3
  3*y3^2 + 1 = 4*T3*d^2.
~~~

Recommended theorem:

~~~lean
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_cases
~~~

The result may be a disjunction with existential y3,T3 in the second branch.

This is a normalization theorem only.

---

# Part XIII — sector finite sets

If clean, define:

~~~text
nonThreePellParameterFiber X D T
threePellParameterFiber X D T
~~~

by filtering the existing fixed-T fiber with:

~~~text
not 3 divides a
3 divides a.
~~~

Then prove exact partition:

~~~text
fixedTFiber
=
nonThreeSector disjoint union threeSector.
~~~

And card identity:

~~~text
fiber.card
=
nonThree.card + three.card.
~~~

This is optional.

The arithmetic sector theorems have priority.

Do not estimate either sector.

---

# Negative theorem boundaries

Document explicitly:

~~~text
The three-sector split is a normalization, not a sparsity theorem.

The non-three sector being primitive does not bound its solution count.

The normalized equation
  3*y3^2 + 1 = 4*T3*d^2
is not claimed to have few solutions.

No Hensel rarity or Pell rarity follows from the sector split alone.
~~~

---

# What LUNA-016 is NOT

Do not attempt:

- Pell/conic solution counting,
- sector cardinality bounds,
- shell/fiber sparsity,
- Hensel density,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce provider classes or unproved hypotheses.

This checkpoint freezes the exceptional-prime normalization only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicPrimitivePell
~~~

unless dependency order requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~text
lake build DkMath.ABC.GNExcessCubicThreeSector
lake build DkMath.ABC
~~~

Scan changed Lean files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit axioms for:

- three_dvd_cubicQuadratic_iff,
- complement factor-three equivalence,
- Pell-parameter factor-three equivalence,
- exact gcd classification,
- gcd=3 sector equivalences,
- normalized three-sector reconstruction,
- normalized three-sector equation,
- normalized coprimality,
- two-sector normal form.

Expected trust boundary:

~~~text
propext
Classical.choice
Quot.sound
~~~

or a subset.

---

## Deliverable

Create:

~~~text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-016.md
~~~

Title:

~~~text
# LUNA-016 — exceptional-three sector normalization
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. cubic quadratic mod-three equivalence,
3. exact depth-one factor 3,
4. realized modulus prime-to-three theorem,
5. complement factor-three equivalence,
6. Pell-parameter factor-three equivalence,
7. exact gcd classification,
8. non-three primitive packet,
9. three-sector quotient reconstruction,
10. squarefree / prime-to-three quotient support,
11. normalized three-sector conic equation,
12. normalized coprimality,
13. two-sector normal form,
14. optional sector finite-set partition status,
15. focused build,
16. ABC aggregator build,
17. no-placeholder / no-new-axiom result,
18. axiom audit,
19. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the exceptional gcd boundary from LUNA-015 has been completely
resolved into two exact production normal forms:

~~~text
Sector A:
  3 does not divide a
  gcd(y,T) = 1
  Coprime y T
  y^2 + 3 = 4*T*d^2.

Sector B:
  3 divides a
  y = 3*y3
  T = 3*T3
  Coprime y3 T3
  3*y3^2 + 1 = 4*T3*d^2.
~~~

Do not count either sector.

After LUNA-016, the primitive conic frontier will have no unresolved
exceptional-prime ambiguity: the prime 3 is either absent or factored out
exactly.

That normalization, and nothing asymptotic, is the purpose of this checkpoint.
