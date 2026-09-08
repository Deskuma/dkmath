# instruction-015 — LUNA primitive Pell support packet

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-015**.

LUNA-014 froze the exact square-cube and fixed-Pell-parameter coordinates:

~~~text
M = u^2 * r^3

r = oddPart M
u = evenPart M / oddPart M

T = r*S
Squarefree T

(2*a+3)^2 + 3 = 4*T*d^2
d = evenPart M.
~~~

The next deterministic step is to freeze the **primitive support arithmetic**
carried by these coordinates:

- divisibility between r, u, d, and M,
- prime support congruence q == 1 mod 3,
- coprimality of the Pell y-coordinate with the repeated modulus,
- coprimality inherited by r, d, and u,
- the fact that any common divisor of y and T divides 3,
- and the exact square divisibility d^2 | y^2+3.

These are exact arithmetic facts.

Do **not** count Pell solutions and do **not** estimate any shell/fiber
cardinality.

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
report-014.md
report-013.md
report-012.md
report-011.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicSquarefulPell.lean
DkMath/ABC/GNExcessCubicComplementIncidence.lean
DkMath/ABC/GNExcessCubicRealizedModuli.lean
~~~

Treat current production Lean as authoritative.

---

## Reporting policy

Do **not** include branch HEAD hashes or commit hashes in report-015.md.

Report exact declarations, proof dependencies, verification, and the remaining
research boundary.

---

# Part I — divisibility hierarchy of squareful coordinates

Add a focused production module.

Recommended file:

~~~text
DkMath/ABC/GNExcessCubicPrimitivePell.lean
~~~

For nonzero squareful M, prove the canonical divisibility relations implied by

~~~text
d = evenPart M
r = oddPart M
u = GNExcessCubicSquarefulQuotient M
d = r*u
M = u^2*r^3.
~~~

At minimum expose:

~~~text
oddPart M divides evenPart M

GNExcessCubicSquarefulQuotient M divides evenPart M

evenPart M divides M

oddPart M divides M

GNExcessCubicSquarefulQuotient M divides M.
~~~

Recommended theorem names may follow the pattern:

~~~text
GNExcessCubicSquarefulQuotient_dvd_evenPart
evenPart_dvd_of_squarefull
GNExcessCubicSquarefulQuotient_dvd_of_squarefull
~~~

Reuse LUNA-013 / LUNA-014 identities.

Do not redo factorization arithmetic.

---

# Part II — prime support of r, d, and u is one modulo three

For a realized modulus

~~~text
M in GNExcessCubicRealizedLargeModulusSpace X,
~~~

the production theorem already gives:

~~~text
prime q divides M -> q % 3 = 1.
~~~

Use Part I to derive the coordinate consumers:

~~~text
prime q divides oddPart M
  -> q % 3 = 1

prime q divides evenPart M
  -> q % 3 = 1

prime q divides GNExcessCubicSquarefulQuotient M
  -> q % 3 = 1.
~~~

Recommended names:

~~~text
GNExcessCubicRealizedLargeModulusSpace_oddPart_prime_mod_three_eq_one
GNExcessCubicRealizedLargeModulusSpace_evenPart_prime_mod_three_eq_one
GNExcessCubicRealizedLargeModulusSpace_squarefulQuotient_prime_mod_three_eq_one
~~~

These should be short divisibility consumers of
GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one.

As cheap corollaries, if useful, prove:

~~~text
not 2 divides M
not 3 divides M

not 3 divides oddPart M
not 3 divides evenPart M
not 3 divides quotient M.
~~~

Do not spend excessive engineering effort on the numeral corollaries.

The prime-support theorems have priority.

---

# Part III — canonical Pell y-coordinate is coprime to M

This is the first main LUNA-015 theorem.

For a represented shell witness a, write

~~~text
M := GNExcessCubicFullRepeatedModulus a
y := 2*a + 3.
~~~

Prove:

~~~text
Nat.Coprime y M.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_coprime_pellY_modulus
~~~

A preferred proof is prime-divisor contradiction.

If a prime q divides both y and M:

1. q divides M, so q % 3 = 1;
2. M divides F(a) through the canonical product
   M*S = F(a), so q divides F(a);
3. the discriminant identity gives
   y^2 + 3 = 4*F(a);
4. q divides y^2 and y^2+3, hence q divides 3;
5. primality forces q = 3;
6. but q % 3 = 1 is impossible.

Use standard Nat.Coprime / prime-divisor API.

Do not use numerical decision procedures.

If a direct gcd proof is shorter, it is acceptable.

---

# Part IV — inherited coprimality with r, d, and u

For the same represented shell witness and M, derive:

~~~text
Nat.Coprime y (oddPart M)

Nat.Coprime y (evenPart M)

Nat.Coprime y (GNExcessCubicSquarefulQuotient M).
~~~

Recommended theorem packet:

~~~text
GNExcessCubicRealizedLargeModulusShellWitness_pellY_coordinate_coprime_packet
~~~

or individual theorem names.

These should follow from Part III and the divisibility relations in Part I.

Do not re-run the prime contradiction three times.

---

# Part V — complement is coprime to r and u

LUNA-013 already froze

~~~text
Coprime r S.
~~~

Add the quotient consumer:

~~~text
Nat.Coprime (GNExcessCubicSquarefulQuotient M) S.
~~~

and, if not already easy to consume:

~~~text
Nat.Coprime (evenPart M) S.
~~~

for a represented incidence pair (M,S).

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_squareCube_coprime_packet
~~~

Reason: r, d, and u divide M, while production LUNA-012 gives Coprime M S.

This is deterministic inheritance.

---

# Part VI — any common divisor of y and T divides 3

This is the second main theorem.

For a represented incidence pair with unique witness a, put:

~~~text
y := 2*a+3
T := oddPart M * S.
~~~

Prove the exact gcd statement:

~~~text
Nat.gcd y T divides 3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_dvd_three
~~~

A direct divisibility proof is preferred.

Let g = gcd y T.

- g divides y, hence g divides y^2;
- T divides M*S = F(a), because oddPart M divides M;
- therefore g divides F(a);
- discriminant identity gives y^2+3 = 4*F(a);
- hence g divides y^2+3;
- subtract the y^2 divisibility to conclude g divides 3.

This theorem captures the precise primitive boundary:

~~~text
y and T are coprime away from the exceptional prime 3.
~~~

Do not claim they are always coprime.

The Pell family with complement 3 is exactly why the factor 3 must remain.

---

# Part VII — optional exact gcd classification

Only if it is very short after Part VI, prove:

~~~text
Nat.gcd y T = 1 or Nat.gcd y T = 3.
~~~

This follows from gcd y T dividing 3 and positivity.

Recommended theorem:

~~~text
..._gcd_pellY_pellParameter_eq_one_or_three
~~~

This is optional.

Do not spend time proving an iff classification involving a mod 3 condition
unless it is immediate.

---

# Part VIII — exact square divisibility in the Pell equation

For a represented incidence pair with witness a and

~~~text
d := evenPart M,
~~~

prove:

~~~text
d^2 divides (2*a+3)^2 + 3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue
~~~

This is immediate from the production identity

~~~text
(2*a+3)^2 + 3 = 4*T*d^2.
~~~

Also expose the quotient version if cheap:

~~~text
(GNExcessCubicSquarefulQuotient M)^2
  divides (2*a+3)^2 + 3.
~~~

because quotient M divides d.

Do not derive a density estimate from this square divisibility.

---

# Part IX — prime-square root condition for the d-support

For a represented pair and a prime q with

~~~text
q divides evenPart M,
~~~

derive:

~~~text
q^2 divides (2*a+3)^2 + 3
~~~

and:

~~~text
q % 3 = 1.
~~~

Recommended theorem packet:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_prime_packet
~~~

A compact conjunction theorem is acceptable:

~~~text
q % 3 = 1 and q^2 divides y^2+3.
~~~

This gives the exact local root condition carried by every prime in d.

Important:

Do not interpret this as a rarity statement.

Hensel lifting permits arbitrarily deep local roots; that route is already
closed.

This theorem only freezes the local support condition.

---

# Part X — quotient-prime packet

If cheap, repeat the same inherited statement for

~~~text
q divides GNExcessCubicSquarefulQuotient M.
~~~

Since quotient divides evenPart M, derive:

~~~text
q % 3 = 1
q^2 divides y^2+3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefulQuotient_prime_packet
~~~

This is optional if Part IX plus the quotient-divides-evenPart theorem is
already convenient enough for consumers.

---

# Part XI — fixed-T fiber primitive conic packet

For:

~~~text
a in GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T,
~~~

package the stable fixed-T facts:

~~~text
M = FullRepeatedModulus a
d = evenPart M
u = SquarefulQuotient M
y = 2*a+3

0 < d
0 < u

y^2 + 3 = 4*T*d^2

Coprime y d
Coprime y u

gcd y T divides 3

d^2 divides y^2+3

every prime q dividing d satisfies
  q % 3 = 1
  and q^2 divides y^2+3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet
~~~

A conjunction theorem or small structure is acceptable.

Do not include any counting statement.

---

# Part XII — optional integer Pell form

If the integer form was not added in LUNA-013 and is now cheap, expose:

~~~text
((2*a+3 : Nat) : Int)^2
  - 4*(T : Int)*(d : Int)^2
=
-3.
~~~

Recommended theorem:

~~~text
GNExcessCubicRealizedLargeModulusShellPellParameterFiber_equation_int
~~~

This is optional.

The Nat equation plus primitive packet has priority.

---

# Negative theorem boundaries

Document explicitly:

~~~text
q^2 divides y^2+3 does not imply global rarity.

Coprime y M does not bound the number of represented moduli.

gcd y T divides 3 does not by itself bound fixed-T Pell fibers.

prime q == 1 mod 3 support is an exact local condition, not an incidence
estimate.
~~~

Do not reopen the Hensel-to-density route.

---

# What LUNA-015 is NOT

Do not attempt:

- Pell solution counting,
- Hensel rarity,
- shell count bounds,
- fiber count bounds,
- fixed-T multiplicity bounds,
- dyadic incidence sparsity,
- paired relative-height exclusion,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce provider classes or unproved hypotheses.

This checkpoint freezes primitive local arithmetic only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicPellParameterIncidence
~~~

unless dependency order requires a nearby placement.

Do not reorder unrelated imports.

---

## Verification

At minimum run:

~~~text
lake build DkMath.ABC.GNExcessCubicPrimitivePell
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

- divisibility hierarchy,
- coordinate prime-mod-three consumers,
- Coprime y M,
- inherited y-coordinate coprimality packet,
- square-cube/complement coprimality packet,
- gcd(y,T) divides 3,
- d^2 divisibility,
- d-support prime packet,
- fixed-T primitive packet.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-015.md
~~~

Title:

~~~text
# LUNA-015 — primitive Pell support packet
~~~

Do **not** include branch HEAD hashes or commit hashes.

Report:

1. files changed,
2. squareful divisibility hierarchy,
3. r/d/u prime-support congruence,
4. Coprime y M theorem,
5. inherited Coprime y r/d/u packet,
6. complement coprimality with d/u,
7. gcd(y,T) divides 3,
8. optional gcd classification status,
9. d^2 divisibility theorem,
10. prime-square root packet,
11. quotient-prime packet status,
12. fixed-T primitive conic packet,
13. optional integer equation status,
14. focused build,
15. ABC aggregator build,
16. no-placeholder / no-new-axiom result,
17. axiom audit,
18. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when every fixed-T shell witness has a production primitive packet
showing:

~~~text
y^2 + 3 = 4*T*d^2

Coprime y d
Coprime y u

gcd y T divides 3

d^2 divides y^2+3

and every prime q dividing d satisfies

  q % 3 = 1
  q^2 divides y^2+3.
~~~

Do not count such solutions.

After LUNA-015, future research can start directly from a fully normalized
negative-Pell/conic problem with all exceptional-prime and support data
already frozen in Lean.

That normalization, not a sparsity theorem, is the entire purpose of this
checkpoint.
