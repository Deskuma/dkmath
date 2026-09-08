# instruction-019 — LUNA paired squareful / square-cube ledger

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-019**.

LUNA-018 froze the paired factorization

~~~text
F = MF*SF
G = MG*SG

Squarefree SF
Squarefree SG

Coprime MF SF
Coprime MG SG
Coprime MF MG

gcd(F,G) divides 7
~~~

and the exact product coupling

~~~text
(MF*SF)*(MG*SG) = 3*(a+1)^4 + a^2.
~~~

The optional squarefull strengthening was deliberately deferred.

LUNA-019 should now freeze that strengthening and place both repeated
coordinates into the same canonical square-cube system already used on the
forward side in LUNA-013/LUNA-014.

No relative-height theorem, counting theorem, density theorem, or ABC closure
is part of this checkpoint.

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
report-018.md
report-017.md
report-015.md
report-014.md
~~~

Inspect:

~~~text
DkMath/ABC/GNExcessCubicPairedOrientation.lean
DkMath/ABC/GNExcessCubicPellParameterIncidence.lean
DkMath/ABC/GNExcessCubicSquarefulPell.lean
DkMath/ABC/GNExcessCubicComplement.lean
~~~

Treat current production Lean as authoritative.

Do not record branch HEAD or commit hashes in report-019.md.

---

## Part I — generic repeatedPrimePowerPart is squarefull

Add a focused production module:

~~~text
DkMath/ABC/GNExcessCubicPairedSquareful.lean
~~~

Before adding a generic theorem, search current production for an equivalent
statement.

If absent, prove:

~~~text
repeatedPrimePowerPart n is squarefull.
~~~

Recommended:

~~~lean
repeatedPrimePowerPart_squarefull (n : ℕ) :
  squarefull (repeatedPrimePowerPart n)
~~~

or a theorem with n != 0 if required by the existing predicate/API.

The intended proof is direct from the definition:

~~~text
every prime in repeatedPrimePowerPart occurs with exponent at least 2.
~~~

Reuse the production theorem:

~~~text
prime_sq_dvd_repeatedPrimePowerPart
~~~

if it already has the right direction.

Do not rebuild factorization machinery unnecessarily.

---

## Part II — both paired repeated parts are squarefull

Using the forward and swap full-repeated identities, prove:

~~~text
squarefull (GNCubicForwardRepeatedPart a)

squarefull (GNCubicSwapRepeatedPart a).
~~~

Recommended:

~~~lean
GNCubicForwardRepeatedPart_squarefull
GNCubicSwapRepeatedPart_squarefull
~~~

The forward theorem should consume the existing LUNA-008 full-repeated
identity.

The swap theorem should consume the LUNA-018 swap full-repeated identity.

Do not duplicate the repeated-prime-power proof.

---

## Part III — positivity and nonzero packets

For all a, both orientation values are positive, hence their repeated parts are
positive.

Expose:

~~~text
0 < MF
0 < MG.
~~~

Recommended:

~~~lean
GNCubicForwardRepeatedPart_pos
GNCubicSwapRepeatedPart_pos
~~~

Use existing positivity of repeatedPrimePowerPart or GN repeated-part API.

These facts are needed by the square-cube consumer.

---

## Part IV — canonical square-cube coordinates on both sides

Reuse the LUNA-014 definitions:

~~~text
GNExcessCubicSquarefulQuotient M
oddPart M
evenPart M.
~~~

For MF and MG define only lightweight semantic abbreviations if useful:

~~~text
rF := oddPart MF
uF := GNExcessCubicSquarefulQuotient MF

rG := oddPart MG
uG := GNExcessCubicSquarefulQuotient MG.
~~~

Do not create new public definitions unless they materially improve readability.

Prove the two exact identities:

~~~text
MF = uF^2 * rF^3

MG = uG^2 * rG^3.
~~~

Recommended theorem packet:

~~~lean
GNCubicPairedRepeatedParts_squareCube_packet
~~~

It should also expose:

~~~text
Squarefree rF
Squarefree rG

0 < rF
0 < rG

0 < uF
0 < uG.
~~~

Use generic squareful square-cube theorems already productionized.

For the swap side, use the generic squareful identity rather than forcing it
through the realized-modulus-space API.

No new root functions.

---

## Part V — repeated-product squarefull theorem

This is the first main LUNA-019 theorem.

Prove:

~~~text
squarefull (MF * MG).
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_squarefull
~~~

A generic helper is acceptable:

~~~text
squarefull x -> squarefull y -> squarefull (x*y)
~~~

only if an equivalent Mathlib theorem is absent.

Coprimality is not required for squarefullness, though the existing paired
coprimality may simplify consumers.

Do not confuse squarefull with squarefree.

---

## Part VI — exact square-cube form of the repeated product

From:

~~~text
MF = uF^2*rF^3
MG = uG^2*rG^3
~~~

derive:

~~~text
MF*MG
=
(uF*uG)^2 * (rF*rG)^3.
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_squareCube_identity
~~~

Because MF and MG are coprime, also prove:

~~~text
Nat.Coprime rF rG

Nat.Coprime uF uG.
~~~

Recommended packet:

~~~lean
GNCubicPaired_squareCube_cross_coprime_packet
~~~

Each coordinate divides its repeated modulus, so coprimality should be inherited
from the paired repeated-part coprimality.

Do not re-run prime-support arguments.

---

## Part VII — squarefreeness of the combined cube-core

Use:

~~~text
Squarefree rF
Squarefree rG
Coprime rF rG
~~~

to prove:

~~~text
Squarefree (rF*rG).
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_oddPartProduct_squarefree
~~~

This is the canonical squarefree cube-core of the paired repeated product.

Do not claim that oddPart(MF*MG) = rF*rG unless it is a short consequence of
existing factorization API.

That equality is optional.

---

## Part VIII — optional oddPart/evenPart multiplicativity

Because MF and MG are coprime, it may be useful to prove:

~~~text
oddPart (MF*MG) = oddPart MF * oddPart MG

evenPart (MF*MG) = evenPart MF * evenPart MG.
~~~

This is optional.

Only add these if existing factorization API makes the proofs short and robust.

Do not spend significant engineering effort on multiplicativity.

The explicit square-cube identity from Part VI is sufficient.

---

## Part IX — prime support congruence for both repeated coordinates

For any prime q:

~~~text
q divides MF -> q % 3 = 1

q divides MG -> q % 3 = 1.
~~~

The forward side is already available through the canonical support machinery
or direct non-exceptional support.

The swap side should be proved analogously from:

~~~text
q divides GNNonExceptionalRepeatedPart 3 1 a
~~~

and the non-exceptional support condition.

Recommended:

~~~lean
GNCubicForwardRepeatedPart_prime_mod_three_eq_one
GNCubicSwapRepeatedPart_prime_mod_three_eq_one
~~~

If the forward theorem already exists under another name, add only a wrapper if
needed for symmetry.

Then derive:

~~~text
Nat.Prime q
q divides MF*MG
=>
q % 3 = 1.
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_prime_mod_three_eq_one
~~~

This is an exact support theorem, not a density statement.

---

## Part X — repeated-product quartic packet

Retain and consume the LUNA-018 theorem:

~~~text
MF*MG divides 3*(a+1)^4 + a^2.
~~~

Combine it with Parts V–VII:

~~~text
squarefull (MF*MG)

MF*MG
=
(uF*uG)^2 * (rF*rG)^3

Squarefree (rF*rG)

MF*MG divides 3*(a+1)^4 + a^2.
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_squareful_packet
~~~

This packet is a durable bridge from paired repeated arithmetic to the quartic
coupling.

Do not estimate the size of the divisor.

---

## Part XI — exact lower structural divisibilities

Because the repeated product is squarefull, every prime divisor q satisfies:

~~~text
q^2 divides MF*MG.
~~~

Expose:

~~~lean
GNCubicPairedRepeatedProduct_prime_sq_dvd
~~~

Then combine with the quartic divisor theorem:

~~~text
q^2 divides 3*(a+1)^4 + a^2.
~~~

Recommended:

~~~lean
GNCubicPairedRepeatedProduct_prime_sq_dvd_quartic
~~~

Again: local square divisibility only, no rarity claim.

---

## Part XII — off-seven square-cube support packet

For positive a with:

~~~text
a % 7 != 1,
~~~

LUNA-018 gives complete cross-coprimality of MF,SF,MG,SG.

Add a consumer packet combining this with the square-cube coordinates:

~~~text
MF = uF^2*rF^3
MG = uG^2*rG^3

Squarefree rF
Squarefree rG

Coprime rF rG
Coprime uF uG

all four forward/swap factor blocks are cross-coprime.
~~~

Recommended:

~~~lean
GNCubicPaired_offSeven_squareCube_packet
~~~

Do not add any size conclusion.

---

## Part XIII — seven-sector squareful boundary

For positive a with:

~~~text
a % 7 = 1,
~~~

record only:

~~~text
gcd(F,G) = 7

not (49 divides F and 49 divides G)

Coprime MF MG

squarefull MF
squarefull MG.
~~~

Recommended:

~~~lean
GNCubicPaired_sevenSector_squareful_packet
~~~

Do not classify which repeated part contains 7 in this checkpoint.

That finer 7-sector state split may be a later fact-freezing task.

---

## Part XIV — hard regression boundary

The module/report must explicitly retain:

~~~text
exists_arbitrarily_large_coprime_cubic_repeated_parts
~~~

and state:

~~~text
squarefull + coprime + exact square-cube coordinates
still do not imply either MF or MG is small relative to a.
~~~

Do not infer relative-height control from the new structure.

---

## Negative theorem boundaries

Do not claim:

~~~text
MF*MG <= (a+1)^2

one of MF,MG <= a+1

both repeated parts cannot exceed a+1

squarefull paired product is rare enough for ABC

q^2 dividing the quartic gives Hensel/density decay.
~~~

These remain research statements or unsupported shortcuts.

---

## What LUNA-019 is NOT

Do not attempt:

- paired relative-height exclusion,
- shell counts,
- squarefull-value asymptotics,
- Hensel rarity,
- Pell counting,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce providers or unproved assumptions.

This checkpoint freezes paired squarefull structure only.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicPairedOrientation
~~~

Do not reorder unrelated imports.

---

## Verification

At minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicPairedSquareful
lake build DkMath.ABC
~~~

Scan changed production files for:

~~~text
sorry
admit
new axiom
abc_main_axiom
native_decide
~~~

None may be introduced.

Audit principal declarations. Expected trust boundary:

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-019.md
~~~

Title:

~~~text
# LUNA-019 — paired squareful / square-cube ledger
~~~

Report:

1. files changed,
2. generic repeated-part squarefull theorem status,
3. forward/swap repeated squarefull theorems,
4. positivity packet,
5. paired square-cube packet,
6. repeated-product squarefull theorem,
7. repeated-product square-cube identity,
8. cross-coprimality of r/u coordinates,
9. combined cube-core squarefreeness,
10. optional odd/even multiplicativity status,
11. prime-support mod-three packet,
12. repeated-product quartic packet,
13. prime-square divisibility packet,
14. off-seven square-cube packet,
15. seven-sector squareful packet,
16. absolute-large regression boundary,
17. focused build,
18. ABC aggregator build,
19. forbidden-construct result,
20. axiom audit,
21. exact remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the paired repeated coordinates have a canonical production
square-cube ledger:

~~~text
MF = uF^2*rF^3
MG = uG^2*rG^3

Squarefree rF
Squarefree rG

Coprime MF MG
Coprime rF rG
Coprime uF uG

MF*MG
=
(uF*uG)^2 * (rF*rG)^3

Squarefree (rF*rG)

squarefull (MF*MG)

MF*MG divides 3*(a+1)^4 + a^2.
~~~

Do not infer height-relative size.

After LUNA-019, paired research can start from an exact squareful
square-cube divisor of the quartic coupling, with all support/coprimality data
already frozen.
