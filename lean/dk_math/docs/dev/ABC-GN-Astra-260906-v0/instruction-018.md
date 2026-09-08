# instruction-018 — LUNA paired-orientation exact arithmetic ledger

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-018**.

The canonical orientation is now heavily normalized through LUNA-017.
Earlier paired-orientation facts are production-proved but still distributed.

Freeze the one-parameter pair

~~~text
F(a) := GN 3 a 1 = a^2 + 3*a + 3
G(a) := GN 3 1 a = 3*a^2 + 3*a + 1
~~~

into one durable paired arithmetic ledger.

The main distinction to preserve is:

~~~text
ordinary support:
  F and G may share 7;

repeated support:
  their repeated parts are coprime.
~~~

Do not attempt any relative-height theorem or ABC closure.

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
report-017.md
report-016.md
report-007.md
report-001.md
~~~

Inspect:

~~~text
DkMath/NumberTheory/GNThreeOrientation.lean
DkMath/ABC/GNCubicOrientation.lean
DkMath/ABC/GNCubicPairedDepth.lean
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessCubicComplementPell.lean
~~~

Treat current production source as authoritative.

Do not record branch HEAD or commit hashes in report-018.md.

---

## Part I — paired value/repeated coordinates

Add:

~~~text
DkMath/ABC/GNExcessCubicPairedOrientation.lean
~~~

Optional lightweight names:

~~~lean
def GNCubicForwardValue (a : ℕ) := GN 3 a 1
def GNCubicSwapValue (a : ℕ) := GN 3 1 a

noncomputable def GNCubicForwardRepeatedPart (a : ℕ) :=
  GNNonExceptionalRepeatedPart 3 a 1

noncomputable def GNCubicSwapRepeatedPart (a : ℕ) :=
  GNNonExceptionalRepeatedPart 3 1 a
~~~

Expose:

~~~text
ForwardValue a = a^2 + 3*a + 3
SwapValue a = 3*a^2 + 3*a + 1.
~~~

Keep wrappers minimal.

---

## Part II — swap orientation has no exceptional factor 3

Prove:

~~~text
not 3 divides GN 3 1 a.
~~~

Recommended:

~~~text
three_not_dvd_GNCubicSwapValue
~~~

Then prove the swap full-repeated identity:

~~~text
GNNonExceptionalRepeatedPart 3 1 a
=
repeatedPrimePowerPart (GN 3 1 a).
~~~

Recommended:

~~~text
GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart
~~~

Use the absence of the exceptional prime 3.

Do not build a new general exceptional-prime theory.

---

## Part III — swap complement API

Define:

~~~lean
noncomputable def GNExcessCubicSwapComplement (a : ℕ) : ℕ :=
  GN 3 1 a / GNNonExceptionalRepeatedPart 3 1 a
~~~

Prove:

~~~text
GNNonExceptionalRepeatedPart 3 1 a
  * GNExcessCubicSwapComplement a
=
GN 3 1 a

=
3*a^2 + 3*a + 1.
~~~

Also:

~~~text
Squarefree (GNExcessCubicSwapComplement a)

Nat.Coprime
  (GNNonExceptionalRepeatedPart 3 1 a)
  (GNExcessCubicSwapComplement a).
~~~

Reuse the generic repeated-complement API from LUNA-008.

---

## Part IV — sharpen ordinary orientation gcd to 7

Specialize the existing:

~~~text
gcd(GN 3 a 1, GN 3 1 a) divides 14.
~~~

Both values are odd. Prove:

~~~text
Nat.gcd (GN 3 a 1) (GN 3 1 a) divides 7.
~~~

Recommended:

~~~text
gcd_GN_three_one_swap_dvd_seven
~~~

Do not modify the generic gcd-divides-14 theorem.

---

## Part V — exact mod-7 overlap classification

Main theorem:

~~~text
7 divides GN 3 a 1
and
7 divides GN 3 1 a

iff

a % 7 = 1.
~~~

Recommended:

~~~text
seven_dvd_both_cubic_orientations_iff_mod_eq_one
~~~

Use exact modular arithmetic, not a finite computational sweep.

Then prove:

~~~text
gcd(F(a),G(a)) = 7 iff a % 7 = 1
gcd(F(a),G(a)) = 1 iff a % 7 != 1.
~~~

or one equivalent if/then theorem.

This should completely classify ordinary support overlap for b=1.

---

## Part VI — prime overlap theorem

Derive:

~~~text
Nat.Prime q
q divides F(a)
q divides G(a)

=>

q = 7
and a % 7 = 1.
~~~

Recommended:

~~~text
prime_dvd_both_cubic_orientations
~~~

Thus 7 is the unique possible ordinary common prime.

---

## Part VII — repeated-support separation

Reuse:

~~~text
GNNonExceptionalRepeatedPart_three_coprime_swap
~~~

to expose, for positive a:

~~~text
Nat.Coprime
  (GNNonExceptionalRepeatedPart 3 a 1)
  (GNNonExceptionalRepeatedPart 3 1 a).
~~~

Recommended wrapper:

~~~text
GNCubicPairedRepeatedParts_coprime
~~~

Optionally expose the one-parameter square-level wrapper:

~~~text
not (q^2 divides F(a) and q^2 divides G(a)).
~~~

Do not reprove the underlying orientation theorem.

---

## Part VIII — paired repeated/complement packet

For positive a, let

~~~text
MF := GNNonExceptionalRepeatedPart 3 a 1
SF := GNExcessCubicComplement a

MG := GNNonExceptionalRepeatedPart 3 1 a
SG := GNExcessCubicSwapComplement a.
~~~

Prove one packet containing:

~~~text
MF*SF = F(a)
MG*SG = G(a)

Squarefree SF
Squarefree SG

Coprime MF SF
Coprime MG SG
Coprime MF MG.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedComplement_packet
~~~

A conjunction or small structure is acceptable.

No size relation between MF and MG.

---

## Part IX — exact paired product coupling

Reuse the production identity:

~~~text
F(a)*G(a)
=
3*(a+1)^4 + a^2.
~~~

Derive:

~~~text
(MF*SF)*(MG*SG)
=
3*(a+1)^4 + a^2.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedComplement_product_identity
~~~

Also prove:

~~~text
MF*MG divides 3*(a+1)^4 + a^2.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedProduct_dvd_quartic
~~~

If cheap, also prove:

~~~text
squarefull (MF*MG).
~~~

This is exact representation only.

---

## Part X — exact paired linear difference

Reuse the production integer identity:

~~~text
3*F(a) - G(a) = 6*a + 8.
~~~

Derive over Int:

~~~text
3*(MF*SF) - (MG*SG) = 6*a + 8.
~~~

Recommended:

~~~text
GNCubicPairedRepeatedComplement_linear_difference
~~~

Use casts explicitly. Do not use Nat subtraction.

---

## Part XI — all cross gcds divide 7

Prove a reusable helper:

~~~text
A divides F(a)
B divides G(a)
=>
gcd A B divides 7.
~~~

Recommended:

~~~text
gcd_dvd_seven_of_dvd_cubic_orientations
~~~

Instantiate it to obtain:

~~~text
gcd MF SG divides 7
gcd SF MG divides 7
gcd SF SG divides 7.
~~~

MF and MG are already coprime.

Recommended packet:

~~~text
GNCubicPaired_cross_gcd_packet
~~~

This isolates every possible cross-orientation contamination to 7.

---

## Part XII — off-seven sector

For positive a with:

~~~text
a % 7 != 1,
~~~

prove:

~~~text
Coprime MF MG
Coprime MF SG
Coprime SF MG
Coprime SF SG.
~~~

Recommended:

~~~text
GNCubicPaired_offSeven_cross_coprime_packet
~~~

The absence of ordinary overlap should make all forward/swap factor coordinates
cross-coprime.

No size theorem.

---

## Part XIII — seven-sector boundary

For:

~~~text
a % 7 = 1,
~~~

record only the safe facts:

~~~text
gcd(F,G) = 7
7 divides F
7 divides G
not (49 divides F and 49 divides G)
Coprime MF MG.
~~~

Recommended:

~~~text
GNCubicPaired_sevenSector_packet
~~~

Do not assert which orientation carries repeated 7-depth.
Do not bound that depth.

---

## Part XIV — absolute-large regression boundary

Keep the existing theorem visible in the module docstring/report:

~~~text
exists_arbitrarily_large_coprime_cubic_repeated_parts
~~~

Meaning:

~~~text
MF and MG can both be arbitrarily large in absolute size
while remaining coprime.
~~~

This is a hard regression against false size inference.

Do not reprove it.

---

## Negative theorem boundaries

Explicitly document:

~~~text
Coprime MF MG does not imply one orientation is small.

The only ordinary common prime being 7 does not bound either repeated depth.

No theorem here says both repeated parts cannot exceed a+1.

The ASTRA-007 paired relative-height numerical signal remains unproved.
~~~

---

## What LUNA-018 is NOT

Do not attempt:

- paired relative-height exclusion,
- both-repeated-parts <= local-height claims,
- paired shell-count estimates,
- Hensel rarity,
- Pell counting,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not add provider classes or unproved assumptions.

---

## Public import

Import the new module from DkMath.ABC after the current fact-freezing chain,
preferably after GNExcessCubicThreeSectorIncidence unless dependency order
suggests placement near GNCubicOrientation.

Do not reorder unrelated imports.

---

## Verification

At minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicPairedOrientation
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

Audit principal theorems. Expected trust boundary:

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-018.md
~~~

Title:

~~~text
# LUNA-018 — paired-orientation exact arithmetic ledger
~~~

Report:

1. files changed,
2. paired coordinate names,
3. swap prime-to-three theorem,
4. swap full-repeated identity,
5. swap complement API,
6. gcd sharpened to 7,
7. exact mod-7 overlap classification,
8. prime overlap theorem,
9. repeated-part coprimality,
10. paired repeated/complement packet,
11. product/quartic identity,
12. repeated-product divisibility / squarefull status,
13. linear-difference identity,
14. cross-gcd-divides-7 packet,
15. off-seven cross-coprime packet,
16. seven-sector packet,
17. absolute-large-depth regression,
18. focused build,
19. ABC aggregator build,
20. forbidden-construct result,
21. axiom audit,
22. remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the paired one-parameter orientations have one durable ledger:

~~~text
F = MF*SF
G = MG*SG

Squarefree SF
Squarefree SG

Coprime MF SF
Coprime MG SG
Coprime MF MG

gcd(F,G) divides 7

gcd(F,G)=7 iff a mod 7 = 1

(MF*SF)*(MG*SG)
=
3*(a+1)^4 + a^2

and every remaining cross gcd divides 7.
~~~

Do not infer height-relative size.

After LUNA-018, paired-orientation research can restart from a precise factored
coordinate system with its unique ordinary overlap prime isolated.
