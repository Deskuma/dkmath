# instruction-020 — LUNA seven-depth state normalization

## Mission

Continue the ABC–GN campaign in **fact-freezing / productionization mode**.

This checkpoint is **LUNA-020**.

LUNA-018 and LUNA-019 isolated the only ordinary paired-orientation overlap
prime:

~~~text
a % 7 = 1
<->
gcd(F(a), G(a)) = 7
~~~

where

~~~text
F(a) = GN 3 a 1 = a^2 + 3*a + 3
G(a) = GN 3 1 a = 3*a^2 + 3*a + 1.
~~~

They also proved that the repeated parts

~~~text
MF = GNCubicForwardRepeatedPart a
MG = GNCubicSwapRepeatedPart a
~~~

are coprime, so the prime 7 can never be repeated in both orientations.

LUNA-020 should completely normalize the internal **7-depth state** by
working modulo 49.

The exact target is:

~~~text
inside a % 7 = 1:

49 divides F(a)  iff  a % 49 = 29

49 divides G(a)  iff  a % 49 = 22.
~~~

Thus the seven sector has three exact states:

~~~text
forward-deep:
  a % 49 = 29

swap-deep:
  a % 49 = 22

shallow-seven:
  a % 7 = 1
  a % 49 != 29
  a % 49 != 22.
~~~

This is arithmetic normalization only.

Do not count any residue state, estimate any repeated part, or infer any
relative-height statement.

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
report-019.md
report-018.md
report-007.md
report-001.md
~~~

Inspect current production source, especially:

~~~text
DkMath/ABC/GNExcessCubicPairedSquareful.lean
DkMath/ABC/GNExcessCubicPairedOrientation.lean
DkMath/ABC/GNExcessCubicComplement.lean
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/NumberTheory/GNThreeOrientation.lean
~~~

Treat current production Lean as authoritative.

Do not include branch HEAD hashes or commit hashes in report-020.md.

---

## Part I — generic repeated-prime membership bridge

Add a focused production module:

~~~text
DkMath/ABC/GNExcessCubicSevenDepth.lean
~~~

Before adding a generic theorem, search for an equivalent existing result.

If absent, prove for prime q and nonzero n:

~~~text
q divides repeatedPrimePowerPart n
iff
q^2 divides n.
~~~

Recommended theorem:

~~~lean
prime_dvd_repeatedPrimePowerPart_iff_sq_dvd
~~~

Preferred shape:

~~~text
Nat.Prime q
n != 0
->
(q ∣ repeatedPrimePowerPart n <-> q^2 ∣ n).
~~~

The forward direction should consume:

~~~text
prime_sq_dvd_repeatedPrimePowerPart
repeatedPrimePowerPart_dvd
~~~

The reverse direction should use the factorization definition or the existing
support/filter API.

Do not build new valuation machinery.

This helper has high value beyond q=7.

If the reverse generic proof becomes disproportionately expensive, a q=7
specialization for the two positive cubic values is acceptable, but the
generic theorem is preferred.

---

## Part II — repeated 7 iff depth at least two

Using the forward and swap full-repeated identities, prove:

~~~text
7 divides MF
iff
49 divides F(a)

7 divides MG
iff
49 divides G(a).
~~~

Recommended theorem names:

~~~lean
seven_dvd_GNCubicForwardRepeatedPart_iff_49_dvd_value

seven_dvd_GNCubicSwapRepeatedPart_iff_49_dvd_value
~~~

These should be short consumers of Part I plus:

~~~text
GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart

GNNonExceptionalRepeatedPart_three_swap_one_eq_repeatedPrimePowerPart.
~~~

Do not redo factorization.

---

## Part III — algebraic lift of the seven-sector residue

Assume:

~~~text
a % 7 = 1.
~~~

Use the exact decomposition:

~~~text
a = 7*k + 1

k := a / 7.
~~~

Expose a helper if useful:

~~~text
a % 7 = 1
->
a = 7*(a/7) + 1.
~~~

Then derive exact factorizations:

~~~text
F(a)
=
7 * (7*k^2 + 5*k + 1)

G(a)
=
7 * (21*k^2 + 9*k + 1).
~~~

Recommended helper theorems:

~~~lean
GNCubicForwardValue_eq_seven_mul_of_mod_seven_eq_one

GNCubicSwapValue_eq_seven_mul_of_mod_seven_eq_one
~~~

Use ring normalization.

These identities are intended to avoid a brute-force 49-residue proof.

---

## Part IV — exact forward mod-49 depth classification

This is the first main LUNA-020 theorem.

Under:

~~~text
a % 7 = 1,
~~~

prove:

~~~text
49 divides F(a)
iff
a % 49 = 29.
~~~

Recommended:

~~~lean
fortyNine_dvd_GNCubicForwardValue_iff_mod_eq_twentyNine
~~~

Intended algebra:

~~~text
a = 7*k + 1

F(a) = 7*(7*k^2 + 5*k + 1)

49 | F
iff
7 | (5*k + 1)

iff
k % 7 = 4

iff
a % 49 = 29.
~~~

Use exact modular arithmetic.

Do not prove this by a 49-case computational search unless the algebraic route
is genuinely blocked.

---

## Part V — exact swap mod-49 depth classification

Under:

~~~text
a % 7 = 1,
~~~

prove:

~~~text
49 divides G(a)
iff
a % 49 = 22.
~~~

Recommended:

~~~lean
fortyNine_dvd_GNCubicSwapValue_iff_mod_eq_twentyTwo
~~~

Intended algebra:

~~~text
G(a) = 7*(21*k^2 + 9*k + 1)

49 | G
iff
7 | (2*k + 1)

iff
k % 7 = 3

iff
a % 49 = 22.
~~~

Again use exact arithmetic, not numerical search.

---

## Part VI — the two deep states are disjoint

Prove directly:

~~~text
not (
  49 divides F(a)
  and
  49 divides G(a)
)
~~~

as the one-parameter q=7 specialization if not already exposed.

This is already implied by the production theorem

~~~text
not_prime_sq_dvd_both_GN_three.
~~~

Recommended wrapper:

~~~lean
not_fortyNine_dvd_both_cubic_orientations
~~~

Then, under a % 7 = 1, prove:

~~~text
not (a % 49 = 29 and a % 49 = 22).
~~~

This is trivial but useful for the state split.

Do not infer any bound on deeper 7-adic valuation within the chosen orientation.

---

## Part VII — forward-deep state packet

For positive a with:

~~~text
a % 49 = 29,
~~~

note automatically:

~~~text
a % 7 = 1.
~~~

Prove the exact packet:

~~~text
7 divides F
7 divides G

49 divides F
not 49 divides G

7 divides MF
not 7 divides MG

not 7 divides SF
7 divides SG.
~~~

Here:

~~~text
SF := GNExcessCubicComplement a
SG := GNExcessCubicSwapComplement a.
~~~

Recommended theorem:

~~~lean
GNCubicPaired_forwardSevenDeep_packet
~~~

For complement support:

- use F = MF*SF and Coprime MF SF;
- use G = MG*SG and Coprime MG SG;
- since 7 divides G but not MG, Euclid/prime-divides-product forces 7 | SG;
- since 7 divides MF and Coprime MF SF, 7 does not divide SF.

Do not use factorization directly if the paired packet already supplies the
needed decomposition/coprimality.

---

## Part VIII — swap-deep state packet

For positive a with:

~~~text
a % 49 = 22,
~~~

prove the symmetric packet:

~~~text
7 divides F
7 divides G

not 49 divides F
49 divides G

not 7 divides MF
7 divides MG

7 divides SF
not 7 divides SG.
~~~

Recommended:

~~~lean
GNCubicPaired_swapSevenDeep_packet
~~~

Again, no depth bound above 2.

---

## Part IX — shallow-seven state packet

For positive a with:

~~~text
a % 7 = 1
a % 49 != 29
a % 49 != 22,
~~~

prove:

~~~text
7 divides F
7 divides G

not 49 divides F
not 49 divides G

not 7 divides MF
not 7 divides MG

7 divides SF
7 divides SG.
~~~

Recommended:

~~~lean
GNCubicPaired_shallowSeven_packet
~~~

Because SF and SG are squarefree, optionally also expose:

~~~text
not 49 divides SF
not 49 divides SG.
~~~

These are exact depth-one complement facts.

---

## Part X — exact cross-gcd pattern in the three states

LUNA-018 proves every cross gcd divides 7.

Use the state packets to sharpen them to exact gcd values.

### Forward-deep

Prove:

~~~text
gcd(MF, SG) = 7

gcd(SF, MG) = 1

gcd(SF, SG) = 1

gcd(MF, MG) = 1.
~~~

Recommended:

~~~lean
GNCubicPaired_forwardSevenDeep_crossGcd_packet
~~~

### Swap-deep

Prove:

~~~text
gcd(SF, MG) = 7

gcd(MF, SG) = 1

gcd(SF, SG) = 1

gcd(MF, MG) = 1.
~~~

Recommended:

~~~lean
GNCubicPaired_swapSevenDeep_crossGcd_packet
~~~

### Shallow-seven

Prove:

~~~text
gcd(SF, SG) = 7

gcd(MF, SG) = 1

gcd(SF, MG) = 1

gcd(MF, MG) = 1.
~~~

Recommended:

~~~lean
GNCubicPaired_shallowSeven_crossGcd_packet
~~~

The proof pattern is:

- each relevant gcd already divides 7;
- show whether 7 divides both factors;
- use prime-divisor classification of divisors of 7.

This gives a complete exact cross-factor overlap table.

---

## Part XI — repeated-product seven support classification

Under a % 7 = 1, prove:

~~~text
7 divides MF*MG
iff
a % 49 = 29 or a % 49 = 22.
~~~

Recommended:

~~~lean
seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
~~~

Because MF*MG is squarefull, optionally also prove:

~~~text
49 divides MF*MG
iff
a % 49 = 29 or a % 49 = 22.
~~~

Recommended:

~~~lean
fortyNine_dvd_GNCubicPairedRepeatedProduct_iff_deepState
~~~

This is a structural classification only.

Do not infer how large MF*MG is.

---

## Part XII — complement-product seven support classification

Under a % 7 = 1, prove the complementary state:

~~~text
7 divides SF*SG
~~~

always, because ordinary overlap at 7 must live somewhere in each orientation.

More sharply:

~~~text
49 divides SF*SG
iff
shallow-seven state.
~~~

Reason:

- forward-deep: only SG carries one 7;
- swap-deep: only SF carries one 7;
- shallow-seven: both SF and SG carry one 7, so their product carries 49.

This theorem is optional if the cross-gcd packets already express the same
information robustly.

Do not add valuation APIs merely for this corollary.

---

## Part XIII — exact three-state theorem

Package the seven sector into a theorem-level trichotomy.

For positive a with:

~~~text
a % 7 = 1,
~~~

prove exactly one of:

~~~text
A. a % 49 = 29

B. a % 49 = 22

C. a % 49 != 29 and a % 49 != 22.
~~~

Recommended theorem:

~~~lean
GNCubicPaired_sevenDepth_cases
~~~

A disjunction theorem is enough.

If useful, return the corresponding forward-deep / swap-deep / shallow packet
inside each branch.

Do not introduce an inductive state type unless it clearly simplifies later
finite-set work.

---

## Part XIV — optional residue list for shallow state

Inside a % 7 = 1, the seven possible residues mod 49 are:

~~~text
1, 8, 15, 22, 29, 36, 43.
~~~

Thus shallow residues are:

~~~text
1, 8, 15, 36, 43.
~~~

This explicit list is optional.

Do not add it unless it is useful for regression or later finite filters.

The inequality form

~~~text
mod49 != 22 and mod49 != 29
~~~

is the preferred durable API.

---

## Part XV — no deeper inference

Document explicitly:

~~~text
forward-deep means valuation at 7 is at least 2 in F,
not exactly 2.

swap-deep means valuation at 7 is at least 2 in G,
not exactly 2.

LUNA-020 does not bound arbitrary 7-adic depth.

The Hensel machinery already shows arbitrarily deep local roots are possible.
~~~

This warning is important.

---

## Negative theorem boundaries

Do not claim:

~~~text
deep state is rare;

forward-deep or swap-deep has bounded valuation;

one deep state cannot occur often;

the mod-49 split yields a density gain sufficient for ABC;

seven-depth state controls relative height.
~~~

The residue classification is exact local arithmetic only.

---

## What LUNA-020 is NOT

Do not attempt:

- counts of the three states,
- density estimates,
- higher 7-adic depth counting,
- paired relative-height exclusion,
- shell-count estimates,
- Hensel rarity,
- ABC quality coupling,
- any use of abc_main_axiom.

Do not introduce providers or unproved assumptions.

---

## Public import

Import the new module from DkMath.ABC immediately after:

~~~text
GNExcessCubicPairedSquareful
~~~

Do not reorder unrelated imports.

---

## Verification

At minimum:

~~~text
lake build DkMath.ABC.GNExcessCubicSevenDepth
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

Audit principal declarations, especially:

- generic repeated membership bridge,
- forward/swap mod-49 classification,
- three state packets,
- cross-gcd packets,
- repeated-product seven-support classification.

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
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-020.md
~~~

Title:

~~~text
# LUNA-020 — seven-depth state normalization
~~~

Report:

1. files changed,
2. repeated-prime membership bridge,
3. repeated-7 iff 49-divisibility,
4. seven-sector algebraic lift,
5. forward mod-49 classification,
6. swap mod-49 classification,
7. deep-state disjointness,
8. forward-deep packet,
9. swap-deep packet,
10. shallow-seven packet,
11. exact cross-gcd tables,
12. repeated-product seven-support classification,
13. optional complement-product classification status,
14. exact three-state theorem,
15. deeper-valuation warning,
16. focused build,
17. ABC aggregator build,
18. forbidden-construct result,
19. axiom audit,
20. remaining research frontier.

Update README / ROADMAP minimally if successful.

---

## Stop condition

Stop when the seven sector is completely normalized at depth two:

~~~text
a % 7 = 1

forward-deep:
  a % 49 = 29
  7 divides MF
  7 does not divide MG

swap-deep:
  a % 49 = 22
  7 does not divide MF
  7 divides MG

shallow-seven:
  a % 49 != 29
  a % 49 != 22
  7 does not divide MF
  7 does not divide MG
  7 divides SF
  7 divides SG.
~~~

Together with the exact cross-gcd table, this should eliminate the final
ordinary-overlap ambiguity left by LUNA-018/LUNA-019.

Do not count the states.

After LUNA-020, paired research can restart with the prime 7 completely
localized to one of three exact depth states.
