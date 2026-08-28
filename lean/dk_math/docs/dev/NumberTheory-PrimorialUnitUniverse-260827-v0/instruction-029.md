# PUU-L029 — Fresh-Prime Mixed-Radix Lift Digit / Static-Dynamic Fiber Identification

## 0. Status / purpose

PUU-L028 completed the old-period monodromy:

```text
r_S(n) = n mod M
Q_S(n) = n / M
Pplus_S,q(n) = Q_S(n) mod q
```

and showed that `q` old-period turns close at the enlarged period
`M(insert q S) = q * M(S)`.

This checkpoint should now identify that quotient residue with the **actual raw
fresh-prime lift index** of the canonical enlarged representative.  This is the
missing static/dynamic compatibility bridge between:

```text
PUU-L007–L009 : static fresh-prime raw-lift / projection fiber
PUU-L020      : static two-sheet phase cover
PUU-L027–L028 : moving-anchor successor / monodromy dynamics
```

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import
Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixTransport
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhasePeriodTransport
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiberProjection
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade
docstring.

---

## 1. Fresh-prime block digit

Let

```text
M := finitePrimeBasisProduct S
Q_S(n) := n / M.
```

Define the fresh-prime mixed-radix digit

```lean
def squareAnchorFreshPrimeBlockDigit
    (S : Finset ℕ) (q n : ℕ) : ℕ :=
  squareAnchorPhaseBlockQuotient S n % q
```

or an equivalent definition.

For prime `q`, prove

```text
digit < q.
```

Do not require coprimality of the moving anchor `n`.  The digit exists for every
anchor; coprimality only matters later when one wants the distinguished seats to
be pairwise distinct survivors.

---

## 2. Mixed-radix quotient decomposition

For fresh prime `q ∉ S`, prove the exact quotient decomposition

```text
Q_S(n)
  = digit_q(n) + q * Q_(insert q S)(n).
```

Use

```text
finitePrimeBasisProduct (insert q S) = q * M.
```

Equivalent multiplication orientation is acceptable if it matches the existing
product theorem.

Then expose the full mixed-radix decomposition of the anchor:

```text
n
  = r_S(n)
  + digit_q(n) * M
  + Q_(insert q S)(n) * (q*M).
```

This should be a direct Euclidean/mixed-radix theorem, not an induction over the
successor transport.

---

## 3. Enlarged canonical representative is the old raw lift at that digit

This is a central theorem.

Prove a theorem equivalent to

```text
r_(insert q S)(n)
  = primeBasisWheelLift S (r_S(n)) (digit_q(n)).
```

Preferred theorem name:

```lean
squareAnchorPhaseRepresentative_insert_eq_old_lift_digit
```

where

```text
r_S(n) := squareAnchorPhaseRepresentative S n.
```

Mathematical reading:

```text
canonical coordinate modulo q*M
  = old canonical coordinate modulo M
  + one fresh-prime lift digit times M.
```

Also expose the old-projection consequence:

```text
primeBasisWheelProjection S (r_(insert q S)(n)) = r_S(n).
```

Prefer to derive this from the canonical lift formula or the existing nested
projection API rather than reproving modular arithmetic from scratch.

---

## 4. Dynamic plus sheet equals the lift digit

Combine PUU-L028

```text
Pplus_S,q(n) = Q_S(n)  in ZMod q
```

with the digit definition to prove

```text
Pplus_S,q(n) = digit_q(n)  in ZMod q.
```

Preferred theorem:

```lean
squareAnchorFreshPrimePlus_eq_blockDigit
```

This theorem should make the static/dynamic identification explicit:

```text
dynamic plus-sheet coordinate
  = fresh-prime raw-lift index of the enlarged canonical representative.
```

Do not claim a natural-number equality between a `ZMod q` coordinate and the digit
without the appropriate cast.

---

## 5. Canonical enlarged representative is a plus raw-lift witness

Prove that the digit itself realizes the `+n` fresh-prime lift condition over the
old canonical representative.

Preferred theorem shape:

```lean
squareAnchorFreshPrimeBlockDigit_is_plusLiftIndex
```

with semantic conclusion

```text
IsFreshPrimePlusLiftIndex
  S q n (squareAnchorPhaseRepresentative S n)
  (squareAnchorFreshPrimeBlockDigit S q n).
```

The proof should use:

1. `digit < q`;
2. the enlarged-representative/raw-lift equality;
3. reduction modulo `q` of `n mod (q*M)`.

No coprime-anchor hypothesis is required for this theorem.  If `q ∣ n`, the plus
seat may coincide with the deleted seat; preserve that degeneracy rather than
forcing distinctness.

---

## 6. Canonical enlarged representative lies in the static phase projection fiber

Prove the provider bridge

```lean
squareAnchorPhaseRepresentative_insert_mem_projectionFiber
```

conceptually:

```text
r_(insert q S)(n)
  ∈ squareAnchorPhaseProjectionFiber
      S q n (r_S(n)).
```

This is the direct connection to PUU-L020:

```text
moving canonical enlarged anchor
  ↓
static enlarged phase fiber
  ↓ old projection
canonical old anchor.
```

Again, do not require the anchor to be coprime merely for phase membership.

If a coprime-anchor corollary is useful, it may additionally state that this
canonical plus lift belongs to the phase/survivor subcover, but keep that as a
corollary rather than the main theorem.

---

## 7. Old-period turns advance exactly one fresh-prime digit

Using PUU-L028, prove

```text
digit_q(n + M) = (digit_q(n) + 1) % q.
```

and preferably the `k`-turn form

```text
digit_q(n + k*M) = (digit_q(n) + k) % q.
```

This gives the concrete raw-lift interpretation of monodromy:

```text
one old-period turn
  = move to the next raw lift index modulo q.
```

Do not introduce cyclic-order / geodesic-distance abstractions.

---

## 8. One enlarged-period orbit traverses the raw lift fiber

Formalize at least one theorem showing that over `q` successive old-period turns,
the digit returns to its initial value:

```text
digit_q(n + q*M) = digit_q(n).
```

Stronger preferred result, if it stays clean:

for `k₁,k₂ < q`, equality of the two digits

```text
digit_q(n + k₁*M) = digit_q(n + k₂*M)
```

implies

```text
k₁ = k₂.
```

This makes the `q` old-period turns a genuine enumeration of the `q` raw lift
indices above one old representative.

If convenient, package this as a Finset/cardinality or injectivity theorem, but do
not build a large permutation abstraction merely for style.

### Static unique-deletion compatibility

If the existing PUU-L007 API makes it short, add a bridge showing that the unique
fresh-prime deleted raw lift occurs at exactly one turn in this `q`-step digit
orbit.  Prefer reusing the existing unique-deletion theorem rather than reproving
it.

This is optional for A+ if the required API connection becomes disproportionately
large; the mixed-radix/raw-lift identification is the primary result.

---

## 9. Visible `6 -> 30` regression

Use

```text
S = {2,3}, M = 6, q = 5.
```

For a fixed old representative, a useful dynamic sample is

```text
n = 4, 10, 16, 22, 28, 34.
```

Expected old block quotients / digits:

```text
Q_S(n) : 0, 1, 2, 3, 4, 5
digit  : 0, 1, 2, 3, 4, 0  mod 5.
```

Expected enlarged canonical representatives modulo `30`:

```text
4, 10, 16, 22, 28, 4.
```

Thus the first five values are exactly the five raw lifts of old representative
`4`, and the sixth closes at the enlarged period.

Route the regression through the public L029 API where practical.  Do not reduce
the entire theorem to a detached `decide`.

---

## 10. A+ rubric

PUU-L029 is Outcome A+ if it establishes the following finite provider structure:

1. fresh-prime block digit `Q_S(n) % q`;
2. exact quotient/mixed-radix decomposition;
3. enlarged canonical representative = old raw lift at that digit;
4. dynamic plus sheet = digit in `ZMod q`;
5. digit is the actual `+n` raw-lift witness;
6. enlarged canonical representative belongs to the static phase projection fiber;
7. old-period turns advance the digit modulo `q`;
8. `q` turns close at the enlarged period;
9. visible `6 -> 30` regression;
10. no Legendre/escape consumer assumption.

The main conceptual theorem is:

```text
fresh-prime tower insertion is one mixed-radix digit,
and the moving plus sheet is exactly that digit.
```

---

## 11. STOP / information-content gate

After PUU-L029, do **not** automatically continue producing more quotient/digit
identities.

PUU-L029 should complete the intended Phase E3 static/dynamic tower compatibility:

```text
old wheel projection
    ↕
fresh-prime raw-lift index
    ↕
block quotient digit
    ↕
dynamic plus sheet
    ↕
enlarged canonical representative.
```

The next step should be an information-content audit:

- Does this compatibility force a genuinely new invariant or forbidden pattern for
  reservation dynamics?
- Or is it only a complete coordinate description of the already-known finite
  wheel?

Only if a new obstruction is identified should the branch advance toward the
coverage-obstruction / Legendre re-entry gate.  Otherwise record Phase E3 as a
successful structural endpoint rather than entering another synonym loop.

---

## 12. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-mixed-radix-lift-digit-260828.md
```

Record:

- exact theorem names;
- the mixed-radix decomposition;
- the enlarged-representative/raw-lift identity;
- plus-sheet/digit identity;
- projection-fiber connection;
- `q`-turn traversal/closure result;
- the `6 -> 30` regression;
- any theorem whose hypotheses were weaker than initially expected;
- whether the unique-deletion bridge was included;
- strict boundary: no escape / Legendre / Jacobsthal / PNT / RH / PowerSwap / GN
  conclusion.
