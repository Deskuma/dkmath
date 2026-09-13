# CGE-010 — Quadruple Signed CRT / Bounded Alternating Pascal Payment

## 0. Stage contract

Continue `wip/goldbach-cross-gap-exchange-260913-v0` after CGE-009.

CGE-009 completed the exact first three signed-CRT / Pascal layers under the existing finite anchor hypotheses:

```text
SignedSingleCRTSum = WindowIncidence
SignedPairCRTSum   = PairOverlap
SignedTripleCRTSum = TripleOverlap
```

and added the exact three-layer provider

```text
Single < Window + (Pair - Triple)
```

as a sufficient survivor condition.

The next obstruction is support multiplicity `4`.  At one seat with support size `k`, the true first-overlap excess is `k - 1` for `k > 0`.  For `k = 4`, the current payment undercounts:

```text
choose 4 2 - choose 4 3 = 6 - 4 = 2
true excess = 3
```

and the missing unit is `choose 4 4 = 1`.

However, **do not assert** the unconditional inequality

```text
Pair - Triple + Quadruple ≤ OverlapExcess
```

for arbitrary support size.  It is false already at `k = 5`:

```text
choose 5 2 - choose 5 3 + choose 5 4 = 10 - 10 + 5 = 5
true excess = 4
```

Therefore CGE-010 is explicitly a **bounded-support checkpoint**.  Add the fourth Pascal/CRT layer and prove exact recovery of overlap only under a visible `support.card ≤ 4` hypothesis (or an equivalent finite-world hypothesis such as `S.card ≤ 4`).

Do not add Strong Goldbach, a universal survivor theorem, or any claim that the four-layer truncation is safe for arbitrary worlds.

## 1. Existing production API to reuse

Reuse current declarations rather than duplicating them.

From `BalancedCapacity.lean`:

```text
goldbachWindowIncidence
goldbachObstructionSupportIn
goldbachWindowLocalOverlapExcess
goldbachWindowOverlapExcess
goldbachWindowIncidenceConservation
goldbachWindowSurvivors_nonempty_iff_incidence_lt
```

From `BalancedPascalOverlap.lean`:

```text
goldbachWindowLocalPairMultiplicity
goldbachWindowLocalTripleMultiplicity
goldbachWindowPairOverlapCount
goldbachWindowTripleOverlapCount
```

From `BalancedSignedCRTOverlap.lean` / `BalancedSignedCRTExact.lean`:

```text
goldbachProgressionSeats
goldbachProgressionWindowCount
mem_goldbachProgressionSeats_iff_balanced_modEq
goldbach_signed_pair_raw_iff_support
goldbachSignedPairCRTSum
goldbachSignedTripleCRTSum
goldbachSignedPairCRTSum_eq_windowPairOverlapCount
goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
```

From `BalancedSignedCRTIncidence.lean`:

```text
goldbachSignedSingleCRTSum
goldbachSignedSingleCRTSum_eq_windowIncidence
goldbachWindowSurvivor_of_exact_signed_crt_budget
goldbachPairAt_of_exact_signed_crt_budget
```

From `BalancedReflection.lean`:

```text
goldbachBalancedOffsets
goldbachWindowSurvivors
goldbachPairAt_of_goldbachWindowSurvivor
```

Keep the CGE-008/CGE-009 endpoint normalization hypothesis `2 ≤ n` explicit where required.

## 2. Suggested owner module

Add a small owner module, candidate path:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTQuadruple.lean
```

Export it from:

```text
DkMath/NumberTheory/Goldbach.lean
```

All declaration names below are candidates.  Use cleaner names if Lean ergonomics suggest them and record final names in `report-010.md`.

## 3. Fourth local Pascal layer

Define the seat-local fourth multiplicity:

```lean
def goldbachWindowLocalQuadrupleMultiplicity
    (n _w : ℕ) (S : Finset ℕ) (t : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupportIn n t S).card 4
```

and the window sum:

```lean
def goldbachWindowQuadrupleOverlapCount
    (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    goldbachWindowLocalQuadrupleMultiplicity n w S t
```

Prove the pure bounded-support arithmetic kernel.  Preferred theorem shape:

```text
k ≤ 4 ->
(k - 1) = (choose k 2 - choose k 3) + choose k 4
```

or an equivalent statement suitable for rewriting the local overlap excess.

Then lift it seatwise.

Preferred generic hypothesis:

```text
∀ t ∈ goldbachBalancedOffsets n w,
  (goldbachObstructionSupportIn n t S).card ≤ 4
```

Under this hypothesis, prove the exact window identity

```text
goldbachWindowOverlapExcess n w S
  = (goldbachWindowPairOverlapCount n w S
      - goldbachWindowTripleOverlapCount n w S)
    + goldbachWindowQuadrupleOverlapCount n w S.
```

If `Nat` subtraction makes the global sum proof awkward, it is acceptable to first prove a local identity and sum after showing the relevant subtraction is nontruncating for `k ≤ 4`.  Do not silently move between `Nat` and `Int` without an explicit theorem.

Also provide an easy sufficient support bound from the finite world, e.g.

```text
(goldbachObstructionSupportIn n t S).card ≤ S.card
```

and a corollary that `S.card ≤ 4` implies the window support bound.  This is useful for the `primeScalesUpTo 7` regression.

## 4. Quadruple signed CRT geometry

Add a fourth signed CRT layer mirroring CGE-007/CGE-008.

Implementation choice is open:

1. strictly ordered quadruples `p < q < r < s`, or
2. `S.powersetCard 4` with product modulus.

Prefer the representation that minimizes tuple bureaucracy and exposes the cardinality proof cleanly.  A `powersetCard 4` implementation is acceptable and may be preferable because the Pascal layer already counts 4-element support subsets.

For one 4-element prime subset / strictly ordered quadruple, define the canonical signed residue family in one product period:

```text
t0 < product modulus
and for every coordinate prime r,
(t0 : ZMod r) ∈ goldbachForbiddenResidues n r.
```

Lift each canonical residue to the balanced window using the existing progression API.

Define a per-quadruple exact count and a world sum, candidate names:

```text
goldbachSignedQuadrupleCRTCount
goldbachSignedQuadrupleCRTSum
```

Deduplicate sign collapse through the residue `Finset`; do not count sign labels with multiplicity.

## 5. Exact signed quadruple sum = fourth Pascal count

Under the same finite prime-world hypotheses used by CGE-008/CGE-009:

```text
2 ≤ n
KnownPrimeScales S
∀ r ∈ S, r ≤ P
P < n - w
```

prove that one quadruple CRT progression family is exactly the balanced seats where those four primes all lie in `goldbachObstructionSupportIn`.

Then double-count over four-element world subsets / strict quadruples and prove the main fourth-layer theorem:

```text
goldbachSignedQuadrupleCRTSum n w S
  = goldbachWindowQuadrupleOverlapCount n w S.
```

This is the decisive CRT theorem of CGE-010.

The intended finite hierarchy after this stage is:

```text
SignedSingleCRTSum    = Incidence
SignedPairCRTSum      = PairOverlap
SignedTripleCRTSum    = TripleOverlap
SignedQuadrupleCRTSum = QuadrupleOverlap
```

Do not infer the corresponding identity for degree `5` or arbitrary degree unless it falls out as a small generic lemma with no scope expansion.

## 6. Bounded four-layer provider

Using the exact overlap identity from section 3 and exact signed identities from sections 4–5, add a sufficient survivor provider under the explicit support bound.

Candidate shape:

```lean
theorem goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w)
    (hsupport4 : ∀ t ∈ goldbachBalancedOffsets n w,
      (goldbachObstructionSupportIn n t S).card ≤ 4)
    (hbudget :
      goldbachSignedSingleCRTSum n w S <
        (goldbachBalancedOffsets n w).card +
          ((goldbachSignedPairCRTSum n w S -
              goldbachSignedTripleCRTSum n w S) +
            goldbachSignedQuadrupleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty
```

A corollary replacing `hsupport4` by `S.card ≤ 4` is desirable.

For `S = primeScalesUpTo P`, add an anchor-local `GoldbachPairAt` wrapper if the hypotheses remain clean.  Keep the SquareBody conditions unchanged:

```text
w ≤ n
P < n - w
n + w ≤ squareBody P
```

This is still a conditional fixed-target provider, not a universal theorem.

## 7. Required regression: multiplicity-four target

Add a new executable audit for

```text
n = 22
w = 9
P = 7
S = primeScalesUpTo 7 = {2,3,5,7}
```

The anchor/horizon checks are:

```text
7 < 22 - 9
22 + 9 ≤ squareBody 7
```

Kernel-check the balanced support sizes if practical.  Expected support pattern for `t = 0..9` is:

```text
1,2,3,1,2,1,2,2,4,0
```

Hence expected aggregate values are:

```text
Window      = 10
Incidence   = 18
Pair        = 13
Triple      = 5
Quadruple   = 1
Overlap     = 9
```

The existing three-layer payment stalls exactly:

```text
18 < 10 + (13 - 5)      -- false; 18 < 18
```

while the four-layer bounded payment succeeds:

```text
18 < 10 + ((13 - 5) + 1)  -- true; 18 < 19
```

Replay the new bounded four-layer provider and, if all anchor/SquareBody hypotheses are met, close the fixed regression `GoldbachPairAt 22`.

This regression is important because it demonstrates a real gain over CGE-009 rather than merely replaying `n=15` or `n=50`.

## 8. Arithmetic firewall at support size 5

Add a pure arithmetic audit showing why the support bound is mandatory.

Kernel-check:

```text
choose 5 2 = 10
choose 5 3 = 10
choose 5 4 = 5
true excess = 4
```

and therefore the four-layer truncation gives `5`, not a safe lower bound for the true excess `4`.

Do **not** export any theorem suggesting unconditional

```text
Pair - Triple + Quadruple ≤ OverlapExcess.
```

If a theorem is useful, export the negating firewall or simply retain it in the audit/report.

## 9. Optional design note for the next stage

If implementation naturally exposes the pattern, record—but do not require—a future path toward the full alternating Pascal tail:

```text
k - 1 = C(k,2) - C(k,3) + C(k,4) - C(k,5) + ...
```

For a general theorem, `Int`-valued alternating sums or a parity-separated formulation may be safer than nested `Nat` subtraction.  CGE-010 should not expand into an arbitrary-degree framework unless the generalization is genuinely simpler than the bounded fourth layer.

## 10. Firewalls / non-goals

Do not add:

- Strong Goldbach;
- a universal strict signed-CRT budget;
- a universal survivor theorem;
- an unconditional four-layer lower bound for arbitrary support size;
- a claim that four layers suffice for all finite worlds;
- analytic density, RH/CFBRC, AKS, or probabilistic input;
- coprimality as a primality replacement;
- hidden endpoint assumptions;
- `sorry`, `admit`, `native_decide`, `unsafe`, or new axioms.

Preserve CGE-004 through CGE-009 APIs.  The new layer refines them; it does not replace the previous sufficient providers.

## 11. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Audit new public declarations with `#print axioms` where practical.  Report any `sorryAx`, new axiom, warning, or forbidden construct immediately.

## 12. Report

Add:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-010.md
```

Record:

- final fourth-layer declaration names;
- whether the bounded local Pascal identity is exact;
- whether `SignedQuadrupleCRTSum = QuadrupleOverlap` is proved;
- exact hypotheses used for support-size `≤ 4`;
- the `n=22,w=9,P=7` values and whether the three-layer budget stalls while the four-layer budget closes;
- the support-size-5 firewall;
- build/axiom/forbidden-construct results;
- Outcome A/B/C.

Preferred outcome labels:

```text
A — BOUNDED FOUR-LAYER CRT/PASCAL CLOSURE
B — QUADRUPLE LAYER ONLY / PROVIDER NOT CLOSED
C — STRUCTURAL / ENGINEERING ONLY
```

The decisive success condition is: exact signed quadruple CRT counting is identified with the fourth Pascal overlap layer, and under an explicit support-size `≤ 4` bound the four-layer payment safely improves the existing provider.
