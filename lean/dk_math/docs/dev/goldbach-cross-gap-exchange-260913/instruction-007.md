# CGE-007: General Signed CRT Pair/Triple Geometry

## 0. Scope / contract

This checkpoint generalizes CGE-006 from the center-aligned one-class case to the ordinary signed Goldbach residue geometry

```text
t ≡  n (mod r)
or
t ≡ -n (mod r)
```

for pair and triple obstruction layers inside the already-defined balanced window.

The implementation MUST remain finite, anchor-local, and combinatorial.

Do **not** add any of the following:

- Strong Goldbach,
- a universal survivor theorem,
- a universal capacity inequality,
- RH / CFBRC / AKS,
- analytic density estimates,
- a coprime-implies-prime shortcut,
- an axiom or hidden assumption equivalent to Goldbach.

The goal is only to replace the center-aligned triple restriction of CGE-006 by an explicit signed CRT residue-family API, and to connect that API to the existing pair/triple Pascal payment of CGE-005.

Use the current repository as the source of truth. Reuse existing declarations where possible; do not duplicate `PrimeWorld`, `BalancedCapacity`, `BalancedPascalOverlap`, or `BalancedCRTOverlap` APIs.

Suggested owner module:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTOverlap.lean
```

Export it from `DkMath.NumberTheory.Goldbach` only after the focused build passes.

---

## 1. Existing facts to reuse

Relevant existing APIs include at least:

- `goldbachForbiddenResidues n r`
- `goldbach_residue_eq_neg_iff`
- `goldbach_card_forbidden`
- `goldbach_obstructed_iff_mem_forbidden`
- `goldbachBalancedOffsets n w`
- `goldbachObstructionSupportIn n t S`
- `goldbachWindowPairOverlapCount`
- `goldbachWindowTripleOverlapCount`
- `goldbachWindowPairOverlap_sub_triple_le_overlap`
- the CGE-004 residue-capacity / overlap provider
- the CGE-005 pair-minus-triple provider
- `goldbachPrimePairs` or the corresponding strict unordered pair API if already available
- `goldbachPrimeTriples`
- `KnownPrimeScales`
- the CRT infrastructure already used by `PrimeWorld.lean` and CGE-006.

CGE-006 currently supplies the left-oriented witness

```text
n % (p*q)
```

and a center-aligned triple progression.  Keep those theorems intact.  CGE-007 should generalize beside them, not rewrite them destructively.

---

## 2. Mathematical target

For a prime `r`, the raw Goldbach obstruction classes are the finite set

```text
{ n, -n } mod r
```

with duplicate removal when `r ∣ 2*n`.

For a strict prime pair `p < q`, simultaneous obstruction therefore lies in the product of two local choices, nominally at most `2^2 = 4` signed CRT classes modulo `p*q`.

For a strict prime triple `p < q < r`, simultaneous obstruction lies in at most `2^3 = 8` signed CRT classes modulo `p*q*r`.

When one coordinate satisfies `r ∣ 2*n`, its `+n` and `-n` choices coincide.  The implementation MUST deduplicate such collapsed sign patterns at the residue level.  Do not count sign labels as distinct when they produce the same CRT residue.

The intended object is therefore a **finite set of canonical CRT residues**, not a raw Boolean sign cube with multiplicity.

---

## 3. CGE-007-A: signed pair residue family

Define a finite residue-family object for a strict pair `p < q` whose members are canonical natural representatives

```text
0 ≤ t₀ < p*q
```

such that

```text
(t₀ : ZMod p) ∈ goldbachForbiddenResidues n p
(t₀ : ZMod q) ∈ goldbachForbiddenResidues n q.
```

Implementation choice is flexible:

- construct via the four raw sign patterns and deduplicate with `Finset`, or
- construct directly by CRT over the two local forbidden finite sets.

Prefer whichever route gives the cleanest kernel-checked membership theorem.

Required theorem shape:

```text
t₀ ∈ signedPairResidues n p q
↔
t₀ < p*q ∧
  (t₀ : ZMod p) ∈ goldbachForbiddenResidues n p ∧
  (t₀ : ZMod q) ∈ goldbachForbiddenResidues n q
```

under explicit prime/distinctness hypotheses as needed.

Also expose a cardinality bound

```text
card signedPairResidues ≤ 4
```

and, if easy, a sharper product bound

```text
card signedPairResidues
  ≤ card (goldbachForbiddenResidues n p) *
    card (goldbachForbiddenResidues n q).
```

Do not force equality when sign classes collapse.

---

## 4. CGE-007-B: signed triple residue family

Analogously define canonical residues modulo `p*q*r` for a strict triple `p < q < r` satisfying all three local forbidden conditions.

Required membership theorem:

```text
t₀ ∈ signedTripleResidues n p q r
↔
t₀ < p*q*r ∧
  forbidden_at p t₀ ∧
  forbidden_at q t₀ ∧
  forbidden_at r t₀
```

with the actual existing `goldbachForbiddenResidues` predicate in the formal statement.

Expose at least

```text
card signedTripleResidues ≤ 8
```

and preferably the local-cardinality product bound.

The center-aligned CGE-006 theorem should become a regression/corollary: if all three primes divide `2*n`, the signed triple family collapses to one residue class, namely the existing canonical progression residue.

Do not delete or replace `GoldbachCenterAlignedWorld`; show compatibility instead.

---

## 5. CGE-007-C: exact progression description inside a balanced window

For any canonical residue `t₀` modulo a positive modulus `M`, seats in the same CRT class have the form

```text
t = t₀ + M*k.
```

Build/reuse a small arithmetic lemma giving an executable count of representatives in the balanced window.

A preferred exact count for the plain interval `0 ≤ t ≤ w` is

```text
if t₀ ≤ w then (w - t₀) / M + 1 else 0
```

for `M > 0`.

Because `goldbachBalancedOffsets n w` is also restricted by `goldbachOffsets n`, either:

1. assume a simple hypothesis such as `w + 2 ≤ n`, so the balanced window is literally `range (w+1)`, or
2. use the existing exact card/range theorem and count against `min (n-1) (w+1)`.

Prefer the simpler theorem statement if it substantially reduces proof noise, but state every restriction explicitly.

Do not silently replace the balanced window by `0..w` without proving the equivalence under the chosen hypotheses.

---

## 6. CGE-007-D: tuple-wise signed CRT counts

Define executable per-pair and per-triple balanced-window counts by summing the progression counts over **distinct canonical signed residues**.

Candidate names are implementation suggestions only:

```text
goldbachSignedPairCRTCount
goldbachSignedTripleCRTCount
```

For one strict pair/triple these counts should represent the number of balanced seats satisfying the raw simultaneous forbidden residue conditions for that tuple.

Then sum over strict unordered prime pairs/triples in a finite world `S`:

```text
SignedPairCRTSum n w S
SignedTripleCRTSum n w S
```

Avoid counting ordered permutations of the same pair/triple.

---

## 7. CGE-007-E: connect raw signed CRT geometry to proper obstruction support

Use the same endpoint firewall as CGE-006.

Assume a finite prime world `S`, a world bound

```text
∀ r ∈ S, r ≤ P,
```

and anchor/window hypotheses strong enough to force

```text
r < n - t
```

for every `r ∈ S` and every balanced seat under consideration.

For example, the existing pattern

```text
w ≤ n
P < n - w
```

is acceptable.

Under this anchor condition, raw divisibility cannot be the exceptional equality `endpoint = r`, so raw forbidden residue membership is equivalent to a proper obstruction at that coordinate.

Prove the signed CRT tuple counts connect to the existing Pascal overlap layers.

Best outcome:

```text
SignedPairCRTSum = goldbachWindowPairOverlapCount
SignedTripleCRTSum = goldbachWindowTripleOverlapCount
```

under the explicit anchor/prime/distinctness hypotheses.

If exact equality is too expensive in this checkpoint, acceptable fallback is:

```text
SignedPairCRTSum ≤ goldbachWindowPairOverlapCount

goldbachWindowTripleOverlapCount ≤ SignedTripleCRTUpperSum
```

with a report explaining precisely where equality was not obtained.

Do not assert an inequality in the useful direction unless the injection/surjection is actually formalized.

---

## 8. CGE-007-F: provider bridge

Connect the signed CRT quantities to the existing CGE-005 provider.

If exact pair/triple identities are proved, expose a theorem whose budget is stated purely in terms of the signed CRT counts:

```text
ResidueCapacity <
  card Window + (SignedPairCRTSum - SignedTripleCRTSum)
```

and conclude a window survivor, then optionally the existing anchor-local `GoldbachPairAt n` endpoint.

If only lower/upper bounds are available, use the safe form

```text
ResidueCapacity <
  card Window + (SignedPairLower - SignedTripleUpper)
```

where those directions have been proved from the signed CRT geometry.

This theorem remains CONDITIONAL.  Do not prove or state that its budget holds for all `n`.

---

## 9. Required regressions

### 9.1 Preserve target-30

Re-run the existing `n=15`, `w=8`, `P=5` case.

The signed layer must collapse compatibly with CGE-006 and recover the existing values:

```text
PairLower / pair signed contribution = 3
TripleUpper / triple signed contribution = 0
Window = 9
Capacity = 10
```

and the existing strict budget replay must still work.

### 9.2 Non-center-aligned mixed-sign world

Add one audit where the sign classes genuinely do **not** all collapse.

Recommended finite world:

```text
n = 50
w = 10
S = primeScalesUpTo 7 = {2,3,5,7}
```

Here the world is not center-aligned: `3 ∤ 100` and `7 ∤ 100`, while `2 ∣ 100` and `5 ∣ 100`.

Expected combinatorial values to verify independently in Lean before committing them as regression facts:

```text
Window = 11
PairOverlap = 12
TripleOverlap = 2
Pair-Triple = 10
OverlapExcess = 10
```

This is an especially useful mixed-collapse test: some sign coordinates merge and others remain doubled.

For the existing width-local residue capacity, the expected coarse sum is

```text
Capacity = 21
```

so the strict budget becomes

```text
21 < 11 + 10
```

which is FALSE by equality.

This failure is intentional and MUST be preserved as a firewall: even exact signed pair/triple accounting does not by itself prove the survivor budget universally.  Do not weaken `<` to `≤`.

If any expected numeric value above differs when evaluated against the exact repository definitions, report the actual kernel-checked value and explain the source of the difference rather than forcing the expectation.

---

## 10. Arithmetic / logical firewalls

The audit should include these points explicitly:

1. `+/-` sign labels are not counted with multiplicity after CRT residues coincide.
2. `r ∣ 2*n` collapses the two local forbidden classes to one.
3. strict `p < q < r` or the existing canonical tuple convention excludes repeated primes.
4. raw residue obstruction is converted to proper obstruction only under the anchor endpoint inequality.
5. signed CRT pair/triple accounting is not a primality theorem.
6. pair-minus-triple is still only a lower payment for first overlap in general support size `≥ 4`.
7. a failed strict budget is a valid Outcome A/B result; do not patch it by asserting survivor existence.

---

## 11. Verification

Run at minimum:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Run `#print axioms` for the main new endpoint theorems.

No new `sorryAx`, `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` implementation shortcut.

Keep repository warning policy unchanged.

---

## 12. Report

Write:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-007.md
```

Report the exact theorem names actually implemented and choose one outcome:

### Outcome A — GENERAL SIGNED CRT OVERLAP ACCOUNTING

General pair/triple signed CRT residue families are connected kernel-correctly to the balanced Pascal overlap layers, with mixed sign-collapse regressions passing.

### Outcome B — PARTIAL SIGNED CRT TRANSPORT

The signed residue/progression families are correct, but only one side of the pair/triple comparison or only a restricted world was closed.  State the exact missing map.

### Outcome C — REPRESENTATION COLLAPSE / NO USEFUL BOUND

The attempted signed CRT abstraction is redundant, incorrectly directed for the provider, or fails to give a usable finite comparison.  Preserve any correct transport lemmas and stop without adding a false escape claim.

---

## 13. Research interpretation

This checkpoint is not expected to prove Goldbach.

Its purpose is to answer a narrower structural question:

> Can the full local `±n` obstruction geometry be represented as a finite deduplicated CRT residue family whose pair/triple seat counts feed the existing Pascal overlap payment without center-alignment?

A successful result moves the project from the special primorial-like `30` world to arbitrary finite prime worlds.  The mixed `n=50`, `P=7` regression is intentionally chosen so that exact overlap accounting can succeed while the coarse capacity budget still fails; this distinguishes a genuine structural generalization from an accidental proof-by-example.
