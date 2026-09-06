# ROADMAP — ABC–GN Astra Campaign 260906 v0

## 0. Campaign objective

Re-open the remaining ABC–GN large-boundary frontier using the strongest
post-Ultra DkMath machinery.

The central strategic change is:

```text
OLD tempting target
  "GN-Wieferich / deep lift cannot happen"

NEW target
  "deep repeated GN mass cannot coexist uniformly with the ABC
   radical/quality geometry without paying a compensating cost"
```

Finite Hensel lifting shows that deep local lifts can exist, so the campaign
must search for **coupling, paired-orientation sparsity, or descent**, not for a
false universal NoLift statement.

## 1. Fixed facts from the existing ABC–GN spine

The following are treated as completed infrastructure, not new research goals.

### 1.1 Exact ABC arithmetic identities

For a coprime positive ABC triple, DkMath already has the exact radical and
square-tail accounting that leads to the intrinsic ABC coordinate
`abcEpsilon`, with

```text
quality = 1 + abcEpsilon.
```

### 1.2 GN lift and non-exceptional channel

The odd-prime GN power-lift route already separates:

- original radical support,
- fresh non-exceptional support,
- exceptional exponent support,
- valuation multiplicity.

For odd-prime exponent, exceptional valuation excess has already been
eliminated.

### 1.3 Joint-pressure frontier

The remaining fresh-support plus non-exceptional-depth mass has an exact joint
form. The uniform joint contract is equivalent to a raw ABC bound.

Therefore:

```text
DO NOT:
  merely rename the joint contract,
  assume a uniform provider,
  or count such a repackaging as progress.
```

### 1.4 Exact large-boundary object

For one target profile, the large CRT modulus is exactly the complete repeated
prime-power part of the non-exceptional GN factor.

Its support equals the non-exceptional GN-Wieferich prime set.

## 2. Post-July new weapons

The degree-three GN prime-closure campaign added:

1. primitive cubic prime-shell constraints,
2. non-ramified derivative exclusion,
3. unique one-step Hensel lifting,
4. arbitrary finite-depth unique correction digits,
5. stability of derivative nondegeneracy along the lifted branch.

Consequences for ABC strategy:

- deep cubic lifts are structured, not mysterious;
- deep cubic lifts are not automatically impossible;
- repeated mass can now be studied by its local address digits;
- cubic orientation should be exploited as a two-channel geometry rather than
  as a simple `T ∨ T.swap` case split.

## 3. Phase A — falsification-first reconnaissance

### ASTRA-000 — workspace and theorem-surface audit

Status: active via `instruction-000.md`.

Objectives:

- confirm all theorem names and dependency directions in current `develop`,
- reconstruct the exact large-profile weight definitions,
- verify the two new algebraic candidates below,
- search for counterexamples before creating production declarations.

Stop condition:

- produce `report-000.md` with proven facts, failed hypotheses,
  counterexamples, and recommended next checkpoint.

## 4. Phase B — cubic orientation arithmetic

### ASTRA-001 — orientation gcd / repeated-support separation

Let

```text
F = GN 3 a b
G = GN 3 b a.
```

Candidate integer identities:

```text
(3*b - 9*a) * F + (3*a + 5*b) * G = 14*b^3
(3*a - 9*b) * G + (3*b + 5*a) * F = 14*a^3
```

Target chain:

```text
Nat.Coprime a b
  ↓
gcd(F,G) ∣ 14
  ↓
no prime square divides both F and G
  ↓
repeated supports of the two cubic orientations are disjoint
  ↓
GN-Wieferich repeated supports are disjoint
```

Mandatory regression / falsification point:

```text
a = 605
b = 370688
c = 371293
```

Expected phenomenon:

- both cubic orientations have repeated prime powers,
- but their repeated-prime sets differ.

This regression prevents the false theorem "one orientation is squarefree".

Go gate:

- only continue if the exact disjointness theorem survives Lean and numerical
  tests.

## 5. Phase C — cubic-specific boundary exponent

### ASTRA-002 — replace the generic 3/4 diagnosis by a cubic endpoint

Current generic target-level estimate uses the general odd-prime order bound
and reaches a `3/4` exponent.

For `p = 3`:

```text
active q prime
q % 3 = 1
  ↓
q >= 7
  ↓
2^8 <= q^3
  ↓
2 <= q^(3/8)
```

Per active prime of depth `k >= 2`, this suggests

```text
2 * q^((3/8)*(k-1)) <= q^((3/8)*k).
```

Target theorem shape:

```text
cubicBoundaryWeight(3/8)
  <= (GNNonExceptionalRepeatedPart 3 a b)^(3/8).
```

A safer intermediate checkpoint may first prove the `1/2` endpoint, then
sharpen to `3/8`.

Go gate:

- the theorem must be derived from the current actual mass/address definitions,
  not from an invented surrogate weight.

## 6. Phase D — small-profile compatibility

### ASTRA-003 — cubic `t = 3/8` Euler / small-boundary audit

The existing half-weight local depth decay becomes stronger, not weaker, if the
weight parameter is reduced from `1/2` to `3/8`.

Investigate whether the present finite Euler-product machinery can be
specialized with minimal changes.

Desired result:

```text
small profiles:
  summable with t = 3/8

large target profile:
  repeated-modulus cost exponent 3/8
```

Stop condition:

- if changing the parameter requires rebuilding the old probabilistic tower
  with no new mathematical gain, do not proceed mechanically. Re-evaluate the
  paired-orientation route first.

## 7. Phase E — paired orientation CRT geometry

### ASTRA-004 — paired bad-profile density

Fix `c = a + b`. View both cubic orientations as functions of the same
moving coordinate.

Potential goal:

```text
orientation A repeated modulus M_A
orientation B repeated modulus M_B

repeated-support disjointness
  ↓
Nat.Coprime M_A M_B
  ↓
simultaneous badness pays modulus M_A * M_B
```

This is the first genuinely new possible route to a global gain.

Questions to answer experimentally:

- Does simultaneous badness occur often?
- Can both moduli be large at once?
- Does the fixed-sum relation impose an extra congruence incompatibility?
- Does Hensel uniqueness make paired addresses sparse?
- Is there a clean finite CRT fiber bound?

No global theorem should be guessed before numerical and Lean scratch tests.

## 8. Phase F — ABC quality coupling

### ASTRA-005 — connect paired repeated debt to `abcEpsilon`

Only enter this phase after a real paired-orientation gain exists.

Possible target forms:

```text
large abcEpsilon
  -> large bad mass in at least one orientation

or stronger:

large abcEpsilon
  -> simultaneous structured badness in both orientations
```

Then combine with the paired-profile sparsity/CRT result.

Alternative output:

- if the structure naturally maps a bad triple to a strictly smaller bad
  triple, switch to a well-founded descent route instead of forcing a sum
  estimate.

## 9. Phase G — endpoint discipline

The campaign reaches an ABC endpoint only if a theorem is produced that removes
the need for the axiom-backed final receiver.

Until then:

```text
abc_main_axiom remains outside the proof route.
No "ABC proved" statement.
No theorem alias may hide a research assumption.
```

If the campaign closes only a stronger local or paired-profile theorem, record
that theorem as the actual result and stop there.

## 10. Preferred workflow with Astra/Codex

Every checkpoint should follow:

```text
current-source audit
  ↓
mathematical reconstruction
  ↓
counterexample search
  ↓
Lean scratch theorem
  ↓
production theorem only after survival
  ↓
report with explicit remaining obstruction
```

Use the model as a field mathematician:

- inspect the workspace,
- query theorem surfaces,
- build scratch Lean files,
- run exact arithmetic experiments,
- deliberately search for counterexamples,
- report dead ends quickly.

Avoid long chains of bookkeeping checkpoints unless each one removes a
mathematically meaningful obstruction.
