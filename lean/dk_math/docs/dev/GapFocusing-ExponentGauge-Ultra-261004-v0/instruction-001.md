# Instruction 001 — Gap focusing / exponent gauge Ultra exploration

## Mission

Audit the DkMath source and formalize only what is necessary to answer:

> Does the change
> `a=x+u, b=u`
> merely rewrite `a^d-b^d`, or does it canonically separate a pure Gap
> direction from the residual cyclotomic/exponent structure?

The central object is

```text
(x+u)^d - u^d = x * GN_d(x,u).
```

The run must separate:

- exact algebra already proved in DkMath/Mathlib;
- new Lean-checkable structural statements;
- interpretive conjectures that remain unproved.

## Phase 1 — source inventory

Locate current production theorems for:

- the generic Cosmic Formula / GN identity;
- product-degree composition, especially the existing `GN_{ab}` theorem;
- difference-of-powers and cyclotomic factorization;
- primitive-root / phase factorization;
- current neutral APIs involving `1-zeta`, geometric sums, and cyclotomic units;
- the merged FLT3/5/7 normalization-fixed unit-power audit.

Record exact theorem names and typed rings.  Do not bridge different carriers
by matching scalar norms.

## Phase 2 — focused versus unfocused Gap

Study the identities

```text
a^d-b^d
(x+u)^d-u^d
(x+u)^d-v^d.
```

The key candidate remainder formula is

```text
(x+u)^d-v^d
  = x*GN_d(x,u) + (u^d-v^d).
```

Determine in the relevant polynomial setting whether the exact divisibility
criterion

```text
x divides ((x+u)^d-v^d)
iff
u^d = v^d
```

is already available or can be proved neutrally.

Interpretation to test:

```text
u^d-v^d = focus defect.
```

Do not call it an invariant unless its transformation behavior is explicitly
checked.

## Phase 3 — cyclotomic phase focus

Audit the factorization

```text
(x+u)^d-u^d
  = product_{zeta^d=1} (x + (1-zeta)u).
```

Determine exactly in which rings and hypotheses this can be stated.

Test the claim that the trivial phase `zeta=1` is the unique phase whose
factor loses all u-dependence and becomes exactly x.

For nontrivial phases retain

```text
x + (1-zeta)u.
```

Do not confuse this phase decomposition with the later FLT unit class.

## Phase 4 — composite degree versus prime degree

Use the existing GN product-degree theorem, expected in the form

```text
GN_{ab}(x,u)
  = GN_a(x,u) * GN_b(x*GN_a(x,u), u^a).
```

Map this against the divisor lattice / cyclotomic factorization of degree d.

Research target:

> composite d has a nontrivial lower-degree route whenever d=ab with a,b>1;
> prime p has no such degree factorization.

Decide whether an honest Lean theorem such as a "Prime Degree Rigidity"
criterion can be stated without merely restating `Nat.Prime p`.

A useful theorem should say something structural about the absence/presence of
nontrivial GN degree decompositions, divisor layers, or cyclotomic subperiods.

If the only honest result is an equivalence to primality, say so clearly.

## Phase 5 — connection to the FLT3/5/7 unit gauge

The merged audit established, after fixed ramifier/power extraction,

```text
[u] in R^×/(R^×)^p
```

as root-choice independent but normalization dependent.

Test whether there is any theorem-level bridge from focused cyclotomic phase
freedom to that residual unit-power class.

Questions:

- Is the unit class simply the algebraic remainder of phase normalization?
- Does an explicit cyclotomic unit such as a geometric sum provide the bridge?
- Or does the unit class only appear after additional ideal/principalization
  data, making it a genuinely later arithmetic layer?

Do not force an identification.  Outcome B is expected if extra arithmetic
data is essential.

## Phase 6 — 2p calibration

Analyze degree `2p` only after the previous phases are stable.

Because `2p=p*2`, inspect the actual GN composition in both orders if useful:

```text
p then 2
2 then p.
```

Determine what algebraically differs between these decompositions and what
data would be required before interpreting `2p` geometrically as a planar
lifting of p.

The separately observed magic-square/plane `2p` phenomenon is a motivation,
not an assumption.  Do not claim the connection unless a precise object map is
found.

## Durable checkpoint protocol

Update `findings-001.md` continuously.

Checkpoint after:

- source inventory;
- focused/unfocused divisibility result;
- cyclotomic phase analysis;
- prime/composite degree analysis;
- attempted unit-gauge bridge;
- 2p calibration;
- any failed unification that changes the research direction.

A partial but precise result is preferable to an unrecorded long search.

## Deliverable

Produce a bounded report answering:

1. What is mathematically canonical in Gap focusing?
2. What information is hidden, cancelled, or retained in GN?
3. Is prime degree structurally rigid beyond the definition of primality?
4. Does the FLT unit gauge descend from phase focusing, or sit in a later layer?
5. What exactly does degree 2p mean algebraically?
6. Which claims remain interpretation rather than Lean-checked mathematics?

Use Outcome A/B/C from README as the final classification.
