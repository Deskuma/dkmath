# Instruction 003 — Prime Reappearance / Cyclotomic Layer Aliasing Ultra exploration

## Mission

Study why different cyclotomic layers can expose the same rational prime even when adjacent degree layers are formally disjoint.

Instruction 002 established:

- adjacent GN values are coprime in primitive coordinates;
- adjacent unit-anchor kernel polynomials are Bézout coprime;
- adjacent nontrivial cyclotomic divisor-index sets are disjoint;
- nevertheless, a rational prime can reappear at a later degree;
- successor freshness is weaker than global primitive-prime freshness.

Calibration example:

    GN_5(1,1) = 31
    GN_6(1,1) = 63 = 3^2 * 7
    Phi_2(2) = 3
    Phi_3(2) = 7
    Phi_6(2) = 3.

Thus the formal cyclotomic layer changes completely from degree 5 to 6, while the rational prime 3 reappears in a different cyclotomic layer.

The goal is to classify this reappearance mechanism as far as the current formal stack honestly permits.

Do not assume a moire law in advance. Determine whether a precise multiplicative-order / prime-power addressing law exists.

## Phase 1 — define and audit prime layer addresses

For fixed integers or naturals a,b and a rational prime q, consider the informal address set

    L_q(a,b) = { n > 1 | q divides Phi_n(a,b) }.

Choose the mathematically natural existing homogeneous cyclotomic API if one exists. Do not introduce a duplicate cyclotomic-value formalism unnecessarily.

If an explicit set definition is useful and reusable, place it under a neutral number-theory namespace.

Record precisely the hypotheses needed for meaningful multiplicative-order statements, especially conditions such as:

    q prime
    q ∤ a
    q ∤ b
    gcd(a,b)=1.

Separate the cases q | n and q ∤ n whenever the mathematics requires it.

## Phase 2 — multiplicative order as first address

Investigate the exact relationship between

    q | a^n - b^n

and the multiplicative order of a / b modulo q.

Prefer a formulation avoiding field fractions if the current API naturally works with a * b^(-1) in (ZMod q)^× or an equivalent unit-group element.

Target the strongest honest theorem of the form

    q | a^n - b^n  <->  ord_q(a/b) | n

under the correct nonvanishing hypotheses.

Then determine when

    q | Phi_n(a,b)

forces

    n = ord_q(a/b)

and when prime-power multiples of the order are possible.

Do not conflate divisibility of a^n-b^n with divisibility of one specific cyclotomic layer.

## Phase 3 — classify prime reappearance

Primary research target:

> For fixed q, classify the degrees n for which q | Phi_n(a,b).

Test the expected pattern that, away from exceptional / ramified cases, the first layer is controlled by

    r = ord_q(a/b)

and later appearances are constrained to degrees of the form

    r * q^k.

Do not state this as a theorem until every side condition is identified.

In particular, distinguish:

- q ∤ n;
- q | n;
- q = 2;
- possible failures caused by q | a*b;
- possible repeated-root / characteristic effects.

If the exact classical statement already exists in Mathlib or DkMath, audit and reuse it. Otherwise prove only the bounded neutral theorem that the current API supports.

## Phase 4 — valuation profile across layers

Divisibility alone loses multiplicity information. Audit and, where feasible, formalize

    v_q(Phi_n(a,b)).

Questions:

- When does a reappearing prime have valuation exactly 1?
- When can the same layer carry q^2 or higher?
- How does the valuation change along a possible sequence r, r*q, r*q^2, ...?
- Which parts follow from LTE-style statements already available in DkMath or Mathlib?
- Which parts require extra ramification hypotheses?

Keep separate:

    prime reappears in a layer

from

    prime appears with first-order load 1.

Use the existing checked example GN_3(2,3)=49 as a reminder that primitive does not imply valuation 1.

## Phase 5 — first appearance versus successor freshness

Instruction 002 proved that in primitive positive coordinates some prime divides GN_(d+1) and does not divide GN_d. This is only freshness relative to the immediately previous degree.

Define or audit a precise first-appearance notion: q appears first at n means q divides the relevant layer at degree n and did not appear at any positive lower degree.

Determine whether existing DkMath.Zsigmondy.PrimitivePrimeDivisor is exactly this notion for a^n-b^n, or differs from the cyclotomic-layer address notion.

Build theorem-level bridges where they are honest.

The degree-6 calibration must remain visible:

    3 and 7 are fresh relative to degree 5,
    but neither is globally new at degree 6.

Do not weaken this distinction.

## Phase 6 — Zsigmondy reinterpretation

Only after the addressing law is stable, revisit the existing DkMath Zsigmondy / primitive-prime results.

Research question:

> Can a primitive prime divisor at degree n be characterized as a prime whose cyclotomic address set has first element n?

If yes, prove the bridge under the correct hypotheses. If only one direction is currently formalizable, state that direction and record the missing converse.

Audit the exact range of existing checked existence theorems and their exceptions. Do not silently promote a sufficient condition to a necessary one.

Do not import an unformalized full Bang–Zsigmondy theorem into the conclusion.

## Phase 7 — layer aliasing as a map

The conceptual target is not a metaphor but a precise many-to-one map:

    cyclotomic layer index -> rational prime support.

Investigate whether the following can be made mathematically precise:

- formal cyclotomic layers at adjacent degrees are disjoint;
- distinct layers can map to the same rational prime;
- multiplicative order selects a fundamental address;
- prime powers in the degree may generate later aliases / echoes.

If this succeeds, characterize the failure of injectivity explicitly.

Do not identify this with FLT unit gauge or ramifier normalization.

## Phase 8 — bounded moire interpretation

Only after the previous phases are checked, assess whether the term moire can be given a mathematically disciplined meaning.

A possible interpretation to test is:

    for each rational prime q,
    its allowed cyclotomic layer addresses form a sparse arithmetic ray;
    superposing these rays across q creates a recurring support pattern
    along the degree axis.

If the actual theorem differs, use the theorem rather than the metaphor.

Do not claim periodicity if the address sets are multiplicative rather than periodic.

Do not introduce geometry, magic squares, or FLT unless the current arithmetic classification itself forces such a connection.

## Possible outcomes

### Outcome A — classified reappearance law

The cyclotomic address set of a rational prime is classified, up to explicit small/ramified exceptions, by multiplicative order and prime-power degree inflation. Primitive-prime first appearance and later reappearance admit a checked common framework.

### Outcome B — strong partial classification

Multiplicative order controls the main behavior and several reappearance / valuation cases are formalized, but a complete address-set classification still requires additional results or exception handling.

### Outcome C — current formal frontier

The source audit yields useful local bridges and calibrations, but the current Mathlib/DkMath stack is insufficient for a meaningful general address law without importing major new arithmetic machinery.

All three outcomes are acceptable.

## Implementation guidance

Prefer reusable neutral theorems in existing number-theory / Zsigmondy / GapFocusing namespaces.

Avoid:

- theorem names using aliasing, echo, or moire when the formal statement is only ordinary divisibility;
- brute-force finite computation presented as a general classification;
- identifying homogeneous cyclotomic values by matching norms only;
- assuming valuation 1 from primitiveness;
- assuming every degree has a globally new prime;
- production dependencies on existing research endpoints carrying sorryAx.

Small calibration theorems are encouraged for:

- Phi_2(2)=3;
- Phi_6(2)=3;
- the degree-6 absence of a globally primitive prime;
- a positive primitive-prime example;
- a valuation-greater-than-one primitive example if already supported.

## Durable checkpoint protocol

Update findings continuously.

Checkpoint after:

- source / API inventory;
- multiplicative-order bridge;
- first-address theorem;
- reappearance classification attempt;
- valuation analysis;
- Zsigmondy bridge;
- A/B/C decision;
- any discovered counterexample that changes the expected address law.

If the run is interrupted, preserve exact theorem names, assumptions, failed candidate statements, and the next mathematical obligation.

## Minimum final report

Answer:

1. What is the exact formal object corresponding to a prime's cyclotomic layer addresses?
2. How does multiplicative order determine first appearance?
3. Under what conditions can the same rational prime reappear in another cyclotomic layer?
4. Are later appearances constrained to r*q^k?
5. What controls v_q(Phi_n(a,b)) at first and later appearances?
6. How does this differ from Instruction 002 successor freshness?
7. How precisely does the existing Zsigmondy primitive-prime notion fit the address picture?
8. Is there now a theorem-level object deserving the interpretation cyclotomic layer aliasing?

Finish with Outcome A, B, or C and list interpretive claims separately from Lean-checked results.