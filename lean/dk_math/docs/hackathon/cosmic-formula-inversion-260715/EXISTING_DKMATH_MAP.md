# Existing DkMath Map

## DkMath — Cosmic Formula Inversion

This document records the existing DkMath and Mathlib declarations that may support the hackathon theorem surface.

Its purpose is to prevent:

- duplicate definitions;
- duplicate proofs;
- unnecessary imports;
- incorrect theorem reuse;
- parallel Big / Body / Gap structures;
- avoidable Codex exploration in later checkpoints.

This file begins as an audit framework.

The first Codex session must update it with exact module paths, declaration names, theorem statements, and reuse classifications.

Codex must not edit Lean source files during that audit.

---

## 1. Current Status

```text
DOCUMENT STATUS:
  PRE-AUDIT SCAFFOLD

LEAN SOURCE AUDIT:
  NOT STARTED

CURRENT AUTHORITY:
  MATHEMATICAL_CONTRACT.md
  ARCHITECTURE.md
  DECISIONS.md
  RISKS_AND_STOPPING_RULES.md

NEXT REQUIRED ACTION:
  repository-audit-only Codex session
```

No declaration listed as a candidate in this document is considered reusable until its exact type has been inspected.

---

## 2. Audit Objective

The audit must determine the smallest existing theorem path for:

```text
finite prime set S
→ product P
→ Coprime P u
→ prime divisor q of P + u
→ q ∉ S
→ fresh prime-factor existence
→ Cosmic Formula completion
→ concrete Demo.lean
```

The stronger audit should also locate candidate APIs for:

```text
bounded rational projection
exact inverse
normalized Body / Gap conservation
DkReal nested intervals
interval-width transport
unique integer candidate
```

The audit must distinguish:

```text
what already exists
what only needs a wrapper
what requires a small corollary
what requires a genuine bridge
what is absent
what is semantically unsuitable
```

---

## 3. Reuse Classification

Every audited declaration must receive exactly one primary classification.

### `DIRECT`

Use the existing declaration without a new theorem.

```text
Meaning:
  exact required statement already exists

Expected action:
  import and apply directly
```

### `WRAPPER`

Expose an existing declaration under a stable hackathon-facing theorem name.

```text
Meaning:
  mathematical content already exists
  public theorem surface needs a clearer specialization or name

Expected action:
  add a thin theorem wrapper
```

### `COROLLARY`

Derive the requested result through a small amount of local reasoning.

```text
Meaning:
  all substantial mathematics already exists

Expected action:
  prove a short theorem from existing declarations
```

### `BRIDGE`

Translate between two existing representations or APIs.

```text
Examples:
  Finset product ↔ existing product wrapper
  Nat identity ↔ existing Cosmic Formula structure
  rational projection ↔ DkReal interval representation
```

### `MISSING`

No suitable existing declaration was found.

```text
Expected action:
  state the smallest proposed missing theorem
  do not implement it during the audit
```

### `REJECTED`

A related declaration exists but does not match the contract.

```text
Examples:
  primitive prime divisor instead of finite-set freshness
  incompatible number domain
  sequence-relative result
  theorem with materially different hypotheses
```

### `DANGEROUS`

The declaration is mathematically relevant but architecturally unsuitable.

```text
Examples:
  creates reverse dependency
  imports a very large unrelated branch
  depends on unverified experimental infrastructure
  would force a core DkMath refactor
```

### `DEMO_ONLY`

A concrete fact should be proved locally with automation.

```text
Examples:
  221 = 13 * 17
  Nat.Coprime 210 11
  13 ∉ {2, 3, 5, 7}
```

---

## 4. Audit Record Format

Each confirmed declaration should be recorded in this form.

````md
### MAP-XXX — Concept Name

```text
Status:
  CONFIRMED / PARTIAL / NOT FOUND / REJECTED

Classification:
  DIRECT / WRAPPER / COROLLARY / BRIDGE / MISSING / REJECTED / DANGEROUS

Module:
  DkMath.Example.Module

Declaration:
  exactDeclarationName

Domain:
  ℕ / ℤ / ℚ / ℝ / DkReal / generic

Exact Type:
  copied or accurately normalized theorem statement

Required Hypotheses:
  list

Produced Conclusion:
  list

Intended Hackathon Use:
  description

Import Cost:
  narrow / moderate / broad

Dependency Risk:
  none / low / medium / high

Notes:
  semantic boundary, coercion issue, or proof strategy

Decision:
  use directly / wrap / derive / reject / defer
```
````

Exact theorem types should be copied accurately enough that a later Codex checkpoint does not need to repeat the same search.

---

## 5. Search Sources

The repository audit should use sources in this order.

```text
1. exact theorem-name and concept search in Lean source
2. __theorems-heading.txt
3. __dkmath-all.lean.txt.gz through zgrep / zcat
4. summary reports in __summary_report_data.tar.gz
5. direct module inspection
6. Mathlib source inspection when DkMath has no suitable theorem
```

The audit should read the project-level repository instructions before searching:

```text
README.md
AGENT.md
SUMMARY.md
```

UUID-named empty tracking anchors must not be repeatedly inspected.

---

## 6. Search Rules

Codex must search by both standard mathematics vocabulary and DkMath vocabulary.

Example:

```text
standard search:
  prime divisor
  Finset product
  Coprime
  not_mem
  exists_prime_and_dvd
  interval width
  injective
  left inverse

DkMath search:
  Big
  Body
  Gap
  GN
  CosmicFormula
  Projection
  DkReal
  GapInterval
  NoLift
  primitive
  fresh
```

A name match is not sufficient.

Codex must inspect:

```text
domain
hypotheses
conclusion
namespace
import path
dependency direction
```

---

## 7. Required Discrete Arithmetic Map

### MAP-001 — Finite Prime Set Representation

```text
Audit Status:
  TO AUDIT

Required Concept:
  S : Finset ℕ

Required Hypothesis:
  ∀ p ∈ S, Nat.Prime p

Expected Source:
  Mathlib Finset and Nat.Prime APIs
  possible DkMath finite-prime wrappers

Questions:
  Is there an existing DkMath structure for a finite prime family?
  Is a plain Finset sufficient?
  Would an existing wrapper increase import or coercion cost?
  Does a reusable theorem already expect a Finset of primes?

Preferred Outcome:
  use Finset ℕ directly unless a clearly superior existing API exists

Prohibited Outcome:
  create a new foundational finite-prime-set structure only for the demo
```

---

### MAP-002 — Finset Product of Prime Members

```text
Audit Status:
  TO AUDIT

Required Expression:
  ∏ p ∈ S, p

Required Fact:
  q ∈ S → q ∣ ∏ p ∈ S, p

Likely Source:
  Mathlib Finset product divisibility

Search Terms:
  Finset.dvd_prod_of_mem
  dvd_prod
  mem.*dvd.*prod
  prime_mem_dvd_product

Questions:
  What exact binder form is most compatible?
  Is the product written as S.prod id?
  Is a two-binder product unnecessarily duplicating the same set?
  Does DkMath already expose a specialized theorem?

Preferred Classification:
  DIRECT or WRAPPER
```

---

### MAP-003 — Product Positivity

```text
Audit Status:
  TO AUDIT

Potential Requirement:
  0 < P

Possible Derivation:
  all primes in S are positive
  finite product of positive values is positive

Questions:
  Is positivity required by the arithmetic theorem?
  Is it only required by projection or visualization?
  Does empty S already give P = 1 and positivity automatically?

Preferred Outcome:
  do not add nonempty S if product positivity already holds for the empty product
```

---

### MAP-004 — Coprimality API

```text
Audit Status:
  TO AUDIT

Required Concept:
  Nat.Coprime P u

Equivalent Form:
  Nat.gcd P u = 1

Likely Source:
  Mathlib Nat gcd / Coprime APIs
  possible DkMath coprime-product bridges

Search Terms:
  Nat.Coprime
  coprime_prod
  gcd_eq_one
  dvd_gcd
  Coprime.dvd_of_dvd_mul_left
  Coprime.not_dvd_of_dvd

Questions:
  Which theorem most directly excludes q dividing both P and u?
  Is there an existing DkMath theorem for a product coprime to an offset?
  Is the project better stated through Nat.Coprime rather than gcd equality?

Preferred Outcome:
  public theorem uses Nat.Coprime
```

---

### MAP-005 — Divisor of `P + u` and `P` Divides `u`

```text
Audit Status:
  TO AUDIT

Required Local Fact:
  q ∣ P
  q ∣ P + u
  → q ∣ u

Possible Proof Routes:
  Nat.dvd_add_iff_left
  Nat.dvd_add_right
  modular congruence
  integer subtraction bridge
  exact divisibility algebra

Search Terms:
  dvd_add_iff
  dvd_add_iff_left
  dvd_add_iff_right
  dvd_sub
  add_sub_cancel_left
  Nat.ModEq

Questions:
  Can this remain entirely in Nat without truncated subtraction?
  Is a ModEq proof cleaner?
  Is there already a DkMath bridge theorem?

Preferred Classification:
  DIRECT or COROLLARY

Avoid:
  unnecessary conversion to Int unless Nat APIs are genuinely awkward
```

---

### MAP-006 — Coprimality Excludes a Prime Dividing Both Inputs

```text
Audit Status:
  TO AUDIT

Required Fact:
  Nat.Coprime P u
  q ∣ P
  q ∣ u
  Nat.Prime q
  → False

Equivalent Routes:
  q ∣ gcd P u
  gcd P u = 1
  prime q cannot divide 1

Search Terms:
  Coprime
  dvd_gcd
  Prime.not_dvd_one
  Nat.dvd_one
  coprime_iff_gcd_eq_one

Preferred Classification:
  DIRECT or COROLLARY
```

---

### MAP-007 — Supplied Prime Divisor Is Fresh

```text
Audit Status:
  TO AUDIT

Required Theorem Meaning:
  q is prime
  q ∣ P + u
  P = product S
  Coprime P u
  → q ∉ S

Target Module:
  DkMath.Hackathon.FinitePrimeEscape

Potential Existing DkMath Areas:
  finite prime products
  Euclid-style prime escape
  primitive-set APIs
  BezoutBridge
  coprime product theorems

Search Terms:
  forall_not_dvd
  coprime_prod_primes
  not_mem.*prime.*dvd
  freshPrime
  FreshPrimeFactor
  prime_dvd_add
  product_add
  Euclid
  escape

Classification Goal:
  DIRECT, WRAPPER, or COROLLARY

If Missing:
  proposed theorem should remain small and Nat-specific
```

---

### MAP-008 — Existence of a Prime Divisor

```text
Audit Status:
  TO AUDIT

Required Fact:
  1 < n → ∃ q, Nat.Prime q ∧ q ∣ n

Likely Source:
  Mathlib Nat prime-divisor API

Search Terms:
  exists_prime_and_dvd
  exists_prime_dvd
  minFac
  prime_minFac
  prime_dvd_iff

Questions:
  What is the shortest proposition-valued existence theorem?
  Does it require n ≠ 1 rather than 1 < n?
  Does it expose an explicit minFac witness?
  Is classical reasoning involved?

Preferred Classification:
  DIRECT
```

---

### MAP-009 — Existence of a Fresh Prime Factor

```text
Audit Status:
  TO AUDIT

Required Theorem:
  1 < P + u
  Nat.Coprime P u
  P = product S
  all members of S prime
  →
  ∃ q, Nat.Prime q ∧ q ∣ P + u ∧ q ∉ S

Expected Construction:
  prime-divisor existence
  +
  supplied-divisor freshness

Preferred Classification:
  COROLLARY or WRAPPER

Questions:
  Is primality of every member of S logically required for exclusion?
  Is it required only to justify the phrase finite prime set?
  Can a stronger theorem exclude every member q of S when each q > 1?
```

---

### MAP-010 — Universal Freshness of All Prime Divisors

```text
Audit Status:
  TO AUDIT

Required Meaning:
  ∀ q, Nat.Prime q → q ∣ P + u → q ∉ S

Expected Use:
  prove both 13 and 17 fresh through one general API

Preferred Classification:
  WRAPPER or COROLLARY

Meaning Boundary:
  does not state uniqueness
  does not state every outside prime divides P + u
```

---

## 8. Freshness and Primitive-Factor Map

### MAP-011 — Existing `FreshPrimeFactor` Predicate

```text
Audit Status:
  TO AUDIT

Required Predicate Meaning:
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S

Search Terms:
  FreshPrimeFactor
  freshPrime
  outsidePrime
  prime_not_mem
  newPrimeFactor

Questions:
  Does an exact predicate already exist?
  Is it specialized to a sequence or primitive divisor?
  Does it use Set rather than Finset?
  Does it include multiplicity or valuation data?

Decision Rule:
  use an existing predicate only if its semantics match exactly

If Not Found:
  a small hackathon-local predicate may be proposed
```

---

### MAP-012 — Primitive Prime Divisor APIs

```text
Audit Status:
  TO AUDIT FOR REJECTION OR OPTIONAL REUSE

Potential DkMath Areas:
  PrimitiveSet
  Petal
  BezoutBridge
  ErdosBridge
  Zsigmondy-related modules
  primitive-factor APIs

Purpose of Audit:
  determine whether any theorem specializes cleanly to finite-set freshness

Required Caution:
  sequence-relative primitiveness is stronger and semantically different

Likely Classification:
  REJECTED for public terminology
  possibly DIRECT or COROLLARY for an internal proof only if exact hypotheses align

Prohibited Action:
  rename the finite escape theorem as primitive merely because a primitive API is reused
```

---

### MAP-013 — Finite Prime Universe Existing Structure

```text
Audit Status:
  TO AUDIT

Required Decision:
  documentation-only term
  or existing formal DkMath object

Search Terms:
  PrimeUniverse
  FinitePrimeUniverse
  PrimeWorld
  PrimitiveSet
  PrimeFamily
  Finset prime product

Preferred Outcome:
  retain as project terminology unless an exact existing object is clearly useful

Avoid:
  introducing a formal universe structure for the MVP
```

---

## 9. Cosmic Formula Map

### MAP-014 — Core Cosmic Formula Module Family

```text
Audit Status:
  TO AUDIT

Known Conceptual Target:
  Big = Body + Gap

Candidate Module Families:
  DkMath.CosmicFormula.*
  other DkMath algebraic split modules

Search Terms:
  CosmicFormula
  Big
  Body
  Gap
  body_add_gap
  big_eq
  CoreBeamGap
  Residual
  Split

Required Audit Output:
  exact module names
  primary structures
  number domains
  relevant theorem names
  import relationships
```

---

### MAP-015 — Square Completion Identity

```text
Audit Status:
  TO AUDIT

Required Theorem:
  P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2

Search Terms:
  square
  add_sq
  pow_two
  cosmic
  body gap
  Gnomon
  completion

Preferred Reuse Order:
  DIRECT existing theorem
  WRAPPER specialization
  COROLLARY from generic Cosmic Formula
  local ring proof

Acceptable Fallback:
  theorem proved by ring

Meaning Boundary:
  arithmetic equality only
  no formal Euclidean dissection required
```

---

### MAP-016 — Existing Big Definition

```text
Audit Status:
  TO AUDIT

Required Intended Value:
  (P + u) ^ 2

Questions:
  Does DkMath define Big as a field of a structure?
  Is Big generic over exponent d?
  Is the square case directly available?
  Is the domain Nat, Int, or a semiring?
  Would reuse obscure the public theorem?

Decision Possibilities:
  DIRECT
  WRAPPER
  REJECTED for the facade while retaining the algebraic theorem
```

---

### MAP-017 — Existing Body Definition

```text
Audit Status:
  TO AUDIT

Required Intended Value:
  P * (P + 2 * u)

Questions:
  Is Body represented as Big - Gap?
  Is there a subtraction-free Nat theorem?
  Does an existing generic power-difference Body specialize to d = 2?
  Is GN used internally?

Preferred Public Form:
  additive equality in Nat
```

---

### MAP-018 — Existing Gap Definition

```text
Audit Status:
  TO AUDIT

Required Intended Value:
  u ^ 2

Questions:
  Is Gap generic as u ^ d?
  Is there an existing UnitKernel or GapKernel?
  Does the existing type require a structure wrapper?

Meaning Boundary:
  square Gap is not the normalized linear Gap coordinate
```

---

### MAP-019 — Generic Exponent Cosmic Formula

```text
Audit Status:
  TO AUDIT

Potential Generic Identity:
  (x + u) ^ d = Body_d(x, u) + u ^ d

Potential DkMath Relation:
  GN
  binomial expansion
  Body / Gap split
  Gnomon band

Purpose:
  determine whether the square theorem should be a specialization

Questions:
  Does specialization to d = 2 simplify cleanly?
  Would importing the generic theory materially expand the facade?
  Is a local square theorem clearer for judges?

Decision Rule:
  prefer the cleanest sound public surface, not maximal abstraction
```

---

### MAP-020 — GN Identity

```text
Audit Status:
  TO AUDIT

Known Conceptual Identity:
  (x + u) ^ d - u ^ d = x * GN_d(x, u)

Potential Square Specialization:
  GN_2(P, u) = P + 2u

Possible Use:
  bridge Body to existing GN machinery
  show Body = P * GN_2(P, u)

Questions:
  Does an exact theorem already exist?
  Is GN required by the MVP?
  Does it improve the inverse-projection story?
  Does it create an unnecessarily deep import?

Likely Outcome:
  optional COROLLARY or DEFERRED
```

---

### MAP-021 — Gnomon / GnomonBand APIs

```text
Audit Status:
  TO AUDIT

Potential Concept:
  (P + u)² - u² = P(P + 2u)

Purpose:
  visual interpretation of Body around Gap

Questions:
  Is a formal GnomonBand already implemented?
  Is it stable enough for public reuse?
  Is it only planned documentation?

Preferred MVP Outcome:
  arithmetic wrapper only
```

---

## 10. Normalized Cosmic Formula Map

### MAP-022 — Existing Normalization API

```text
Audit Status:
  TO AUDIT

Required Identity:
  P(P + 2u) / (P + u)²
  +
  u² / (P + u)²
  =
  1

Preferred Domain:
  ℚ

Search Terms:
  normalized
  normalize
  ratio
  bodyRatio
  gapRatio
  unitInterval
  conservation
  div_sq

Questions:
  Does DkMath already normalize Big to one?
  Which domain is used?
  Is denominator positivity already packaged?
```

---

### MAP-023 — Linear Gap Coordinate

```text
Audit Status:
  TO AUDIT

Candidate:
  u / (P + u)

Required Relation:
  (u / (P + u))² = u² / (P + u)²

Questions:
  Does DkMath distinguish linear Gap scale and square Gap mass?
  Is there an existing unit-coordinate abstraction?
  Are Units or SilverRatio modules relevant, or unrelated?

Decision:
  do not reuse by name alone
```

---

### MAP-024 — Normalized Body

```text
Audit Status:
  TO AUDIT

Candidate:
  P(P + 2u) / (P + u)²

Alternative Identity:
  1 - (u / (P + u))²

Questions:
  Which form is easiest to connect to existing DkMath APIs?
  Does Nat-to-rational coercion already have wrappers?
```

---

## 11. Projection Map

### MAP-025 — Existing Projection Definitions

```text
Audit Status:
  TO AUDIT

Candidate Unsigned Projection:
  P / (P + u)

Candidate Signed Projection:
  -P / (P + u)

Known Decision:
  primary convention remains deferred until audit

Search Terms:
  Projection
  inverseProjection
  normalizedCoordinate
  bounded
  unitInterval
  signed projection
  DkReal projection

Required Audit Output:
  exact existing formulas
  domains and codomains
  endpoint conventions
  inverse theorems
  DkReal compatibility
```

---

### MAP-026 — Unsigned Projection Interval Bound

```text
Audit Status:
  TO AUDIT

Required Theorem:
  0 ≤ P / (P + u) < 1

Domain:
  ℚ preferred

Hypotheses:
  P ≥ 0
  u > 0

Likely Source:
  Mathlib ordered-field division lemmas
  possible DkMath normalization API

Classification Goal:
  COROLLARY or BRIDGE
```

---

### MAP-027 — Signed Projection Interval Bound

```text
Audit Status:
  TO AUDIT

Required Theorem:
  -1 < -P / (P + u) ≤ 0

Purpose:
  compare with existing DkMath inverse-projection conventions

Classification:
  AUDIT ONLY until ADR selects a convention
```

---

### MAP-028 — Exact Unsigned Inverse

```text
Audit Status:
  TO AUDIT

Forward:
  x = P / (P + u)

Inverse:
  P = u * x / (1 - x)

Required Conditions:
  u > 0
  x in the forward image
  1 - x ≠ 0

Search Terms:
  leftInverse
  rightInverse
  injective
  fractionalLinear
  mobius
  ratio inverse

Preferred Domain:
  ℚ
```

---

### MAP-029 — Exact Signed Inverse

```text
Audit Status:
  TO AUDIT

Forward:
  x = -P / (P + u)

Inverse:
  P = -u * x / (1 + x)

Purpose:
  compare with existing DkMath interval convention

Classification:
  AUDIT ONLY until projection decision
```

---

### MAP-030 — Projection Injectivity for Fixed `u`

```text
Audit Status:
  TO AUDIT

Required Meaning:
  fixed positive u
  projection P₁ = projection P₂
  → P₁ = P₂

Possible Proof:
  exact left inverse
  monotonicity
  cross multiplication

Questions:
  Is there an existing strict monotonicity theorem?
  Is left-inverse proof shorter?
```

---

### MAP-031 — Projection Image Characterization

```text
Audit Status:
  TO AUDIT

Potential Requirement:
  characterize values attained by natural P

MVP Requirement:
  none

Preferred Milestone:
  inverse only on the image

Risk:
  accidental claim of surjectivity onto a closed interval

Likely Classification:
  DEFERRED
```

---

## 12. DkReal Map

### MAP-032 — DkReal Core Type

```text
Audit Status:
  TO AUDIT

Known Conceptual Role:
  computable or nested rational representation of real values

Candidate Module Family:
  DkMath.DkReal.*

Required Audit Output:
  exact primary type
  constructors
  coercions
  equality notion
  order instances
  interval representation
```

---

### MAP-033 — GapInterval

```text
Audit Status:
  TO AUDIT

Known Conceptual Candidate:
  nested interval or interval-gap structure

Search Terms:
  GapInterval
  nested
  width
  interval
  shrink
  zero width
  contains

Questions:
  Is GapInterval the correct public bridge?
  What are endpoint types?
  Is interval inclusion explicit?
  Is width represented directly?
```

---

### MAP-034 — Nested Interval Theorems

```text
Audit Status:
  TO AUDIT

Required Properties:
  I_{n+1} ⊆ I_n
  projected value belongs to every I_n
  widths shrink

Search Terms:
  antitone
  nested
  subset
  contains
  tendsto
  width_zero
  diameter

Classification Goal:
  DIRECT or BRIDGE
```

---

### MAP-035 — Width Definition

```text
Audit Status:
  TO AUDIT

Required Meaning:
  upper endpoint - lower endpoint

Questions:
  Does the existing interval type expose width?
  Is width in ℚ, ℝ, or NNReal?
  Are nonnegativity theorems available?
```

---

### MAP-036 — Mapping Intervals Through a Monotone Function

```text
Audit Status:
  TO AUDIT

Required Later Use:
  apply inverse projection to projected interval endpoints

Required Properties:
  monotonicity of inverse
  endpoint ordering
  image interval containment

Search Terms:
  mapInterval
  image_Icc
  monotoneOn
  intervalMap
  map_lower_upper

Potential First Genuine Obstruction:
  no compatible interval-map API
```

---

### MAP-037 — Width Transport Through Inverse Map

```text
Audit Status:
  TO AUDIT

Required Later Goal:
  bound width of inverse-mapped interval

Possible Tools:
  exact endpoint subtraction
  monotonicity
  derivative / Lipschitz bound
  rational algebra
  local denominator lower bound

Risk:
  becomes a new analysis program

Expected Classification:
  likely BRIDGE or MISSING
```

---

### MAP-038 — Width Less Than One Implies At Most One Integer

```text
Audit Status:
  TO AUDIT

Required Theorem Meaning:
  interval width < 1
  → at most one integer lies inside

Potential Sources:
  Mathlib Int floor / ceil
  interval cardinality
  order lemmas
  existing DkMath discretization bridge

Search Terms:
  unique integer
  atMostOne
  width_lt_one
  floor
  ceil
  Int.cast
  Nat.cast
  Icc integers

Classification Goal:
  DIRECT, COROLLARY, or BRIDGE
```

---

### MAP-039 — Integer Existence in an Interval

```text
Audit Status:
  TO AUDIT

Required Distinction:
  at-most-one does not imply existence

Possible Later Requirement:
  prove the original P lies in every reconstructed interval

Preferred Route:
  transport membership from the exact projected value

Questions:
  Can existence be obtained without floor / ceil?
```

---

### MAP-040 — Unique Macro-Integer Reconstruction

```text
Audit Status:
  TO AUDIT

Required Final Meaning:
  original P lies in reconstructed interval
  reconstructed interval has width < 1
  therefore P is the unique integer candidate

Expected Composition:
  membership
  +
  at-most-one integer theorem

Likely Classification:
  BRIDGE

Stretch Only:
  not required for MVP
```

---

## 13. Demo Arithmetic Map

### MAP-041 — Demo Prime Set Evaluation

```text
Audit Status:
  EXPECTED DEMO_ONLY

Required Fact:
  product {2, 3, 5, 7} = 210

Likely Proof:
  norm_num
  decide
  simp

Questions:
  Which Finset literal notation is stable and readable?
```

---

### MAP-042 — Demo Coprimality

```text
Audit Status:
  EXPECTED DEMO_ONLY

Required Fact:
  Nat.Coprime 210 11

Likely Proof:
  norm_num
  decide
```

---

### MAP-043 — Demo Boundary

```text
Audit Status:
  EXPECTED DEMO_ONLY

Required Fact:
  210 + 11 = 221

Likely Proof:
  norm_num
```

---

### MAP-044 — Demo Factorization

```text
Audit Status:
  EXPECTED DEMO_ONLY

Required Fact:
  221 = 13 * 17

Likely Proof:
  norm_num
```

---

### MAP-045 — Demo Prime Proofs

```text
Audit Status:
  EXPECTED DEMO_ONLY

Required Facts:
  Nat.Prime 13
  Nat.Prime 17

Likely Proof:
  norm_num
  decide
```

---

### MAP-046 — Demo Freshness

```text
Audit Status:
  GENERAL THEOREM REUSE REQUIRED

Required Facts:
  13 ∉ demoPrimeSet
  17 ∉ demoPrimeSet

Preferred Proof:
  use the general finite-prime escape theorem

Acceptable Supporting Automation:
  norm_num or decide for divisibility and explicit membership facts

Prohibited:
  prove all public freshness results only by deciding finite membership
```

---

### MAP-047 — Demo Cosmic Completion

```text
Audit Status:
  GENERAL THEOREM REUSE REQUIRED

Required Fact:
  210 * 232 + 11 ^ 2 = 221 ^ 2

Preferred Proof:
  apply or specialize the general Cosmic Completion theorem

Acceptable Supporting Automation:
  norm_num to normalize displayed constants
```

---

## 14. Candidate DkMath Module Families

The following module families are candidates only.

Their exact relevance must be confirmed by audit.

```text
DkMath.CosmicFormula.*
  expected relevance:
    Big / Body / Gap
    general completion identities
    GN bridges

DkMath.DkReal.*
  expected relevance:
    nested rational intervals
    width and reconstruction

DkMath.NumberTheory.*
  expected relevance:
    prime, divisibility, gcd, finite products

DkMath.Petal.*
  possible relevance:
    GN
    primitive factors
    product structures

DkMath.ABC.*
  possible relevance:
    valuation and primitive-factor bridges
  likely not required by MVP

DkMath.KUS.*
  possible relevance:
    bounded or projected coordinate systems
  must not be assumed

DkMath.Units.*
  possible relevance:
    normalization or unit-coordinate interpretation
  audit exact semantics before reuse

DkMath.SilverRatio.*
  likely unrelated to MVP
  inspect only if directly referenced by a projection API
```

Codex must not perform a full audit of every listed family.

Search should remain concept-driven.

---

## 15. Mathlib Fallback Map

When DkMath has no project-specific theorem, prefer standard Mathlib APIs.

### Finset

```text
membership
product
product divisibility
filter
image
cardinality
```

### Nat

```text
Prime
Coprime
gcd
divisibility
prime divisor existence
minFac
```

### Algebra

```text
ring
ring_nf
field_simp
nlinarith
```

### Ordered Fields

```text
division inequalities
positivity
interval membership
monotonicity
```

### Int / Floor / Ceiling

```text
integer interval bounds
at-most-one candidate
floor and ceil characterization
```

DkMath wrappers are preferred only when they add genuine project meaning or connect to later DkMath phases.

---

## 16. Import Audit Table

Codex should fill this table after locating exact declarations.

| Hackathon module | Candidate import | Required declaration | Import cost | Decision |
|---|---|---|---:|---|
| `FinitePrimeEscape.lean` | `TO AUDIT` | product-member divisibility | unknown | pending |
| `FinitePrimeEscape.lean` | `TO AUDIT` | prime-divisor existence | unknown | pending |
| `FinitePrimeEscape.lean` | `TO AUDIT` | coprime exclusion | unknown | pending |
| `CosmicCompletion.lean` | `TO AUDIT` | Cosmic Formula identity | unknown | pending |
| `CosmicCompletion.lean` | `TO AUDIT` | Big / Body / Gap bridge | unknown | pending |
| `Demo.lean` | hackathon modules only | public facade | low | expected |
| optional projection | `TO AUDIT` | rational normalization | unknown | deferred |
| optional DkReal bridge | `TO AUDIT` | nested interval API | unknown | deferred |

The audit should state when `import Mathlib` is being used temporarily rather than as the final narrow dependency.

---

## 17. Proposed Minimum Implementation Surface

This section is provisional until the audit is complete.

### `FinitePrimeEscape.lean`

Possible minimal additions:

```lean
/-- A prime divisor outside the original finite reference set. -/
def FreshPrimeFactor
    (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

Only add this if no equivalent exists.

Possible theorem surface:

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p)
    (hu : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

```lean
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p)
    (hu : Nat.Coprime (∏ p ∈ S, p) u)
    (hgt : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
```

Exact binder syntax must follow the audited product API.

---

### `CosmicCompletion.lean`

Possible minimal addition:

```lean
theorem cosmicCompletion
    (P u : ℕ) :
    P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2 := by
  ring
```

Preferred replacement:

```text
thin wrapper around an existing DkMath theorem
```

if one is exact and architecturally suitable.

---

### `Demo.lean`

Possible public surface:

```lean
def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}

def demoP : ℕ := 210

def demoU : ℕ := 11

def demoBoundary : ℕ := 221
```

```lean
theorem demo_product :
    ∏ p ∈ demoPrimeSet, p = demoP
```

```lean
theorem demo_thirteen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 13
```

```lean
theorem demo_seventeen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 17
```

```lean
theorem demo_cosmic_completion :
    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
      (demoP + demoU) ^ 2
```

These names and shapes remain provisional until audit review.

---

## 18. Audit Questions Requiring Explicit Answers

The first Codex report must answer all of the following.

### Arithmetic

```text
1. What exact theorem proves a Finset member divides its product?
2. What exact theorem proves prime-divisor existence for n > 1?
3. What is the shortest Coprime-based exclusion route?
4. Is primality of every member of S logically needed?
5. Does an exact finite-prime escape theorem already exist?
6. Does FreshPrimeFactor already exist?
```

### Cosmic Formula

```text
7. What exact DkMath modules define Big, Body, and Gap?
8. Is the square identity already implemented?
9. Is the square identity a specialization of a generic exponent theorem?
10. Is GN useful for the public facade?
11. What is the narrowest safe import?
```

### Projection

```text
12. Does DkMath already define the signed or unsigned projection?
13. Which convention matches current DkReal interval APIs?
14. Does an exact inverse theorem already exist?
15. Is projection formalized over ℚ, ℝ, or another type?
```

### DkReal

```text
16. What is the primary nested-interval type?
17. Is interval width already defined?
18. Can intervals be mapped through a monotone inverse?
19. Is width transport available?
20. Is width < 1 integer uniqueness already proved?
```

### Architecture

```text
21. Which candidate APIs would create undesirable dependencies?
22. Can the MVP remain a thin three-module facade?
23. What is the first genuinely missing theorem?
24. What exact files should the first implementation checkpoint edit?
```

---

## 19. First Audit Report Requirements

The first audit report must be written to:

```text
docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-001.md
```

It must contain:

```text
Status
Search scope
Modules inspected
Exact reusable declarations
Rejected near matches
Proposed imports
Proposed theorem wrappers
Genuinely missing lemmas
Dependency risks
Smallest Phase 2 implementation surface
No-source-edit confirmation
Stopping point
```

It must also update this map or provide a patch proposal for it.

---

## 20. Audit Stopping Rule

The audit stops when:

```text
the finite-prime theorem route is mapped
the Cosmic Formula route is mapped
candidate projection and DkReal entry points are identified
the first implementation surface is unambiguous
the first genuinely missing theorem is named
```

The audit must stop before:

```text
editing Lean source
proving a missing theorem
creating projection files
refactoring existing modules
implementing the demo
```

---

## 21. Post-Audit Acceptance Criteria

This map is considered audit-complete when:

```text
every MVP concept has at least one confirmed declaration or MISSING record
every selected declaration has an exact module and name
every selected declaration has a semantic note
import costs are recorded
dangerous dependencies are identified
the proposed Phase 2 file set is bounded
open projection and DkReal decisions are clearly separated from MVP work
```

---

## 22. Known Pre-Audit Conclusions

The following project-level conclusions are already fixed and do not require rediscovery.

```text
The public demo uses:
  S = {2, 3, 5, 7}
  P = 210
  u = 11
  P + u = 221
  fresh factors 13 and 17

The main arithmetic theorem concerns:
  freshness relative to a finite set

It does not concern:
  sequence-relative primitive prime divisors

The main Cosmic Formula identity is:
  P(P + 2u) + u² = (P + u)²

The MVP does not require:
  formal Euclidean dissection
  DkReal reconstruction
  projection surjectivity
  open-problem results

Core DkMath must not depend on:
  DkMath.Hackathon.*
```

The audit determines implementation reuse, not project meaning.

---

## 23. Map Update Rules

When Codex updates this document:

```text
preserve section identifiers MAP-001, MAP-002, ...
do not reuse identifiers
replace TO AUDIT with exact findings
include exact declaration names
include module paths
include concise normalized theorem types
record rejected near matches
record import cost
record final reuse decision
```

If multiple declarations support one concept, list each and identify the preferred one.

Historical rejected candidates should remain recorded after audit.

---

## 24. Final Map Goal

The completed map should make the first implementation instruction possible without broad repository exploration.

The ideal post-audit route should look like:

```text
FinitePrimeEscape.lean

existing theorem A:
  member divides Finset product

existing theorem B:
  Coprime exclusion

existing theorem C:
  prime divisor exists

new wrapper D:
  supplied prime divisor is fresh

new corollary E:
  fresh prime factor exists
```

```text
CosmicCompletion.lean

existing theorem F:
  generic Body + Gap = Big

new specialization G:
  P(P + 2u) + u² = (P + u)²
```

```text
Demo.lean

general theorem D
+
general theorem G
+
concrete norm_num facts
```

If the audit produces this level of clarity, the next Codex implementation session should not need to rediscover the same theorem surface.
