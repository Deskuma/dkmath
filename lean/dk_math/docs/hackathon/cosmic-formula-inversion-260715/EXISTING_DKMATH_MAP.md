# Existing DkMath Map

## DkMath — Cosmic Formula Inversion

## 1. Current Status

```text
DOCUMENT STATUS: AUDITED AT hack-001
LEAN SOURCE AUDIT: COMPLETED
SOURCE EDITS: NONE
FINAL RECOMMENDATION: a thin Nat facade over Mathlib, with a local ring identity
```

The audit distinguishes finite-set freshness from sequence-relative primitive
divisors. `Finset ℕ` is sufficient; no new finite-prime-universe structure is
needed.

## 2. Audit Objective and Confirmed Core Route

| Role | Module | Declaration and normalized type | Class | Cost |
|---|---|---|---|---|
| member divides product | `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` | `Finset.dvd_prod_of_mem (f) (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i` | DIRECT | narrow through Mathlib |
| remove known addend | `Mathlib.Algebra.Ring.Divisibility.Basic` | `dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c` | DIRECT | narrow |
| coprime means gcd one | Mathlib Nat gcd | `Nat.coprime_iff_gcd_eq_one : Nat.Coprime a b ↔ Nat.gcd a b = 1` | DIRECT | narrow |
| common divisor divides gcd | Mathlib Nat gcd | `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n` | DIRECT | narrow |
| prime cannot divide one | Mathlib Nat prime | `Nat.Prime.not_dvd_one : Nat.Prime q → ¬ q ∣ 1` | DIRECT | narrow |
| prime divisor exists | `Mathlib.Data.Nat.Prime.Basic` | `Nat.ne_one_iff_exists_prime_dvd : n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n` | DIRECT | narrow |

Shortest exclusion route, entirely in `ℕ`: from `q ∈ S`, use
`Finset.dvd_prod_of_mem id` to obtain `q ∣ P`; combine that with
`q ∣ P + u` via `dvd_add_right` to get `q ∣ u`; then `Nat.dvd_gcd`,
`Nat.coprime_iff_gcd_eq_one`, and `Nat.Prime.not_dvd_one` contradict
primality. No subtraction or `ℤ` bridge is required.

`DkMath.Samples.Prime.B` contains
`exists_prime_not_mem_dvd_prod_add_unit` with assumptions `0 < u`, every
member prime, and every member not dividing `u`. It is a useful near match but
not the requested Coprime API. The Coprime variant in that file,
`exists_prime_not_mem_dvd_prod_add_unit_of_coprime'`, contains `sorry`, so it
is rejected as a dependency.

## 3. Reuse Classification

The primary labels used below retain the project meanings: `DIRECT`,
`WRAPPER`, `COROLLARY`, `BRIDGE`, `MISSING`, `REJECTED`, `DANGEROUS`, and
`DEMO_ONLY`.

## 4. Audit Record Format

Each MAP entry records a status/classification, exact declaration where one
exists, hypotheses or semantic boundary, and the reuse decision.

## 5. Search Sources

Direct source, theorem index, compressed source database, summary archive,
candidate modules, and Mathlib source were checked in the prescribed order.

## 6. Search Rules

Both standard mathematical vocabulary and DkMath vocabulary were searched;
no declaration was accepted from its name alone.

## 7. Required Discrete Arithmetic Map

### MAP-001 — Finite Prime Set Representation

CONFIRMED / DIRECT. Use `S : Finset ℕ` and, only where the public contract
needs it, `∀ p ∈ S, Nat.Prime p`. A wrapper structure adds no value.

### MAP-002 — Finset Product of Prime Members

CONFIRMED / DIRECT. Use `P := ∏ p ∈ S, p` and
`Finset.dvd_prod_of_mem (fun p => p) hqMem`.

### MAP-003 — Product Positivity

CONFIRMED / COROLLARY. It is not needed for divisor exclusion. If needed,
primality gives nonzero factors and `Finset.prod_ne_zero_iff`; the empty
product is already `1`, so `S.Nonempty` is unnecessary.

### MAP-004 — Coprimality API

CONFIRMED / DIRECT. Public statements should use `Nat.Coprime P u`; the
exclusion proof may rewrite with `Nat.coprime_iff_gcd_eq_one`.

### MAP-005 — Divisor of `P + u` and `P` Divides `u`

CONFIRMED / DIRECT. `dvd_add_right hqP` turns `q ∣ P + u` into `q ∣ u`.
This is cleaner than the `Nat.dvd_sub` route used in the older sample.

### MAP-006 — Coprimality Excludes a Prime Dividing Both Inputs

CONFIRMED / COROLLARY. `Nat.dvd_gcd hqP hqu`, the gcd-one form of
coprimality, and `hqPrime.not_dvd_one` close the contradiction.

### MAP-007 — Supplied Prime Divisor Is Fresh

NOT FOUND AFTER SEARCH / MISSING. No completed exact theorem with
`Nat.Coprime (∏ p ∈ S, p) u` and a supplied divisor was found. Proposed shape:

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) : q ∉ S
```

Notably, `∀ p ∈ S, Nat.Prime p` is not logically required for exclusion.

### MAP-008 — Existence of a Prime Divisor

CONFIRMED / DIRECT. From `1 < n`, derive `n ≠ 1`, then apply
`Nat.ne_one_iff_exists_prime_dvd`. This exact theorem supplies the witness.

### MAP-009 — Existence of a Fresh Prime Factor

PARTIAL / COROLLARY. Compose MAP-008 and MAP-007. Neither `S.Nonempty`,
`0 < u`, nor `0 < P` is needed once `1 < P + u` is assumed.

### MAP-010 — Universal Freshness of All Prime Divisors

PARTIAL / WRAPPER. This is the universal closure of MAP-007 and needs no new
mathematics.

## 8. Freshness and Primitive-Factor Map

### MAP-011 — Existing `FreshPrimeFactor` Predicate

NOT FOUND AFTER SEARCH / MISSING. Searches covered direct source,
`__theorems-heading.txt`, and the compressed source database. Proposed local
predicate: `Nat.Prime q ∧ q ∣ n ∧ q ∉ S`.

### MAP-012 — Primitive Prime Divisor APIs

REJECTED. `DkMath.NumberTheory.PrimitiveSet.PrimitiveOn` is a divisibility
antichain, while `PrimitivePrimeFactorOfDiffPow`, Petal/Zsigmondy bridges, and
`PrimitivePrimeDivisor` are sequence/exponent-relative. None means finite-set
freshness; their broad imports and hypotheses are also unsuitable.

### MAP-013 — Finite Prime Universe Existing Structure

NOT FOUND / REJECTED as unnecessary. `Finset ℕ` plus a prime-membership
hypothesis is the correct MVP representation.

## 9. Cosmic Formula Map

### MAP-014 — Core Cosmic Formula Module Family

CONFIRMED. `DkMath.CosmicFormula.Defs` defines real-valued `Big`, `Body`, and
`Gap`; `DkMath.CosmicFormulaBinom` defines generic `CommRing` versions and
`big_is_body_and_gap`; `DkMath.CosmicFormula.CoreBeamGap` gives a generic
`CommSemiring` decomposition through `BigN`, `BodyN`, and `Gap`.

### MAP-015 — Square Completion Identity

PARTIAL / COROLLARY. `DkMath.Samples.Prime.B.cosmic_identity_ring` states the
same polynomial as a subtraction-equals-zero theorem over `CommRing`, but the
module imports all of `Mathlib` and contains unrelated unfinished declarations.
For the Nat facade, the narrow and safe recommendation is a local theorem
proved by `ring`:

```lean
P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

### MAP-016 — Existing Big Definition

CONFIRMED / BRIDGE. `CosmicFormulaBinom.Big d x u = (x + u)^d` is generic;
specialize `d = 2`. The public Nat equality need not expose this definition.

### MAP-017 — Existing Body Definition

CONFIRMED / BRIDGE. `CosmicFormulaBinom.Body d x u = x * G d x u`; its square
specialization normalizes to `x * (x + 2*u)`, but that normalization lacks the
thin exact public theorem desired here.

### MAP-018 — Existing Gap Definition

CONFIRMED / DIRECT. `CosmicFormulaBinom.Gap d u = u^d`; at `d = 2` it is the
required square Gap.

### MAP-019 — Generic Exponent Cosmic Formula

CONFIRMED / DIRECT. `DkMath.CosmicFormulaBinom.big_is_body_and_gap`:
`Big d x u = Body d x u + Gap d u` over any `CommRing`.
`CoreBeamGap.big_eq_body_add_gap` provides the subtraction-free
`CommSemiring` analogue.

### MAP-020 — GN Identity

PARTIAL / DEFERRED. `Body_eq_GZ`, `mul_G_eq_GZ`, and the generic binomial
identity connect Body to the canonical kernel. GN/GZ naming and imports make
this unnecessary for the public square facade; use it only in later bridges.

### MAP-021 — Gnomon / GnomonBand APIs

NOT FOUND AFTER SEARCH / MISSING as a relevant stable public API. Arithmetic
completion suffices; no geometry should be introduced.

## 10. Normalized Cosmic Formula Map

### MAP-022 — Existing Normalization API

NOT FOUND AFTER SEARCH / MISSING for the stated rational Body/Gap conservation.
It is a small future rational corollary requiring a nonzero denominator.

### MAP-023 — Linear Gap Coordinate

NOT FOUND / MISSING. Existing Units/KUS uses different semantics.

### MAP-024 — Normalized Body

NOT FOUND / MISSING. This should remain a later `ℚ` definition/corollary.

## 11. Projection Map

### MAP-025 — Existing Projection Definitions

NOT FOUND AFTER SEARCH / MISSING. `DkMath.Samples.Projection` is a real-valued
curvature/Body demo and does not define either `P/(P+u)` or `-P/(P+u)`.
The CF2D inverse action is matrix/level-set semantics and is unrelated.

### MAP-026 — Unsigned Projection Interval Bound

PARTIAL / COROLLARY from ordered-field division lemmas; no DkMath wrapper.
Its image lies in `[0,1)` when `0 ≤ P` and `0 < u`.

### MAP-027 — Signed Projection Interval Bound

PARTIAL / COROLLARY; no DkMath wrapper. Its image lies in `(-1,0]` under the
same hypotheses.

### MAP-028 — Exact Unsigned Inverse

NOT FOUND / MISSING. Proposed rational formula `u*x/(1-x)` with `x ≠ 1`.

### MAP-029 — Exact Signed Inverse

NOT FOUND / MISSING. Proposed rational formula `-u*x/(1+x)` with `x ≠ -1`.

### MAP-030 — Projection Injectivity for Fixed `u`

NOT FOUND / COROLLARY once either exact inverse is proved.

### MAP-031 — Projection Image Characterization

DEFERRED. No MVP requirement; do not claim surjectivity onto a full interval.

The unsigned convention is the better first candidate because current DkReal
arithmetic is explicitly nonnegative. The signed convention requires a signed
DkReal layer that the repository itself says is deferred.

## 12. DkReal Map

### MAP-032 — DkReal Core Type

CONFIRMED / DIRECT. `DkMath.Analysis.DkReal.Basic` defines
`DkMath.Analysis.DkReal` with `interval : ℕ → GapInterval`, stepwise nesting,
and widths tending to zero; `DkReal.ofRat` embeds rationals.

### MAP-033 — GapInterval

CONFIRMED / DIRECT. `DkMath.Analysis.DkReal.Interval.GapInterval` has rational
`lo`, `hi`, and `lo ≤ hi`; `singleton`, interval addition, nonnegative
multiplication, power, and separation APIs exist.

### MAP-034 — Nested Interval Theorems

CONFIRMED / DIRECT. Use `DkReal.interval_succ_subset`,
`interval_subset_of_le`, and `tendsto_width_zero`. Semantic membership in all
cast intervals is supplied later by `DkReal.Semantic.semanticValue_mem_Icc`.

### MAP-035 — Width Definition

CONFIRMED / DIRECT. `GapInterval.width I = I.hi - I.lo`, with
`width_nonneg`, `lo_add_width`, and arithmetic width lemmas.

### MAP-036 — Mapping Intervals Through a Monotone Function

NOT FOUND AFTER SEARCH / MISSING. Existing interval power is specialized to a
nonnegative natural power, not a fractional-linear inverse map. This is the
first likely DkReal representation bridge.

### MAP-037 — Width Transport Through Inverse Map

NOT FOUND AFTER SEARCH / MISSING. No fractional-linear endpoint-width bound
was found.

### MAP-038 — Width Less Than One Implies At Most One Integer

NOT FOUND AFTER DkMath and Mathlib theorem-index/source searches / COROLLARY.
Basic ordered-ring facts can prove it, but an exact reusable packaged theorem
was not located.

### MAP-039 — Integer Existence in an Interval

PARTIAL / BRIDGE. It should come from transported membership of the original
`P`, not from width or floor/ceil alone.

### MAP-040 — Unique Macro-Integer Reconstruction

NOT FOUND / BRIDGE. Compose inverse-map membership, MAP-037, and MAP-038;
this is stretch work, not MVP.

## 13. Demo Arithmetic Map

### MAP-041 — Demo Prime Set Evaluation

DEMO_ONLY: prove `∏ p ∈ {2,3,5,7}, p = 210` with `norm_num`/`decide`.

### MAP-042 — Demo Coprimality

DEMO_ONLY: `Nat.Coprime 210 11` by `norm_num`/`decide`.

### MAP-043 — Demo Boundary

DEMO_ONLY: `210 + 11 = 221` by `norm_num`.

### MAP-044 — Demo Factorization

DEMO_ONLY: `221 = 13 * 17` by `norm_num`.

### MAP-045 — Demo Prime Proofs

DEMO_ONLY: `Nat.Prime 13` and `Nat.Prime 17` by `norm_num`/`decide`.

### MAP-046 — Demo Freshness

WRAPPER: use the general supplied-divisor exclusion theorem for both `13` and
`17`; automation may discharge concrete primality/divisibility.

### MAP-047 — Demo Cosmic Completion

WRAPPER: specialize the general Nat completion theorem at `210` and `11`, then
normalize displayed constants.

## 14. Candidate DkMath Module Families

CosmicFormula is semantically relevant; NumberTheory supplies standard
arithmetic precedents. PrimitiveSet, Petal, KUS, Units, SilverRatio, and CF2D
are rejected or deferred for the MVP because their meanings or dependency
costs do not match the contract.

## 15. Mathlib Fallback Map

The selected fallback surface is Finset product divisibility, Nat gcd/Coprime,
Nat prime-divisor existence, divisibility of sums, and `ring`. Ordered-field
and floor/ceil APIs remain later projection/reconstruction tools.

## 16. Import Audit Table

| Hackathon module | Proposed import | Use | Risk |
|---|---|---|---|
| `FinitePrimeEscape.lean` | narrow Mathlib Finset/Nat prime-gcd modules, or `Mathlib` initially | product, divisibility, gcd, prime existence | low |
| `CosmicCompletion.lean` | `Mathlib` for `ring` | local Nat polynomial identity | low |
| `Demo.lean` | the two hackathon modules | facade and concrete arithmetic | low |
| later projection | ordered-field Mathlib only | rational bounds/inverse | low |
| later DkReal bridge | `DkMath.Analysis.DkReal.Basic` plus interval module | interval representation | moderate |

Do not import `DkMath.Samples.Prime.B`: it is broad, global-namespace sample
code and includes unfinished Coprime theorems. Do not import PrimitiveSet,
Petal, Zsigmondy, KUS, Units, or CF2D for the MVP. The smallest `hack-002`
surface is `FinitePrimeEscape.lean` only: define the exact local predicate if
desired, prove supplied-divisor exclusion, and derive fresh-prime existence.

## 17. Proposed Minimum Implementation Surface

For `hack-002`, edit only `FinitePrimeEscape.lean`; add the local
`FreshPrimeFactor` predicate if accepted, the supplied-divisor exclusion
theorem, and the existence corollary. Later checkpoints may add a local `ring`
wrapper in `CosmicCompletion.lean` and concrete facts in `Demo.lean`.

## 18. Audit Questions Requiring Explicit Answers

All 24 required questions are answered by MAP-001 through MAP-047 and the
checkpoint report. The decisive answers are: the exact finite escape theorem
and predicate are missing; the generic Cosmic split exists; the public square
wrapper should be local; neither projection exists; DkReal has the carrier,
nesting, and width entry points but lacks inverse interval mapping and width
transport.

## 19. First Audit Report Requirements

The completed detailed record is `report-hack-001.md` in this directory.

## 20. Audit Stopping Rule and Searches Performed

Exact and semantic searches were run over `DkMath/`,
`logs/summary_report/__theorems-heading.txt`,
`logs/__dkmath-all.lean.txt.gz`, the summary-report archive listing, direct
candidate modules, and Mathlib sources. Terms included `FreshPrimeFactor`,
prime/divisor/product/Coprime variants, `Big`, `Body`, `Gap`, `GN`, projection,
inverse, normalization, DkReal, GapInterval, map interval, width transport,
floor/ceil, `AtMostOne`, and integer uniqueness.
