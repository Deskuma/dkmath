# Codex Instruction — PRIM-PAR-000 Valuation Tower / Parity Asset Reconnaissance

Branch: `wip/number-theory-primitive-structure-260822-v2`

Project: DkMath NumberTheory Primitive Structure

Checkpoint type: **read-only mathematical/API reconnaissance first**

## Environment boundary

The repository is currently staying on Mathlib / Lean environment **v4.32.2**.

The previous branch included source-level stabilization work intended to make a later v4.33.0 migration smoother, but this checkpoint must **not** perform the upgrade.

Do not change:

```text
lean-toolchain
lakefile / dependency revisions
Mathlib version
```

Do not rewrite proofs merely for hypothetical v4.33.0 compatibility during this reconnaissance.

---

# 1. Current mathematical position

PRIM-C001/C002 and PRIM-L022 are complete.

The generic square-Body normal form is now:

```text
old-generated
or
unique fresh ℓ > P × small old-generated k with 0 < k ≤ P.
```

For Legendre square points, PRIM-L022 identifies the fresh small-cofactor view with the old-prime quotient view.  In a fresh split

```text
ℓ * k = n^2 + r,
ℓ > n,
0 < k ≤ n,
```

an old support prime `p ≤ n` satisfies `p ∣ k`, and

```text
squareOffsetSupportQuotient n p r = ℓ * (k / p).
```

Consequently

```text
large quotient prime
  ↔ k = p
  ↔ singleton old support + selected-prime depth one.
```

The unresolved full-cover frontier still keeps the `old-generated` branch explicit.

The next expected information loss is **prime-power depth parity**.  Before creating a new parity theory, audit whether DkMath already has the required finite tower and parity machinery.

---

# 2. Target conceptual normalization

For a fixed prime `p` and nonzero natural `m`, let

```text
v := padicValNat p m.
```

The desired local normal form is only

```text
v = 2 * pairCount + parityGap
parityGap ∈ {0,1}
```

mathematically:

```text
pairCount = v / 2
parityGap = v % 2
```

so that the finite prime-power tower

```text
p^1, p^2, ..., p^v
```

is partitioned into complete two-depth packets plus at most one terminal unpaired depth.

The intended interpretation is:

```text
pairCount
  complete two-depth packets

parityGap = 0
  no terminal depth remains

parityGap = 1
  one terminal depth remains
```

This checkpoint is **not** authorized to claim that this solves the classical sieve parity problem.

In particular,

```text
Ω(m) odd
```

does not distinguish a prime (`Ω = 1`) from `Ω = 3,5,...`.

The goal is lossless information retention, not a primality theorem.

---

# 3. Already confirmed repository assets

The reconnaissance must start from current source, not from reimplementation.

## 3.1 `DkMath.ABC.PadicValNat`

Current source already contains at least:

```lean
padicValNat_split
padicValNat_eq_zero_iff
Vp_ge_one_iff
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
padicValNat_pow
```

Most importantly, for prime `p` and `m ≠ 0`:

```text
k ≤ padicValNat p m
  ↔ p^k ∣ m.
```

Therefore the valuation already supplies a finite terminal height for the `p^k` tower.

`padicValNat_split` currently expresses a first-layer/deep-layer split.  Determine whether it is useful for parity, or whether ordinary Euclidean division by `2` is the cleaner owner.

## 3.2 `DkMath.NumberTheory.PrimitiveSet.FullExponentSlot`

Current source already contains:

```lean
FullExponentSlotChannelSet
FullExponentSlotCoverage
NatBaseMultiplicityCompleteOn
```

and specifies full prime-power channel membership by

```text
Nat.Prime p
1 ≤ k
k ≤ n.factorization p
q = p^k.
```

Thus DkMath already has an explicit finite exponent-slot interpretation in terms of `Nat.factorization`.

A central audit question is whether the exact bridge

```text
n.factorization p = padicValNat p n
```

(or an equivalent Mathlib theorem) already exists under the natural hypotheses.  Do not create a duplicate if it does.

## 3.3 `DkMath.NumberTheory.ValuationFlow.Basic`

Current source already provides lightweight valuation profiles and `padicValNat`-based mass readers:

```lean
ValuationProfile
profileOfPrime
diffMass
boundaryMass
beamMass
```

Determine whether a parity/depth API naturally belongs near generic Primitive semantics, near `ValuationFlow`, or should remain a thin bridge over `ABC.PadicValNat`.

Do not move existing theorem owners during reconnaissance.

## 3.4 `DkMath.Units.NPUnit`

Current source already proves:

```lean
val_succ
succ_succ
succ_succ_N
```

with the semantics:

```text
one succ step  = +1/2
 two succ steps = +1 and phase preserved.
```

This is a genuine existing two-cycle / half-phase model.

However, **do not automatically make `Primitive` depend on `Units.NPUnit`**.

Audit whether NPUnit is:

```text
A. a theorem-bearing reusable model that should participate in the parity bridge
or
B. only a conceptual/display analogy for the two-depth packet structure.
```

Prefer B unless an actual theorem transfer materially reduces or strengthens the Primitive API.

---

# 4. Required reconnaissance questions

Answer all of the following from current source / Mathlib APIs.

## Q1 — exact valuation/factorization bridge

Find the canonical theorem path relating, for prime `p` and nonzero `m`,

```text
padicValNat p m
```

and

```text
m.factorization p.
```

Classify:

```text
A. exact theorem already exists
B. only a thin wrapper is missing
C. the representations have a nontrivial mismatch
```

Record exact declaration names, imports, hypotheses, and orientation.

## Q2 — finite tower membership

Determine the smallest existing theorem chain for

```text
1 ≤ j ≤ padicValNat p m
  ↔ p^j ∣ m
```

and how it relates to the `FullExponentSlotChannelSet` specification.

Decide whether a new explicit `Finset` of local depths is needed at all.

Do not create one during PRIM-PAR-000.

## Q3 — parity normal form

Inventory Mathlib/DkMath lemmas sufficient to prove, for any `v : ℕ`,

```text
v = 2 * (v / 2) + v % 2
v % 2 ≤ 1
v % 2 = 0 ∨ v % 2 = 1
```

or equivalent `Even` / `Odd` formulations.

Determine whether a valuation-facing wrapper adds real semantic value.

A desired future wrapper might look conceptually like:

```lean
theorem padicValNat_eq_two_mul_pairCount_add_parityGap ...
```

but **do not implement it yet**.

## Q4 — local parity versus global `Ω`

Search current DkMath and Mathlib for an existing finite-support definition/API for the total prime-factor multiplicity

```text
Ω(m) = Σ_p m.factorization p.
```

Record exact existing names if available.

Determine whether the first implementation checkpoint should:

```text
A. stop at local p-direction parity
or
B. safely include a finite global Ω-parity theorem without building new factorization infrastructure.
```

Default to A unless B is already nearly free.

## Q5 — C002 fresh split transport

For

```text
m = ℓ * k
Nat.Prime ℓ
P < ℓ
Nat.Coprime ℓ k
```

inventory the existing theorem path for valuations/factorization showing conceptually:

```text
old prime p ≤ P:
  v_p(m) = v_p(k)

fresh prime ℓ:
  v_ℓ(m) = 1
```

and therefore, if global Ω is available cheaply,

```text
Ω(m) = Ω(k) + 1
```

or at least the corresponding parity flip.

Do not reprove C002 factor geometry.

## Q6 — relation to current Legendre obstruction classes

Map the existing seat classes

```text
simple/fresh
singleton-depth
multi-support
old-generated
```

onto the prime-power tower language.

In particular identify exactly what parity can distinguish and what it cannot.

Required negative check:

```text
Does local/global parity alone force a simple seat?
```

If not, say so explicitly.

## Q7 — actual leverage test

Assess whether preserving terminal parity gives any **new structural restriction** on

```text
SquareOffsetsFullyCovered n
```

beyond the already known Direction/Depth and small-cofactor data.

Classify the result:

```text
Outcome A — DIRECT LEVERAGE
  an existing theorem chain already yields a genuinely stronger full-cover constraint.

Outcome B — LOSSLESS COORDINATE
  parity can be formalized cleanly and is reusable, but currently adds no new contradiction/constraint.

Outcome C — REDUNDANT
  existing support/depth APIs already retain all information that the proposed parity wrapper would expose, so a new layer would be mostly naming.
```

Do not force Outcome A.

---

# 5. Source priority

Use the current v2 branch as the source of truth.

Start with:

```text
DkMath/ABC/PadicValNat.lean
DkMath/NumberTheory/PrimitiveSet/FullExponentSlot.lean
DkMath/NumberTheory/PrimitiveSet/FullExponentSlotBridge.lean
DkMath/NumberTheory/ValuationFlow/Basic.lean
DkMath/Units/NPUnit.lean
DkMath/NumberTheory/Primitive/SquareBody.lean
DkMath/NumberTheory/Legendre/Obstruction.lean
DkMath/NumberTheory/Legendre/LocalizedObstruction.lean
DkMath/NumberTheory/Legendre/SmallCofactor.lean
```

Then search Mathlib/current repository for exact supporting declaration names.

Prefer source and theorem signatures over old review prose.

---

# 6. Deliverable

Create a focused report:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-reconnaissance-260824.md
```

The report must contain:

1. executive outcome A/B/C;
2. exact existing theorem inventory with file/module ownership;
3. valuation ↔ factorization bridge result;
4. finite tower representation result;
5. parity-normal-form theorem inventory;
6. global Ω availability result;
7. C002 fresh-split transport result;
8. mapping to current Legendre obstruction classes;
9. actual leverage assessment for the full-cover frontier;
10. minimal recommended PRIM-PAR-001 theorem surface, **only if justified**;
11. dependencies that should explicitly **not** be introduced;
12. any v4.32.2 / future-v4.33.0 API sensitivity discovered, without upgrading the project.

Keep the report mathematical and API-focused.  Do not turn it into a general essay on sieve theory.

---

# 7. Non-goals / hard boundaries

Do **not** in PRIM-PAR-000:

- modify Lean theorem files;
- add a new parity namespace or abstraction;
- add `Ω` infrastructure if it is not already available cheaply;
- import `NPUnit` into Primitive merely for analogy;
- rewrite `FullExponentSlot` machinery;
- alter PRIM-C001/C002 or PRIM-L022;
- change the Legendre frontier theorem;
- claim a solution to the sieve parity problem;
- claim parity implies primality;
- claim odd `Ω` means prime;
- introduce analytic sieve/PNT/Mertens estimates;
- introduce RH/CFBRC dependencies;
- change Lean/Mathlib versions;
- perform the v4.33.0 upgrade.

This is reconnaissance.  The correct result may be that no new parity implementation is presently justified.

---

# 8. Verification

Since no Lean source modification is authorized, no full build is required solely for this checkpoint.

If temporary scratch examples are used to verify theorem signatures, keep them uncommitted and report the result.

Run:

```sh
git diff --check
```

and confirm that the only committed project change from executing PRIM-PAR-000 is the reconnaissance report.

---

# 9. Stop condition

After writing the report, stop.

Do not begin PRIM-PAR-001 automatically.

The next implementation checkpoint will be chosen only after review of the reconnaissance result.
