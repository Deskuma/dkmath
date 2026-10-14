# Codex instruction-011 — unbounded prime-power core exclusion by primitive allocation

Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Previous review: `review-010.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## One new mathematical question

Gate 010 proved a bounded mixed-obstruction family using the
simple global size threshold `2*s < 343*5^7`.
The existing exact full-sieve, however, also requires
`Nat.Coprime r (M/r)` for its selected divisor.

Can this **primitivity** hypothesis replace the global
upper bound for the special unbounded prime-power family

```text
n_k = 6+4*k
s_k = 13^n_k
M_k = 2*s_k
```

with all `k:ℕ`?

Target (not yet Lean checked):

```lean
theorem sixthPowerSieved_thirteen_power_family_excluded (k : ℕ) :
    ¬ SixthPowerSievedNestedCondition (2 * 13 ^ (6 + 4 * k))
```

Unlike the gate-010 progression, `M_k` is strictly
increasing without an upper cutoff. This experiment should
test that statement on mathematical merit; do not force it
by weakening the exact predicate or adding unproved
source assumptions.

## Source-first review

Read the exact repository definitions and theorem signatures
before implementing:

- `SevenRamifiedFusionSixthPowerAllocationSieve`:
  `SixthPowerSievedNestedCondition`, especially
  `r∈M.divisors`, `Nat.Coprime r (M/r)`,
  `343*r^7<M`, exact branch disjunction;
- `SevenRamifiedFusionModFortyTwoAllocationSieve`:
  the existing mod-42 receiver exclusion **with
  divisor guard**;
- `SevenRamifiedFusionGeneralGapModFiveImage`:
  the general-gap mod-five exact receiver exclusion at
  the **same chosen divisor**;
- `SevenRamifiedFusionParametricMixedExclusion`:
  gate 010 proof structure (only reusable parts, **not**
  its fixed global bound);
- `Nat.Coprime`, `Nat.Prime` and Euclid lemmas in Mathlib,
  plus any pre-existing DkMath prime-power decomposition tools.

Avoid duplicate theorems and unnecessary refactoring.

## Gate A — primitive divisor lemma (first prove the real mechanism)

Suggested shape:

```lean
theorem eligible_primitive_divisor_two_thirteen_pow
    (n : ℕ) {r : ℕ}
    (hmem : r ∈ (2 * 13 ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * 13 ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * 13 ^ n) :
    r = 1 ∨ r = 2
```

`n=0` may be included if valid, or impose the smallest
necessary positivity condition and explain it. This
lemma *must* retain the coprimality premise; without it,
the conclusion can fail for sufficiently large n
(e.g. r=13 with n large). Add a lean-checked diagnostic
showing why the coprimality guard cannot be discarded
if useful.

Candidate argument for a fixed alleged `r`:

1. From divisor membership, obtain `0<r`,
   `r∣2*13^n` and the exact factor identity
   `r*((2*13^n)/r)=2*13^n`.
   Write `t=(2*13^n)/r` for the **same** complementary
   factor as in the full-sieve.
2. If `13∤r`, use primality of 13 to prove
   `Nat.Coprime r (13^n)`. Euclid with
   `r∣2*13^n` yields `r∣2`, so `r=1∨r=2`.
3. If `13∣r`, the given `Nat.Coprime r t`
   implies `13∤t`. Therefore t is coprime
   to `13^n`. The factor identity shows
   `t∣2*13^n`; Euclid now gives `t∣2`,
   hence `t≤2`. Combining
   `r*t=2*13^n` with `0<r` gives
   `2*13^n≤2*r`, contradicting
   `343*r^7<2*13^n`.

This is a proof sketch, not a supplied theorem.
Codex may use valuation, prime-power divisors,
Coprime/multiplicity or a cleaner structural lemma.
**Do not replace this argument with a bounded finite
enumeration of n or of possible r.**

## Gate B — the unbounded source-free family

Verify generally in Lean:

```text
13^(6+4*k) ≡ 1 (mod 42)
13^(6+4*k) ≡ 4 (mod 5)
```

Useful arithmetic: `13²≡1 (mod 42)`,
`13⁴≡1 (mod 5)`, `13⁶≡4 (mod 5)`.

Then assume a `SixthPowerSievedNestedCondition M_k`
witness. Apply Gate A to get `r=1∨r=2`,
using the **actual hcop from that witness**.

- `r=1`: `M_k≡2 (mod 42)`, not 1,
  so apply existing divisor-guarded mod-42
  exact receiver exclusion.
- `r=2`: `M_k/2=s_k≡4=2² (mod 5)`,
  and `5∤2`, so apply existing general-gap
  mod-five exact receiver exclusion.

In both branches preserve the chosen r, actual
division and exact GN/RHS disjunction. No new
endpoint witness or chart equivalence is required.
No global upper bound on M is allowed in the final
unbounded-family statement.

Show that the family is **genuinely unbounded** or
has an injective index map (one small Lean test or
lemma is enough), instead of simply labeling an
indexed theorem an infinite collection.
Check k=0 recovers `M=9653618` from gate 009;
sample k=1,2 as lightweight regression checks.

## Optional diagnostic: cheap versus exact

If the narrow proof is successful, you may look
at whether `r=2` remains a cheap allocation for
infinitely many family members, using existing
gate-008 facts and monotonicity. This is secondary.
Do not claim uniform sixth-power sieve witness:
`13^(6+4*k)` is not literally a sixth power for
arbitrary k. A natural narrower subfamily
`k=3*j` has exponent `6+12*j` and does have a
literal sixth-power witness, but it is optional.

The main result is **no exact full-sieve allocation**
for all k under the actual prime-power provenance,
not merely a cheap-filter contrast.

## Scientific boundary and acceptance

This proof would rule out an **unbounded collection
of abstract core values**, not establish that
any of them is realized by a real
`RamifiedSignedRootRoutingPacket`. Source-specific
carrier/chart constraints identified as missing at
gate 005 remain missing. No unconditional FLT7
closure or general arbitrary-M receiver emptiness.

If the proposed primitive divisor dichotomy is false
or its transfer lacks a necessary premise, report
the first precise missing point and a narrower
correct theorem. Do not introduce axioms, `sorry`,
`admit`, hidden hypotheses or unsafe substitutes.

Acceptance:
- **Outcome A:** Lean-checked primitive divisor
  mechanism, full-sieve exclusion for every k,
  plus a sound unboundedness/injectivity certificate.
- **Outcome B:** a verified narrower structural
  exclusion or a precise missing bridge.
- **Outcome C:** false target or documented obstruction,
  with proof-level evidence of the failure where possible.

## Execution/reporting contract

Codex chooses imports, implementation tactics,
focused Lean checking and local build strategy.

Audit every new exported theorem via `#print axioms`,
report observed standard axioms and any surprises.
Use `findings-011.md`, `report-011.md` and a compact,
provenance-marked `evidence/011-verification-summary.md`
only when evidence is worth retaining.
`logs/` is transient; do not commit large logs.

**Codex: implementation, verification, reporting ONLY.
No Git staging/commit/push, branch creation, PR or merge.
Stop after this gate and return results for review.**
