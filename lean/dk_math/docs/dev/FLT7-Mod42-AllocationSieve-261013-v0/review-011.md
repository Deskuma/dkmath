# Review 011 — Outcome A accepted; prime-base generalization frontier

Date: 2026-10-13
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `37719706f4c3d81bc9808c94dd3dd4f532e663b9`

## Verdict

**ACCEPTED — Outcome A.** Reviewed the actual GitHub sources:

- `DkMath/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean`;
- `DkMathTest/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean`;
- `findings-011.md`, `report-011.md` and
  `evidence/011-verification-summary.md`.

The two production exports are:

1. `eligible_primitive_divisor_two_thirteen_pow`:
   for every natural n, divisor membership in `2*13^n`,
   coprimality of `r` with its **actual quotient**, and the
   existing size guard force `r=1∨r=2`.
2. `sixthPowerSieved_thirteen_power_family_excluded`:
   for every natural k,
   `¬ SixthPowerSievedNestedCondition (2*13^(6+4*k))`.

The source proof uses the same quotient `t=(2*13^n)/r`
as the full-sieve witness. If 13 does not divide r, Euclid
forces `r∣2`. If 13 divides r, the given coprimality
forces 13 not to divide t and hence `t∣2`. This contradicts
`343*r^7<r*t≤2*r`. This reasoning does not require a
global bound on n or M. It **does** require the primitive
coprimality guard, as the test's explicit r=13/n=10
countermodel demonstrates.

For the resulting divisor r=1, previously verified
mod-42 necessary congruence blocks the receiver;
for r=2, the general-gap mod-five integer-image
theorem does so. The exponent identities establishing
`13^(6+4*k)≡1 (mod42)` and `≡4 (mod5)` are shown
for arbitrary k, not sampled values.

The DkMathTest source separately establishes injectivity
of k↦2*13^(6+4*k), the base core 9653618 and k=1,2
applications. This is genuinely an infinite family of
**distinct abstract core values** rejected by the exact
full-sieve predicate.

Codex-reported focused build and tests returned 0. Four
`#print axioms` audits (including the test diagnostics)
list only `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`. The reviewer checked source and
compact evidence, but did **not** independently run Lean.

## Mathematical boundary

Neither this infinite family nor its conditional exact-sieve
exclusion constructs any actual
`RamifiedSignedRootRoutingPacket` or settles whether these
numbers occur as its `internalDepthFourSeventhCore`.
The source/real-pair/chart bridge missing at gate 005 remains
unproven. This is not an arbitrary-M receiver-emptiness
result and not FLT7 closure.

## Next frontier: which part depends on the prime 13?

The divisor argument used only **primality of the power
base**, not the particular numeral 13. The residue
calculations, on the other hand, used the values of
`13^n` modulo 42 and 5.

The next mathematically useful generalization is to
separate these two mechanisms. Suggested theorem
shape (research proposal, **not** Lean checked yet):

```lean
theorem sixthPowerSieved_two_prime_pow_excluded
    {p n : ℕ} (hp : Nat.Prime p)
    (h42 : Nat.ModEq 42 (p ^ n) 1)
    (h5 : Nat.ModEq 5 (p ^ n) 4) :
    ¬ SixthPowerSievedNestedCondition (2 * p ^ n)
```

A supporting eligible-divisor lemma should require **all
three actual guards** — divisor membership, quotient
coprimality, size — and conclude r=1 or 2 for any
prime p. Then the known mod-42 and mod-5 consumers
should close the exact branches. Do **not** hide a
prime-power factorization restriction in a newly defined
receiver or ask for an exact endpoint to exist.

For a second arithmetic regression distinct from 13,
`p=223, n=2` has p prime, `223²≡1 (mod42)` and
`223²≡4 (mod5)`, giving `M=99458`.
Here r=2 is also a legitimate *eligible* divisor under
membership, coprimality and `343*2^7<M`.
These facts are planning calculations to verify in Lean,
not a claim that an exact receiver is inhabited or
the separate sixth-power sieve has been checked.

If the generic lemma is a duplicate of an existing
Mathlib/DkMath result, reuse it rather than building a
new framework. Stop after this bounded generalization.

## Operational roles

Codex: source exploration, code, verification, findings,
report and compact evidence **only**; no git add/stage,
commit, push, new branch, PR or merge. Wise Wolf:
reviews and publishes research notes/instructions to
this branch. User controls integration decisions.
`logs/` is disposable; `evidence/` stays concise,
with attribution for actual local tests.
