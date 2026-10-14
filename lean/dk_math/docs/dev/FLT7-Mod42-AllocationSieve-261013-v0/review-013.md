# Review 013 — Outcome A accepted; small-coefficient primitive allocation frontier

Date: 2026-10-14
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `c8f3d45e5282b8ee53eb5b7301203fef38c0223b`

## Verdict and reviewed evidence

**ACCEPTED — Outcome A.** Reviewed the actual GitHub source:

- `DkMath/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean`;
- `DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean`;
- `findings-013.md`, `report-013.md` and
  `evidence/013-verification-summary.md`.

Three public production exports are checked in source:

1. `centeredSevenSextic_not_dvd_thirteen`: for arbitrary
   natural D,q, if 13 does not divide D then 13 does not divide
   the *actual* sextic `centeredSevenSextic D q`.
2. `centeredSevenSextic_no_image_of_thirteen_support`:
   if 13 does not divide r and 13 divides s, the exact
   image equality `F(7^27*r^49,q)=448*s^49` has no natural center.
3. `nestedAllocation_excluded_of_thirteen_support`:
   the same chosen r, s=M/r exclude both existing exact GN/RHS
   receiver branches by the centered equivalence.

The nonvanishing proof uses a **universal** finite-field proposition
for arbitrary `d,x:ZMod13`, discharged by Lean `decide`, and
casts arbitrary naturals to this field. This is not a list of
bounded natural-number examples; the Python arithmetic preview
is not a proof assumption. The support transport retains the
same chosen divisor and quotient and does not redefine any receiver.

The DkMathTest regression
`allocationThree_thirteenSupport_regression` verifies
`M=3*13^12,r=3` passes the full endpoint-free cheap allocation,
the independent sixth-power sieve (witness `13^2`), and one
mod-five **image match**, but fails **both exact receiver branches**
by mod13 support. The old sufficient mod-five square obstruction
is not applicable (`s≡1`, `r²≡4` modulo five).
Matching a residue is not producing an exact endpoint.

Codex-reported focused build/test exited zero; the three
production declarations and named regression depend only on
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The reviewer inspected the committed source and compact evidence;
**did not independently rerun Lean**.

## Proven boundary

This is a pointwise exact receiver exclusion at r=3, not
`¬ SixthPowerSievedNestedCondition (3*13^12)`.
Neither the prior filters' passage nor the residue image match
constructs an actual endpoint or source packet. The missing
same-packet source/real-pair/chart bridge from gate 005 remains open.

## Next structural opportunity: a coefficient bound, not a new modulus

The gate 012 prime-power divisor ownership argument was proved
for `M=2*p^n`. Its proof appears to generalize to

```text
M=c*p^n, p prime, 0<c≤343=7^3.
r∈M.divisors, Coprime r (M/r), 343*r^7<M
    -> r | c.
```

Sketch: if p does not divide r, Euclid gives r|c.
If p divides r, coprimality puts p outside the quotient
t=M/r, so t|c and `M=r*t≤c*r≤343*r≤343*r^7`,
contradicting the strict size guard.
This must be checked in Lean; the generic coefficient lemma
does not follow merely by renaming existing `c=2` code.

Specializing to `c=3,p=13` forces eligible r|3,
so only r=1 or 3, **for arbitrary exponent n**.
At r=1 the complement M is divisible by 3, incompatible
with the **existing mod-42 exact receiver necessity**:
s≡1 mod42 would imply s≡1 mod3. At r=3, for any
n>0, the complementary s=13^n is divisible by 13,
while r=3 is a unit modulo 13; the new gate-013
support theorem excludes both exact receivers.

This suggests the **new, not-yet-Lean-proved** unbounded
full-sieve statement

```lean
∀ n : ℕ, 0 < n →
  ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n).
```

A derived family n=k+1 with injective index map would
certify genuine infinity and recover the gate-013
worked example at n=12.

Scientific caution: for small n, r=3 may fail
the coarse size guard and the full sieve can be empty
for simpler reasons. The theorem must nonetheless
use the actual eligibility and same-r receiver conditions,
not declare `r=3` exact or legitimate unconditionally.
For large n, the new support theorem offers the real
obstruction. No new prime modulus is necessary.

This would be a broader *abstract core* exclusion.
It would still not assert existence of an actual
`RamifiedSignedRootRoutingPacket` with such a core,
or prove FLT7.

## Gate 014 authorization

Authorize `instruction-014.md` for the generic small-coefficient
primitive divisor lemma and full exact-sieve exclusion of
`3*13^n` for n>0, with a small infinity certificate.
Do not demand a uniform cheap/sixth-power survivor proof
on the whole n-family in the same gate; those conditions
require separate proof and a suitable exponent subfamily.

Codex implements/verifies/reports **only**, no Git
staging, commit, push, branch creation, PR or merge.
Wise Wolf publishes reviewed research notes and instructions.
Keep `logs/` transient and `evidence/` compact with
honest verification provenance.
