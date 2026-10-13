# Codex instruction-013 — prime-13 support gap in the centered integer image

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-012.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Research objective

The previous gates gave necessary residue sieves and
prime-power primitive divisor restrictions. Gate 012's
multi-prime diagnostic showed that not all eligible
allocations reduce to r=1 or r=2.

Here test a **different, source-independent but
factor-sensitive obstruction**: the prime 13 may divide
the complementary factor `s=M/r` without dividing
the actual gap `D=7^27*r^49`. The **actual**
centered sextic seems unable to take the value zero
modulo 13 when D is a unit.

This is a new proposed theorem, **not yet Lean-checked**.
It must be proved from the real polynomial, not from
general intuition about cyclotomic factors or a Python table.

## Existing source audit

Inspect actual declarations / index first:

- `DkMath.FLT.Seven.SevenRamifiedFusionCenteredPolynomial`:
  `centeredSevenSextic` and `nestedAllocation_iff_centered`;
- `DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage`:
  the same-r exact receiver transport pattern, but at
  a **different** modulus;
- `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`:
  endpoint-free cheap allocation definition;
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`:
  exact and separate sixth-power sieve definitions;
- relevant Mathlib ZMod/nat divisibility APIs and any
  already existing mod13 image/nonvanishing facts.

Do not alter existing receivers or rewrite proved sieve code.

## Gate A — universal mod13 polynomial nonvanishing

For

```text
F(D,q)=7*q^6+35*D^2*q^4+21*D^4*q^2+D^6
```

the independent **Python exact modular precheck** found
`F(D,q)≠0 (mod13)` for all residues
`D∈{1,...,12},q∈{0,...,12}`.
A small image check when `D≡2` yielded
`{1,4,5,10,12}` (never zero).

Prove a universal Lean statement for arbitrary naturals
`D,q` with `¬13∣D`, perhaps in `ZMod 13`.
Use a short algebraic proof or finite reduction covering
all input residues, **not** 169 isolated examples or a
Python precheck promoted to a theorem.

Then derive the main proposed API, adapting Lean names:

```lean
theorem centeredSevenSextic_no_image_of_thirteen_support
    {r s : ℕ} (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ s) :
    ¬ ∃ q : ℕ,
      centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49
```

The proof should establish that `13∤r` implies
`13∤(7^27*r^49)`, and that `13∣s` makes
the target zero modulo13. Do not add hidden
positivity/coprimality assumptions.

## Gate B — same chosen r exact receiver exclusion

Transport the no-image theorem through the **existing**
`nestedAllocation_iff_centered`:

```lean
theorem nestedAllocation_excluded_of_thirteen_support
    {M r : ℕ}
    (hr13 : ¬ 13 ∣ r)
    (hs13 : 13 ∣ M / r) :
    ¬ (NestedGNAllocationCondition M r ∨
       NestedRHSAllocationCondition M r)
```

Normalize the necessary scalar equality
`64*(7*(M/r)^49)=448*(M/r)^49`.
The chosen r and quotient are preserved. No
additional `r∣M` guard is necessary merely for
this scalar transport; if you create an allocation
consumer requiring it, retain that guard explicitly.

Do not conclude arbitrary-M full-sieve emptiness.

## Gate C — composite prime-support regression, r=3

Use the concrete allocation:

```text
s=13^12
M=3*s
r=3
t=13^2
```

It has two distinct prime bases in M.
Check in Lean, with the *same chosen r=3*:

1. `r∈M.divisors`, `Nat.Coprime r (M/r)`,
   `343*r^7<M`, `s=M/r` and
   `Nat.ModEq 42 s 1`;
2. `ModFortyTwoCheapAllocation M r` — including
   the actual branch-size inequality, not just
   the congruence;
3. `SixthPowerAllocationSieve r (M/r)` using
   the **literal equality** `s=(13^2)^6`.
   This is a separate necessary condition, not
   an actual exact endpoint witness;
4. the previous mod-five **image is compatible**
   at q=2: the actual F(D,2) and
   `448*s^49` have the same residue modulo5.
   This is not a natural integer image equality;
5. `13∤r` and `13∣M/r`, hence the newly proved
   mod13 theorem excludes **both** exact GN/RHS
   receivers for this r.

These arithmetic comparisons are independently
Python-checked but must be Lean-verified where claimed.
The fresh mod13 result must not be confused with
the old mod5 square obstruction: at r=3,
`s≡1 (mod5)` whereas `r²≡4 (mod5)`;
the gate-008 sufficient premise is not met.

Optionally export one small composite regression theorem
if it is genuinely useful; a test-only named result suffices.

## Interpretation, outcome and boundaries

If successful, the new mechanism is a *complementary
prime-support obstruction* to an **exact integer image**,
rather than an arbitrary extra congruence on s alone.
It uses both which primes divide the gap r and which
primes divide the complement s.

For this gate, **do not claim**

- `¬ SixthPowerSievedNestedCondition (3*13^12)`
  from the r=3 result alone;
- any existence or nonexistence of an actual
  `RamifiedSignedRootRoutingPacket` with such a core;
- a theorem for all primes analogous to the mod13 case;
- arbitrary-M reconstruction emptiness or FLT7 closure.

A later gate may exploit the already-proved prime-power
ownership argument to classify **all eligible divisors**
of `3*13^n`, but that is not the deliverable here.

There is a possible abstract number-theoretic explanation:
`F(D,q)=[(q+D)^7-(q-D)^7]/(2D)` over fields of
characteristic not 2 or 7; and the seventh-power
map on the nonzero group mod13 is injective since
`gcd(7,12)=1`. This is only explanatory guidance:
the actual Lean result must be checked directly
and must not divide by a potentially zero D.

Outcome A: arbitrary-unit-D mod13 nonvanishing,
support-based no-image and same-r receiver exclusion,
plus correct nontrivial r=3 regression, Lean checked.
Outcome B: a narrower sound lemma or a precise missing
bridge.
Outcome C: falsified target or documented proof blocker.

## Validation, records and stop

Codex decides imports, proof strategy and focused
build/test procedure appropriate to the actual environment.
For new public theorems run `#print axioms`, reject
`sorryAx`, `sorry`, `admit`, fresh axioms and unsafe
proof substitutes. Do not confuse a finite modular
precheck with verified general input reduction.

Deliver `findings-013.md`, `report-013.md`,
and concise `evidence/013-verification-summary.md`
when material proof evidence exists. Label provenance
and actual exit status. `logs/` stays temporary/ignored.

**Codex only implements, tests and reports.
No git stage/add, commit, push, branch creation,
PR or merge. Stop after gate 013.**
