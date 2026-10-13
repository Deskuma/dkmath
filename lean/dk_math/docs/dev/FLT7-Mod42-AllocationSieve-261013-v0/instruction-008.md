# Codex instruction-008 — divisor-dependent mod-five centered-image exclusion

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-007.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Mission — a genuinely nontrivial generalization of r=1

Gate 007 proved that for **r=1** and `M≡1 (mod 5)`,
the centered sextic target is outside its modulo-five image.
Now inspect the **actual gap** `D=7^27*r^49` for arbitrary
divisors `r` and establish a small, structurally valid
divisor-dependent exclusion, without changing the exact receiver
definition.

The central target is the unit-divisor case:

```lean
theorem centeredSevenSextic_generalGap_no_image_mod_five
    {r s : ℕ} (hr5 : ¬ 5 ∣ r)
    (hs5 : Nat.ModEq 5 s (r ^ 2)) :
    ¬ ∃ q : ℕ,
      centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49
```

This is a **proposed theorem**, not yet Lean checked.
Do not add hypotheses merely to make the proof close.
Use actual definitions/types and an appropriate name.

Then transport it to the actual GN/RHS condition, with
`s=M/r` and *the same chosen r*:

```lean
theorem nestedAllocation_excluded_of_mod_five_square
    {M r : ℕ}
    (hr5 : ¬ 5 ∣ r)
    (hs5 : Nat.ModEq 5 (M / r) (r ^ 2)) :
    ¬ (NestedGNAllocationCondition M r ∨
       NestedRHSAllocationCondition M r)
```

Use `nestedAllocation_iff_centered` from the repository,
retaining natural arithmetic, signed orientation, positivity and
coprimality from the underlying exact candidate.
This theorem does not need to invent endpoint `u`.
If a divisor guard is mathematically required for an additional
consumer, retain it **explicitly**; never erase provenance.

## Numerical discovery table — Python checked, NOT Lean proof

The actual sextic is

```text
F(D,q) = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6.
D = 7^27*r^49, T = 448*s^49.
```

Finite modulo-five enumeration over all 25 pairs
`(r mod 5, q mod 5)` gives:

| r mod 5 | D mod 5 | image F(D,·) mod 5 | allowed s mod 5 if F=T |
| --- | --- | --- | --- |
| 0 | 0 | {0,2,3} | {0,1,4} |
| 1 | 3 | {1,2,4} | {2,3,4} |
| 2 | 1 | {1,3,4} | {1,2,3} |
| 3 | 4 | {1,3,4} | {1,2,3} |
| 4 | 2 | {1,2,4} | {2,3,4} |

For `r=1,4`, `r²≡1 (mod 5)` is excluded.
For `r=2,3`, `r²≡4 (mod 5)` is excluded.
When `r≡0`, `s≡0` is **not** excluded by modular image alone;
hence the `5∤r` premise is necessary for the proposed shape.

First check these candidate patterns and the actual polynomial
against existing code. For the generic no-image theorem,
a small exhaustive proof over residues of `r,s,q` in `ZMod 5`,
or a cleaner algebraic argument, is acceptable. The proof must
reduce **arbitrary** naturals to the finite residue computation.
Do not present the Python table as the Lean result.

## Meaningful r>1 regression example

Test the concrete allocation

```text
r = 2
t = 13
s = t^6 = 4826809
M = r*s = 9653618
```

The following were independently checked with exact Python integer
arithmetic and now need Lean validation where used:

- `r∈M.divisors`, `Nat.Coprime r (M/r)`;
- `343*r^7 < M`, `7^161*r^343 < M^49`;
- `Nat.ModEq 42 (M/r) 1`;
- `SixthPowerAllocationSieve r (M/r)` holds by witness `t=13`;
- `Nat.ModEq 5 (M/r) (r^2)` and `¬ 5 ∣ r`.

Thus the **same fixed divisor r=2** should pass
`ModFortyTwoCheapAllocation M r` and the independent sixth-power
condition while failing *both exact endpoint receiver branches*.
Make this discrimination explicit, ideally as one named test theorem
and, if useful, one small production consumer.

The already-proved sufficient perfect-sixth adjacent-bracket
condition `9*r²≤t` does **not** hold for this example:
`9*4=36>13`. Do not misstate this as a converse of the
existing perfect-sixth exclusion. The mod-five image obstruction
is a distinct argument here.

Do **not** conclude `¬ SixthPowerSievedNestedCondition M`
from the pointwise `r=2` exclusion: another divisor may remain
eligible. Nor does this imply any actual source packet exists.

## Acceptance boundaries

Focus on two genuinely new results:

1. A general unit-divisor mod-five **integer-image** obstruction
   for all `5∤r` with `s≡r² (mod 5)`.
2. Its application to an exact receiver and the nontrivial
   `r=2` cheap-plus-sixth-power surviving allocation.

Optionally record the full residue table in findings or a short
test module, but do not enlarge gate 008 into all residue moduli,
arbitrary-prime classification, global counterexample descent,
new FLT7 closure or a rewrite of receiver definitions.

It would be especially useful to compare whether the new
restriction follows from gate-007's **fixed r=1** theorem (it should
not, since `r=2` uses a different gap) or whether earlier six-power
and size filters already reject the chosen example (the arithmetic
precheck indicates they do not).

No `sorry`, `admit`, new axioms, `sorryAx`,
`unsafe` proof substitutes or unproved premise disguised as
a theorem. If a target is false, return the counterexample and
correct the mathematical plan.

## Reports, verification, and stop

Inspect the theorem inventory and actual Lean declarations.
The implementer chooses local imports, module names, methods
and focused build/test commands according to the environment.

New production exports require `#print axioms`.
Report build/test outcomes with actual exit statuses and
a clear difference between numerical precheck and Lean proof.

Deliver:
- `findings-008.md` — arithmetic table, source reuse,
  decisions, failures, and logical boundary;
- `report-008.md` — Outcome A/B/C, exact exported theorem
  signatures, tests, axiom audit, next research question;
- `evidence/008-verification-summary.md` — compact decisive
  results only, with provenance.

`logs/` remains temporary and ignored; no bulk transcripts.

**Codex is only the implementer and verifier. No git add/stage,
commit, push, branch creation, PR or merge. Stop after gate 008.**

Success A: general divisor-dependent theorem, exact receiver
transport, and r=2 strict-screening example kernel-checked.
Success B: narrower correct theorem or localized proof bridge.
Success C: falsified conjecture or documented obstruction.
