# Review 007 — Outcome A accepted; general-divisor modulo-five image frontier

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `fa0c7b13f9e68d403a18a777f7d129d76744f787`

## Verdict

**ACCEPTED — Outcome A.** Reviewed the published production and test
modules plus `report-007.md`, `findings-007.md` and
`evidence/007-verification-summary.md`.

The four public declarations in
`DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage` are:

1. `centeredSevenSextic_fixedGap_mod_five_image`: the exact
   polynomial at gap `D=7^27` has image contained in
   residues `{1,2,4}` modulo five for **all** natural centers.
   The tests witness each residue, establishing equality of the
   finite image set.
2. `centeredSevenSextic_fixedGap_no_image_mod_five`: a target
   `448*s^49` with `s≡1 (mod 5)` is outside the image.
3. `nestedAllocation_one_excluded_of_mod_five`: the exact GN
   and RHS receivers at **divisor `r=1`** are excluded if
   `M≡1 (mod 5)`.
4. `mod42Cheap_modFive_family`: every `M=631+210*k`
   passes the cheap filter and separate sixth-power sieve at
   `r=1`, but its *same fixed-divisor* exact receiver is absent.

The Lean source uses the actual sextic definition, reductions into
`ZMod 5`, exhaustive residue classes for arbitrary inputs, and
the pre-existing centered/exact equivalence. The test demonstrates
injectivity and unboundedness of the family.

At `M=589`, the target is **in** the mod-five image, yet gate 006's
independently verified adjacent-integer bracket still excludes its
exact center. These are mathematically distinct failure mechanisms.

The implementer's focused build and final Lean test were reported
with exit status 0. Each of the four `#print axioms` lists only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
The reviewer inspected source and compact evidence, but
**did not independently rerun Lean**.

## Scope and what has NOT been shown

`r=1` exclusion does not automatically eliminate other divisor
allocations of a large `M`. The result neither proves
`¬ HasModFortyTwoCheapAllocation M`, nor
`¬ SixthPowerSievedNestedCondition M` for the whole progression,
nor unconditional FLT7.

The infinite family refers to abstract arithmetic candidates;
actual source packets or exact endpoint witnesses are not generated.

## New arithmetic precheck: the effect of a general divisor r

The actual centered gap is `D=7^27*r^49`; the target is
`448*s^49`, `s=M/r`. A separate exhaustive Python
integer-residue computation gives the following *candidate*
modulo-five image table (not yet Lean-checked for variable r):

| r mod 5 | D mod 5 | F(D,q) residues for q mod 5 | Possible s mod 5 if image equality holds |
|---|---|---|---|
| 0 | 0 | {0,2,3} | {0,1,4} |
| 1 | 3 | {1,2,4} | {2,3,4} |
| 2 | 1 | {1,3,4} | {1,2,3} |
| 3 | 4 | {1,3,4} | {1,2,3} |
| 4 | 2 | {1,2,4} | {2,3,4} |

In particular, for **5 not dividing r**, whenever
`s≡r^2 (mod 5)`, the residue `448*s^49` is
**absent** from `F(7^27*r^49,q)` for every integer q.
The `r=1` theorem is a special case. The `5 ∤ r`
guard matters: when `5 ∣ r` and `s≡0`, both target
and polynomial may vanish modulo five.

**Concrete distinct allocation (Python arithmetic check, not yet Lean):**

```text
r = 2
s = 13^6 = 4826809
M = 2*s = 9653618
s % 42 = 1
s % 5 = 4 = r^2 % 5
gcd(r,s) = 1
343*r^7 < M
7^161*r^343 < M^49
SixthPowerAllocationSieve r s holds (t=13, because s=t^6)
```

Thus `(M,r)=(9653618,2)` passes the ordinary cheap
allocation and the separate sixth-power sieve but should
be rejected by the new mod-five image test. This time
`r≠1`. The existing perfect-sixth adjacent-bracket theorem
requires `9*r^2≤t`, which fails here since `36>13`.
Do not assume that failure of this *sufficient* criterion
means the exact receiver is inhabited.

The above table and concrete example are preliminary
arithmetic checks, not yet a new Lean kernel result.
They motivate one bounded follow-up instead of an
unrestricted search over moduli.

## Next gate and responsibilities

Authorize `instruction-008.md` to prove the **unit-divisor
(`5∤r`) generalized mod-five no-image theorem** and test
a nontrivial `r=2` allocation. The full `r≡0` classifier
is optional discovery, not a requirement for a correct result.

Codex: implement, test and report only. **No Git add/stage,
commit, push, branch creation, PR or merge.** Wise Wolf publishes
the reviewed research documents to the branch; the user controls
integration. `logs/` disposable, `evidence/` concise and
provenance-labelled.

Stop after gate 008 for review. Do not claim any general
reconstruction obstruction not justified by the new theorem.
