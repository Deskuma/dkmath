# Review 012 — Outcome A accepted; new prime-support image frontier

Date: 2026-10-14
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `f2cbb0af201d731a2c68d258a071c6e05360717e`

## Decision

**ACCEPTED — Outcome A.** The actual published Lean production/test
sources, `report-012.md`, `findings-012.md` and the compact
`evidence/012-verification-summary.md` were inspected.

The two new production theorems in
`DkMath.FLT.Seven.SevenRamifiedFusionPrimePowerPrimitiveExclusion`:

- `eligible_primitive_divisor_two_prime_pow` proves that for
  `Nat.Prime p` and arbitrary `n` (including zero), membership
  `r∈(2*p^n).divisors`, actual quotient coprimality and the
  existing strict coarse size inequality force `r=1∨r=2`.
- `sixthPowerSieved_two_prime_pow_excluded` combines this
  structural result with **explicit** assumptions
  `p^n≡1 (mod42)` and `p^n≡4 (mod5)` to exclude the
  complete exact full sieve at `M=2*p^n`, with no global
  magnitude bound.

The proof transports the *actual same divisor and quotient*
from the exact sieve. The prime-divisibility split uses Euclid:
either r divides 2 or its complementary quotient divides 2;
the latter contradicts the size inequality. Receiver exclusion
at r=1 reuses the divisor-guarded mod42 theorem; at r=2
it reuses the same-divisor mod5 centered-image theorem.
This is a genuine prime parameterization of the gate 011
factor-ownership mechanism, not an unproved endpoint assumption.

DkMathTest checks specialization to the old 13 family, and
a distinct `p=223,n=2,M=99458` example with nonvacuous
eligible r=2. A multi-prime diagnostic
`M=2*(3*5^10),r=3` formally shows that allowing multiple
prime bases defeats the simple `r=1∨r=2` classification.
It does **not** provide an exact endpoint witness.

Codex reports successful final focused build and tests.
`#print axioms` of both exports lists only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The reviewer checked real source and evidence but **did not
rerun Lean independently**.

## Boundary

No claim that all prime powers meet the necessary residues
or that arbitrary M has an empty exact sieve. No source
packet is constructed; gate 005's source/real-pair/chart
compatibility remains open. No FLT7 closure.

## Independent new mathematical precheck: the complementary prime support

The source's actual centered sextic is

```text
F(D,q)=7*q^6+35*D^2*q^4+21*D^4*q^2+D^6,
D=7^27*r^49, target=448*s^49.
```

A **separate Python exact modular enumeration**, not a
Lean proof, shows:

```text
For every d in {1,...,12}, every q modulo 13:
    F(d,q) mod 13 != 0.
For r=3, D mod 13=2,
    {F(D,q) mod13 | q mod13}={1,4,5,10,12}.
```

Therefore a candidate *new* theorem is

```lean
theorem centeredSevenSextic_no_image_of_thirteen_support
    {r s : ℕ} (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ s) :
    ¬ ∃ q : ℕ,
       centeredSevenSextic (7^27*r^49) q = 448*s^49
```

The reason is **prime support**, not the prior condition
`s≡r² (mod5)`: if `13∤r`, D is nonzero mod13 and
the sextic's image avoids zero; if `13∣s`,
the target is zero mod13. The finite verification
above is only a precheck and requires Lean universal proof.

A meaningful *new two-base diagnostic* is

```text
M = 3*13^12, r=3, s=M/r=13^12, t=13^2.
```

Independent exact-integer arithmetic checked:

- divisor membership and quotient coprimality;
- `343*r^7<M`, `s≡1 (mod42)`;
- GN-side cheap size `7^161*r^343<M^49`;
- `s=t^6`, so the separate sixth-power sieve holds;
- modulo-five **compatibility**, since
  `F(7^27*3^49,2)≡448*s^49≡3 (mod5)`;
- yet `s≡0 (mod13)` while the centered polynomial
  is never zero mod13 for this D.

This illustrates an allocation passing the prior cheap,
sixth-power and mod-five *necessary image* checks but
expected to fail both exact receivers for a **new reason**.
A mod-five match is only modular matching, not exact
integer image existence. No packet or exact witness
is asserted.

The target `M=3*13^12` is *not* covered by
the generic `2*p^n` theorem from gate 012.
A future all-divisor theorem for this M would need to
handle **all** eligible divisors and should not be
assumed from a pointwise r=3 exclusion.

## Next gate

Authorize `instruction-013.md` for a focused, source-backed
prime-13 support-image lemma and chosen-divisor exact receiver
transport; test the genuinely composite fixed allocation
`(M,r)=(3*13^12,3)`. An optional all-divisor extension is
deferred until the new source-level obstruction is verified.
Do not turn this into arbitrary-prime/modulus enumeration.

Roles: Codex implements/verifies/reports only, **no staging,
commit, push, branch creation, PR or merge**. Wise Wolf
publishes reviews and research instructions. User owns
integration. `logs/` transient; `evidence/` compact,
with provenance and no fictitious independent rerun.
