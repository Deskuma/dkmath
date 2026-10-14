# Review 005 — Outcome B accepted; pivot to a direct centered-image test

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `afbb0a0b83a200fac5c011532adf4603e2981630`

## Decision

**ACCEPTED — Outcome B**, with a correctly scoped negative-model diagnostic.

Reviewed the actual GitHub version of
`source-coupling-map-005.md`, `report-005.md`, `findings-005.md`,
`evidence/005-verification-summary.md`, and
`DkMathTest/FLT/Seven/SevenRamifiedFusionSourceAllocationChartAudit.lean`.

The map separates what the same real source packet already supplies
(carrier `7^4*M^7`, positive seven-unit `M`, actual complementary
root `N`, `M*N=V*C`, a polynomial identity for `N^7`, real-pair
loaded roots and prime support) from a **chosen** `r,s` and
reconstructed center/endpoint. No new theorem transporting real-pair
load to that selected chart was established.

The existing prime-support statement requires a prime dividing
`r`, and hence has no nontrivial prime to inspect at `r=1`.
This does **not** show that an exact `r=1` chart is realizable.

The already-checked perfect-sixth exclusion requires both
`M/r=t^6` and `9*r^2≤t`. The mere existence of a sixth-power
*residue* in `SixthPowerAllocationSieve` does not imply the literal
sixth-power equality.

## Negative diagnostic checked

The new test-only theorem
`DkMathTest.FLT.Seven.abstractLedger_cheap_not_force_perfectSixth`
constructs the naked-ledger model
`(M,N,V,C)=(631,1,631,1)`. This satisfies the stated positive,
seven-unit, coprime, product and cheap/modulus-one sixth-power premises
yet `M` is not a natural sixth power.

This is a valid counterexample to the **bare abstract premise
implication**, not to a theorem involving an actual source packet or
its quadratic polynomial/phase/orientation data.

The implementer's report records focused Lean checking/build with
exit 0 and axiom dependencies
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The reviewer read the published test source and compact evidence;
no independent Lean build was performed. No production module was
added, correctly respecting the review gate.

## Caution on the proposed missing statement

The manuscript candidate
`source_divisorOne_center_requires_perfectSixth` would infer
`M=t^6, 9≤t` from an actual source packet and an **exact
centered candidate at divisor one**. This is a *strong unproved
restriction*, not a routine identity. Proving it plus the existing
perfect-sixth gap obstruction would already exclude the entire
divisor-one chart for actual packets. Do not add it as an assumed
axiom or force it because a previous plan named it.

The mapping failure may be a genuine mathematical gap rather than a
missing import. Alternative routes must remain open.

## New concrete nearshore calculation (independent, not Lean-checked)

Instead of requiring literal sixth powers, existing code already has
`centeredSevenSextic_no_image_of_adjacent_bracket`, based on strict
monotonicity of the centered polynomial

```text
F(D,q) = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6.
```

For the cheap-filter survivor `M=589, r=1`, set

```text
D = 7^27 = 65712362363534280139543
T = 448*589^49
k = 52382010648825907313680.
```

A **separate Python arbitrary-precision integer calculation**
confirmed the strict bracket

```text
F(D,k) < T < F(D,k+1).
```

Since the inputs `k,k+1` are adjacent, the existing no-image
theorem would show **no integer centered coordinate** can realize
this exact target. This is a promising proof *candidate*, not yet
a Lean-verified theorem. It uses no perfect-sixth assumption and
does not identify an actual source packet.

For this fixed `M`, the existing coarse allocation size bound
`343*r^7 < 589` together with divisor membership also forces
`r=1`. Therefore a successful Lean bracket plus the existing
centered/exact equivalences could rule out *every* exact allocation
at `M=589`, while leaving other `M) unresolved.

The same numerical method may be inspected at other cores, but gate
006 is intentionally limited to one candidate before generalizing.

## Roles and evidence

- Codex: implementation, source checks, focused validation,
  findings/report/evidence only; **no Git add/commit/push, branch
  creation, PR or merge**.
- Wise Wolf: review and publication of review/instruction documents.
- User: integration and overall repository control.
- Disposable `logs/` stays ignored; keep `evidence/` compact,
  with Python precheck and Lean proof clearly distinguished.

## Next step

**Authorize instruction-006**: verify the one strict adjacent-value
bracket in Lean and transport it, without new assumptions, to the
fixed-core exact allocation exclusion at `M=589`. If the numeral
proof is impractical or the route fails, report the exact failure and
avoid claiming a general obstruction. Stop for review after gate 006.
