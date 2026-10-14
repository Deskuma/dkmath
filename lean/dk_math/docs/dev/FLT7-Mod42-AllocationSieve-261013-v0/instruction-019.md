# Codex instruction-019 — discriminate source-intrinsic core constraints from valuation bookkeeping

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed gate: `review-018.md` (Outcome A formalization; no new independent M restriction)
Implementer: GPT-6.1 Sol (light)

## Why gate 019 is different

Gate 018 successfully kernel-checked
`M*N=V*C`, `Coprime M N`, `Coprime V C`
and exclusive prime-valuation ownership for the
**same source packet**. These facts are a faithful
readout of existing source laws, **not** a new
restriction on the factorization of actual M.

A useful next step is not yet another equivalent
valuation, support or coprimality lemma.
Instead rigorously distinguish:

- what the **scalar ledger alone** permits;
- what source **quadratic coordinates, norm identities,
  and ramified axis** add independently;
- whether any established combined condition
  rules out a core in the forbidden/untreated
  arithmetic region.

This gate is primarily **source-first exploration and
falsifiability**, with kernel-checked tests when
a precise statement is found. No new modular-sieve
families, finite-chart existence claims or broad
architecture overhaul.

## Part A — small scalar-ledger separation diagnostic

Use a DkMathTest-only exact arithmetic example:

```text
M=841=29^2, N=1, V=841, C=1.
M*N=V*C, 0<M,N,V,C.
Coprime M N, Coprime V C.
7∤M and 7∤N.
```

Check, in Lean, that every **prime** dividing this
M equals 29, and
`¬ Nat.Coprime 7 (29-1)`. Hence it has no
prime divisor satisfying all the gate-016
permutation-prime support conditions. The scalar
ledger therefore does not force a prime
amenable to the gate-016 general receiver
exclusion.

This is an **abstract integer countermodel to an
inference from the stated ledger alone**, not
a `RamifiedSignedRootRoutingPacket`, not a model
of the additional quadratic/norm identities,
not an exact receiver, and not evidence of an
FLT7 counterexample. Do not describe it as a
counterexample to gate 016 or 018 theorems.

If the above simple finite computation is already
fully duplicated, leave it as a documented
arithmetic fact rather than creating an unnecessary
new production module. A single `decide` test
is sufficient.

## Part B — audit independent real source constraints

Inspect actual theorem signatures and proof dependencies
under the same packet `p`, in a targeted manner:

- `SevenBaseTerminalRamifiedQuadraticInnerRoot`:
  coprimality of actual inner coordinates A,B and
  `B=7^4*M^7`;
- `SevenBaseTerminalRamifiedRealCubicNorm`:
  `leftRoot^7`, `rightRoot^7`,
  `signedRootGap_seventhPower_eq`, and
  `sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven`;
- `SevenRamifiedFusionAllocationThreshold`:
  complementary positive N source ledger
  `M*N=V*C`;
- `SevenRamifiedFusionSourcePrimeValuationLedger`:
  `Coprime V C` and entire prime multiplicity
  ownership;
- the actual canonical split/theorems supplying
  `vertical_coprime_compensation_residual`
  and `compensationCore_eq`;
- `SevenRamifiedFusionOrientedCarrierValuationOwnership`
  and `SevenRamifiedFusionRealPairLoadAllocation`
  only where a concrete link to **actual M**
  is justified.

For every claimed constraint, record its actual
provenance and **exact extra hypotheses**.
Keep Q (quotientRoot), M, complementary N,
V,C, real-pair loads and reconstructed r,s,u,q
distinct unless an actual same-packet theorem
identifies them.

Ask ONE discriminating question first:
**Does the live source already prove an intrinsic
condition on the actual core M that cannot be
read off the scalar ledger alone?**
For instance, a congruence, valuation parity,
restriction on prime factors, or a bound on an
actual core cofactor might be useful, but no such
theorem is presumed to exist.

If a credible candidate is found:
- formulate the exact proposed Lean statement
  with the weakest justified source premises;
- test it against the source definitions and
  all known equations/edge cases;
- prove it in a small production module
  **only if source facts really suffice**;
- report whether it materially contributes to
  core restriction, not just source factoring.

If not, produce a precise negative inventory
rather than an invented lemma or more cosmetic
conservation APIs.

## Part C — compare to the usable gate-016 receiver criterion

To invoke gate 016 at a real source core M,
one still needs some actual decomposition

```text
M = c*ℓ^n,
c≤343, n>0,
ℓ prime, ℓ≠2,7, gcd(7,ℓ−1)=1.
```

Assess explicitly whether the strongest **actually
proven source** conditions provide any part of
this beyond `M>0` and `7∤M`.
Do NOT infer this decomposition from
`M*N=V*C`, gcd properties, or the
prime-valuation ledger alone.

Alternatively, if source coordinate/norm
relations suggest a different intrinsic
contradiction or a descent without a reconstructed
natural endpoint, state **exactly** which new
equation/positivity/well-founded measure is missing.
No claim of unconditional FLT7, bare-packet
inconsistency or chart existence without proof.

Distinguish:
- a theorem from bare p;
- an implication requiring reconstruction hrec;
- a theorem requiring additional seventh-power
  cell hypotheses;
- an unproved source-to-endpoint existence target.

Use `source-bridge-frontier-017.md` as baseline;
do not mechanically copy its whole table.
A source theorem that merely reuses hrec is not
an unconditional source constraint.

## Deliverable and stop discipline

Write:
- `findings-019.md`: what the scalar test
  establishes, what was actually found in source,
  and a definite mathematical next-step conclusion;
- `report-019.md`: Outcome, changes, precise
  theorem signatures (if any), exit status,
  axiom checks, and the genuine relevance to M;
- `source-constraint-frontier-019.md`: a concise
  matrix separating ledger constraints from
  source-only independent constraints and the
  first missing statement, or a sound candidate
  bridge if found;
- `evidence/019-verification-summary.md`
  only for real focused Lean checks.

**Outcome A:** a genuine new, Lean-kernel-checked
source-only restriction on actual M that was not
simply the ledger restated, with an explanation
of how it advances the FLT7 frontier.

**Outcome B:** rigorous Lean-checked scalar
separation or narrowly proved readout, exact
source constraint inventory, and an honest
conclusion that no new M restriction was found.
This is an acceptable endpoint; do not demand
more code just to obtain A.

**Outcome C:** false candidate or concrete blocker
with precise counterexample, missing premise,
or type-check evidence.

Use minimal new production code (possibly none).
Focused build/tests and `#print axioms` for
any new export; no `sorryAx`, `sorry`,
`admit`, new axioms or unsafe substitutions.
Local logs temporary; evidence concise and
explicit about provenance.

If no independent source constraint is found,
**recommend a strategic pause/research redesign**,
not automatic instruction-020 or an arbitrary
sequence of more weak sieve gates.
Do not start gate 020 yourself.

**Codex implements, checks and reports ONLY:
no git add/stage/commit/push, branch creation,
PR or merge. Stop after 019 for review.**
