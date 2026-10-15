# instruction-003 — GN7 × cyclotomic Kummer common kernel

Date: 2026-10-15 JST  
Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Gate: **003 only**; stop for review.  
Lean root: `lean/dk_math`.

## Preconditions

Read `AGENT.md` at repository root and this research folder's
`README.md`, `ROADMAP.md`, `review-002.md`, and the Gate-001
17-row matrix. Confirm branch/HEAD and preserve local changes.
GitHub repository HEAD is the canonical source.

**Repository artifacts policy:** no build transcripts, CLI outputs,
job counts, evidence directories, downloaded upstream copies,
generated inventory dumps or extra report appendices. Use local
temporary files if diagnostics are needed; keep them untracked.
Do not specify `LEAN_NUM_THREADS`. CI is the final integration judge.

## A. Make Gate 002 visible to ordinary CI

Check the actual default `DkMath` and `DkMathTest` entrances and
the existing `DkMath.FLT.Seven` facade. The Gate-002 module
`PrimeTraceOneDirectCyclotomicKummerUnit` was intentionally opt-in.

Wire **only the minimal appropriate imports** so ordinary project
CI builds/test targets cover G1–G3 and the arbitrary-unit regression,
respecting dependency direction. Do not globally activate the massive
Gate-001 inventory probe or unrelated scratch tests. No CI config
redesign or extra test suite.

## B. GN7 and cyclotomic Kummer share one source

Inspect the actual already-checked Lean declarations and their
hypotheses, rather than proving duplicate algebra:

- `PrimeTraceOneDirectCyclotomicSecondCaseAudit.lean`:
  `directCyclotomicNorm_eq_cyclotomicSeven`,
  `directLinearFactor_norm_product_identity`;
- `PrimeTraceOneDirectCyclotomicIdealOwnership.lean`:
  `directGap_eq_uniformizer_pow`,
  `directLinearFactor_eq_uniformizer_mul_quotient`,
  `directLinearFactor_not_mem_ramifiedPrime_sq`;
- `SevenRamifiedFusionCyclotomicRamifiedPrime.lean`:
  `ofReal_seven_eq_uniformizer_pow_six_mul_unit`;
- Existing `GN 7` / `cyclotomicSeven` and the Kummer
  carry/binomial-coefficient theorems in DkMath number theory.

The guiding identities, with orientations and rings made explicit,
are:

```text
g = endpointLeft - endpointRight
L = endpointLeft - zeta * endpointRight
  = g + (1-zeta) * endpointRight
Norm(L) = cyclotomicSeven(endpointLeft, endpointRight)
g * Norm(L) = endpointLeft^7 - endpointRight^7
7 = unit * (1-zeta)^6
```

Also inspect the polynomial identity
`GN_7(-T,1) = Φ_7(1-T)` (using the actual GN definition
and its permitted ring arguments) and the exactly-once
7-divisibility of interior seventh-row binomial coefficients.
**These mathematical identities are not a descent by themselves.**

Find whether existing source already proves the connections.
If so, **do not add a redundant theorem**. If a genuinely missing
small bridge makes an existing GN constraint available to the
*same chosen cyclotomic source*, implement at most **one**
non-vacuous theorem with real source hypotheses and a minimal test.

## C. Distinguish an invariant from a new obstruction

For each proposed bridge ask: does it impose a restriction not already
equivalent to `L = pi*gamma^7`, `Norm(L)=7*residualRoot^7`,
or other established chosen-packet results?
If not, mark it a useful correspondence but **not** new FLT7
progress. Do not fabricate a descent state or successor.
Do not import Anthropic's finished FLT theorem.

## D. Exit — tiny report only

Create **only** `report-003.md` (aim one page), stating:

- actual changed source paths and proof names (if any);
- CI entrance imports now checking G1–G3;
- essential nonstandard axioms or `sorryAx` only if present;
- exact GN-to-cyclotomic equality and whether it is already
  proved or a genuinely new constraint;
- one precisely named *remaining* mathematical obstruction.

Run local checks as needed, but **do not report or commit build
output, command history, successes/failures or raw logs**.
No `evidence/`, copied research sources, automated bulk audits,
PR or merge. **STOP for review** before Gate 004.
