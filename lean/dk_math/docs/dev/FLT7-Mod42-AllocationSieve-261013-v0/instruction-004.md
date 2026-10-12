# Codex instruction-004 — global rejection and infinite-survivor audit

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-003.md` (gate 003 Outcome A accepted)
Implementer: GPT-6.1 Sol (light)
Scope: a focused mathematical audit of the **strength and limitations**
of the existing endpoint-free mod-42 allocation filter.

**Implement/test/report only. Do not stage, commit, push, create branches,
open PRs or merge. Stop after this instruction.**

## Research question

We now have a necessary condition:
`InternalDepthFourCounterexampleReconstructionObligation p` implies
`HasModFortyTwoCheapAllocation (internalDepthFourSeventhCore p)`.

Determine what this *actually* rules out using two opposite examples:

1. Prove that the new arithmetic filter excludes **all allocation
   divisors** for one concrete core (`M=554`), not just `r=1`.
2. Prove that the arithmetic filter still allows an **infinite family**
   of core values (`M=631+42*k`, `r=1`), even if the old
   `SixthPowerAllocationSieve` is required separately at this divisor.

These are results about **cheap necessary arithmetic conditions**.
They do not supply or rule out an endpoint witness for arbitrary `M`,
and do not prove unconditional FLT7.

## Existing source to inspect and reuse

Inspect exact definitions and signatures, using the theorem index and
actual Lean sources before writing anything:

- `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`
- `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold`
- `DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit`

Do not recreate an existing theorem and do not alter exact receiver
predicates. You may choose your own names, files, imports and proof
strategy. Preserve the mathematical statements below.

## Gate A — full rejection at M=554

Proposed exported theorem shape:

```lean
theorem no_mod42Cheap_at_554 :
    ¬ HasModFortyTwoCheapAllocation 554
```

Reason: if `ModFortyTwoCheapAllocation 554 r`, the divisor
membership gives `r>0`; its bound `7^3*r^7<554` forces `r=1`,
since `r≥2 → 7^3*r^7 ≥ 343*128 > 554`.
But `554/1 ≢ 1 (mod 42)`. This must be checked with Lean
rather than assuming a finite inspection is a general proof.

A small companion consequence can be useful:
```lean
theorem no_reconstruction_of_core_eq_554
    (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 554) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

However, note that a real packet may already have constraints
excluding this exact core independently. Treat this as a **conditional**
consumer, not a newly constructed packet or global contradiction.
This companion theorem is optional if the source-specific premises
make it redundant.

## Gate B — infinitely many surviving cheap candidates

Proposed exported shape:

```lean
theorem mod42Cheap_family (k : ℕ) :
    ModFortyTwoCheapAllocation (631 + 42 * k) 1
```

The arithmetic needed:

- `1 ∈ (631+42*k).divisors` and coprimality to 1;
- `7^3*1^7 < 631+42*k`;
- `(631+42*k)/1 ≡ 1 (mod 42)`;
- GN-side threshold `7^161*1^343 < (631+42*k)^49`.
  Establish the base integer inequality `7^161 < 631^49`
  with a Lean check, then use monotonicity in `k`.

You may also show:

```lean
theorem mod42Cheap_family_has (k : ℕ) :
    HasModFortyTwoCheapAllocation (631 + 42 * k)

theorem mod42Cheap_family_sixthPower (k : ℕ) :
    SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1)
```

The second statement should reuse
`sixthPowerAllocationSieve_mod_one`, and is not evidence of
any exact GN or RHS witness.

If a general infinite-range lemma simplifies these exports, feel
free to expose that lemma instead. Prove a genuine unbounded family,
not just a bounded list of examples.

## Gate C — interpret the boundary, do not overstate it

Clearly distinguish in `report-004.md`:

- **Proved:** a particular core 554 has no cheap allocation;
- **Proved:** many (indeed infinitely many) other cores pass the
  *necessary-only* cheap allocation checks, with a trivial
  sixth-power sieve at `r=1`;
- **Not proved:** those passing cores arise from an actual
  `RamifiedSignedRootRoutingPacket`, or satisfy either exact
  endpoint equation;
- **Not proved:** global reconstruction failure or FLT7 closure.

The research conclusion must answer whether simply iterating
modular cheap filters has a credible path to an unconditional theorem,
or whether future work requires **source-coupled constraints**
linking the actual outer/inner carrier, integer chart and endpoint.

Do not assert that infinitely many passing cheap cores give actual
counterexamples or make FLT7 false. They show the current set of
necessary-only filters is too weak to derive absence *by itself*.

## Verification and reporting

Use whichever appropriate local build and verification procedures the
implementing environment supports. For new public theorems:

- source-level and focused Lean typechecking/build;
- proof-level tests (including contrasts with `554` and `589`);
- `#print axioms` output and confirmation that no `sorryAx`
  or fresh axioms are introduced.

Never modify stable FLT7 proof modules for presentation reasons.
Use only minimal new code if necessary. An unexpected false target,
an already-existing stronger lemma, or a redundant consumer should
be reported precisely, not forced through with hidden hypotheses.

Write:

- `findings-004.md`: relevant symbols, mathematics, attempted paths,
  failure/success and reason;
- `report-004.md`: Outcome A/B/C, checked statements, exact command
  results, axiom audit, interpretation and proposed next research target;
- `evidence/004-verification-summary.md` only for concise,
  durable, provenance-marked proof results.

`logs/` remains temporary and ignored. Do not archive huge output.

**Stop and report for review. No Git staging/commit/push/PR/merge.**
