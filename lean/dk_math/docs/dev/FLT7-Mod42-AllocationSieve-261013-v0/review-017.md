# Review 017 — Part A accepted, constructive source bridge remains Outcome B

Date: 2026-10-14
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation HEAD: `d8635347bfd3db86d26392491597d80b9169981e`

## Decision

**Part A: ACCEPTED — Outcome A. Constructive bridge: Outcome B, accurately localized.**
Reviewed actual production
`DkMath/FLT/Seven/SevenRamifiedFusionSourcePermutationPrimeObstruction.lean`,
test source, `report-017.md`, `findings-017.md`,
`source-bridge-frontier-017.md`, and
`evidence/017-verification-summary.md`.

Three exported source-indexed theorems:

1. `internalDepthFour_no_reconstruction_of_permutation_prime_core`
   uses an **explicit** equation for the actual chosen
   `internalDepthFourSeventhCore p = c*ℓ^n`, together with
   c≤343,n>0, ℓ prime, ℓ≠2,7 and
   `Nat.Coprime 7 (ℓ-1)`. By the proven
   source ↔ full-sieve equivalence and gate-016
   prime-power exclusion, reconstruction is impossible.
2. `reconstructed_core_ne_smallCoefficient_permutation_prime_power`
   is the valid contrapositive **under supplied reconstruction**.
3. `internalDepthFour_no_finiteCharts_of_permutation_prime_core`
   uses the existing finite-chart equivalence and the
   **same explicit hcore**. No additive chart existence
   is introduced or inferred.

All three retain same packet p. The proof does not
infer the core factorization from p, nor supply
`InternalDepthFourCounterexampleReconstructionObligation p`.
Codex reports focused Lake build (9091 jobs) and final
Lean test exit 0, three standard-axiom audits
`[propext, Classical.choice, Quot.sound]`,
no `sorryAx`. Reviewer inspected actual code and
compact evidence; **no independent local Lean build was run**.

## Bridge finding and interpretation

The source-bridge audit correctly distinguishes
these *source-only* ingredients:

- actual K, M=|K.innerSndRoot|, carrier=7^4*M^7,
  M>0 and 7∤M;
- actual positive complementary N with
  M*N=V*C, `Nat.Coprime M N`, 7∤N;
- source real-pair load/coprimality and
  associated seventh-power split.

In contrast:
- `internalDepthFourSummand_nested_normal_form`
  requires a **supplied**
  `CounterexamplePack u (internalDepthFourCarrier p) v`;
- loaded recovery's full-core branch additionally
  requires seventh powers of row-two cells;
- reconstruction ↔ finiteCharts is an **iff**,
  not a witness from bare p;
- the existing root-depth mismatch explicitly
  forbids simply identifying the old inner root
  with the required new away root.

The first missing constructive object on the finite-chart
route is a positive primitive natural additive pair
`u,v` for the **prescribed carrier**, satisfying
`u^7+Y^7=v^7` or `u^7+v^7=Y^7`
with appropriate coprimality and bounds.
The direct-use `fail_if_success` tests are
proof-API type checks, not a metatheorem that
such a bridge is logically impossible.

**Strategic caution.** Bare-packet → additive chart is
extremely strong: it constructs another FLT7-type
counterexample/away route. Do not regard the existence
of that pair as routine normalization of associated
ring powers. Any such construction must justify
new natural endpoints, orientation, positivity and
the Fermat additive equation. The source may instead
need an intrinsic contradiction or an intrinsic
restriction on M; none was newly supplied by gate 017.

## Next task choice — intrinsic arithmetic, not fabricated endpoints

Gate 018 will **not** demand a theorem producing
a finite chart from bare p. It will attempt a
small, unconditional, same-packet **prime-valuation
conservation ledger** from the already-proved
complementary-root factorization:

`M*N=V*C`, `Nat.Coprime M N`,
with M,N>0.

For every prime ℓ that divides actual M,
one has ℓ∤N and hence
`v_ℓ(M)=v_ℓ(V)+v_ℓ(C)`
provided valuations are defined on the positive
factors. This is a proposed arithmetic consequence
of the actual source ledger, **not yet a Lean export**.
It must be checked for duplicates and genuinely
add value beyond the existing source-indexed
prime-support routing theorem. The identity
does not identify chart divisor r, reconstruct
endpoints, or bound M/ℓ^n by 343; it cannot be used
as if it supplied those missing statements.

If possible, the resulting source-only invariant
should become a usable receiver **input** in a future
research step. If it yields only known facts or
cannot be sharpened, report that clearly and revisit
the strategy instead of fabricating stronger lemmas.

Gate 018 may also contrast conditional reconstructed-core
restrictions from 017 with these unconditional source
valuation facts. There is no permission to
claim unconditional FLT7 or core classification.

Codex: implementation, focused checking, reports only;
**no git add/stage/commit/push, branching, PR or merge**.
Wise Wolf publishes review and instructions.
