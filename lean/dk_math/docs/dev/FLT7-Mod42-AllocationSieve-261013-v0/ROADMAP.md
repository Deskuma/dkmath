# ROADMAP — FLT7 Mod-42 Allocation Sieve

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Base: `develop` (first prepared 2026-10-13).
Current status: **Gates 001–004 and 006–016 ACCEPTED (Outcome A); gate 005 ACCEPTED (Outcome B); gate 017 Part A Outcome A / constructive bridge Outcome B; gate 018 ACCEPTED (Outcome A, derived ledger); gate 019 ACCEPTED (Outcome B); research PAUSED. No gate 020 authorized.** See `review-001.md` through `review-019.md`.
Local integration status: **CLOSEOUT READY** — Facade 17/17、tests 19/19、必須5 local checks成功、CI suite coverage設定済み。Remote CIは未実行。See [branch closeout summary](branch-closeout-summary-261014.md) and [closeout report](report-closeout-facade-261014.md). Research remains paused; no gate020.

## Goals and gates

| Gate | Scope | Exit evidence | Status |
| --- | --- | --- | --- |
| 000 | Read live existing receiver APIs; theorem-index duplicate check | Actual declarations and required hypotheses recorded | Source audit done; Codex to reconfirm |
| 001 | Primitive seventh-order residues modulo 6 | Two focused, kernel-checked lemmas for GN7 and alternating cyclotomic factor; audit | **ACCEPTED — Outcome A** |
| 002 | Divisor-aware allocation bridge to mod 42 | Both exact branches -> `M/r ≡ 1 (mod 42)`, plus exclusion lemma | **ACCEPTED — Outcome A** |
| 003 | Independent pre-endpoint arithmetic filter and discrimination audit | Necessary-only candidate filter, exact-to-cheap implication, strict screening example | **ACCEPTED — Outcome A** |
| 004 | Necessity-boundary audit | Globally exclude cheap core 554; prove an infinite cheap-survivor family; preserve exact-vs-cheap distinction | **ACCEPTED — Outcome A** |
| 005 | Same-packet source–allocation–chart audit | Inspect real carrier/norm ledger, divisor-one blind spot, missing chart bridge; optional genuinely new theorem | **ACCEPTED — Outcome B** |
| 006 | Centered integer-image bracket at M=589 | Strict adjacent-value bracket, exact centered receiver exclusion, all eligible divisors at M=589 | **ACCEPTED — Outcome A** |
| 007 | Modular image gap for the centered sextic | Uniform modulo-five missing image; unbounded cheap-but-not-exact family at divisor one | **ACCEPTED — Outcome A** |
| 008 | Divisor-dependent modulo-five image audit | General 5-unit r image obstruction s≡r² mod 5; same-r receiver exclusion; r=2 cheap + sixth-power discrimination | **ACCEPTED — Outcome A** |
| 009 | Mixed-obstruction fixed-core closure | Exhaust eligible divisors at M=9653618; exclude r=1 by mod42 and r=2 by mod5; prove full exact sieve false | **ACCEPTED — Outcome A** |
| 010 | Parametric mixed-obstruction family | Free-s mixed exact exclusion from residues and size; 63,800-core finite bounded progression | **ACCEPTED — Outcome A** |
| 011 | Unbounded prime-power primitive allocation | Primitivity forces r=1/2 for all M=2*13^n; all k of M=2*13^(6+4*k) have no exact sieve; injectivity | **ACCEPTED — Outcome A** |
| 012 | Generic prime-power primitive exclusion | Generic p-power primitive divisor theorem, residue-conditional full-sieve exclusion; p=223,n=2 regression | **ACCEPTED — Outcome A** |
| 013 | Complementary prime-support centered image | Mod13 unit-gap nonvanishing, 13|s and 13∤r exact receiver exclusion, composite r=3 regression | **ACCEPTED — Outcome A** |
| 014 | Small-coefficient primitive divisor family | For M=c*p^n, c≤343, eligible coprime r divides c; full exact sieve absent for all 3*13^n, n>0; injectivity | **ACCEPTED — Outcome A** |
| 015 | Prime-base avoidance and complement ownership | Eligible p∤r and p|M/r for c≤343,n>0; all c*13^n full-sieve excluded, even if 13|c | **ACCEPTED — Outcome A** |
| 016 | Seventh-power permutation-prime image frontier | Generic seventh-power field injectivity and odd-prime nonvanishing, exact same-r receiver exclusion, c*ℓ^n full-sieve corollary; ℓ=11/13 and 29/2 diagnostics | **ACCEPTED — Outcome A** |
| 017 | Source-indexed obstruction and chart existence frontier | Three conditional actual-core/finite-chart exclusions; no constructive source→primitive endpoints; exact missing formula documented | **Part A ACCEPTED — Outcome A; bridge Outcome B** |
| 018 | Intrinsic source-prime valuation conservation | Same-packet V/C coprimality, prime valuation conservation, exclusive multiplicity; established as derived readout, no new M bound | **ACCEPTED — Outcome A (derived)** |
| 019 | Independent source-constraint discrimination | Scalar M=29² model verified; genuine source complementary N>1 proved in test; no new M-only restriction or endpoint | **ACCEPTED — Outcome B; PAUSED** |

After each gate, pause for human/Wise Wolf review before issuing the next
implementation instruction. Do not autonomously expand 001 into 003.

## Gate 001 — completed; approved in review-001.md

1. Search all relevant declarations in current `develop`-derived branch.
2. Establish the two bare arithmetic facts with correct coprimality:
   `Nat.Coprime D u -> GN 7 D u ≡ 1 (mod 6)`,
   `Nat.Coprime x y -> alternatingCyclotomicSeven x y ≡ 1 (mod 6)`.
3. Write them in one new production Lean file, with a minimal import.
4. Add focused Lean checks/tests and `#print axioms`.
5. Record exactly what was proved, which imports were used, build commands,
   error/failure attempts, and all remaining conditions.
6. Stop and hand the report back for review.

No new global FLT7 theorems in gate 001. **Implemented and reviewed**, see `report-001.md` and `evidence/001-verification-summary.md`.

## Gate 002 — implemented and accepted; review-002.md

Focused build, test applications and three axiom audits passed; see `report-002.md` and `evidence/002-verification-summary.md`. Gate 003 authorized by review-002.md; implementation not yet started.

Re-use gate-001 and existing `nestedAllocation_residue_sieve`:

- For the GN branch prove `Nat.Coprime D u` using the exact receiver's
  `Nat.Coprime u (7*M)` **and** the separate `r ∣ M`.
- For the RHS branch use `Nat.Coprime u D` and
  `Nat.Coprime u (D-u)` from its interval bound.
- From `7*s^49 ≡ 1 (mod 6)` derive `s ≡ 1 (mod 6)`,
  using `s^49 ≡ s (mod 6)`.
- Combine `s ≡ 1 (mod 6)` and `s ≡ 1 (mod 7)` into mod 42.
- Add an exclusion lemma from failure of this necessary congruence,
  retaining its divisor hypothesis.

The new theorem must **not** remove a receiver's divisibility guard simply
because an adjacent existing lemma does not need that guard modulo 7.

## Gate 003 — completed and accepted (review-003.md)

Construct a pre-endpoint arithmetic filter independent of the exact receiver predicates. Prove a correct exact-to-cheap implication and check its screening power relative to previous necessary-only guards. Do not merely append mod 42 to a predicate already containing exact endpoint equations. Do not assert that a necessary congruence is sufficient or that all receivers are empty.

Codex only implements, validates, and reports; **no commit, push, PR, or merge instructions to Codex**. Wise Wolf publishes reviewed instruction/review documents. The user makes repository integration decisions.

## Gate 004 — completed and accepted (review-004.md)

Audit the global reach and the limitations of the necessary-only arithmetic filter: show a concrete core excluded for *all* divisor allocations, and exhibit an unbounded family that passes the cheap conditions without asserting any endpoint witness. These are structural boundary certificates, not FLT7 closure. Then stop for review and identify whether a source-coupled invariant is the next target.

## Gate 005 — completed and accepted (Outcome B; review-005.md)

Locate the first source-specific condition linking the actual internal carrier and norm ledger to the **same selected allocation** and centered chart. Distinguish known source results from a new restrictive bridge. Explicitly inspect the divisor-one blind spot in the prime-support route. A documented negative result and exact missing theorem are valid outcomes; do not merely repackage existing exact receiver equivalences or add arbitrary modular filters. Codex handles implementation/audit and reporting only, with no Git operations.

## Gate 006 — completed and accepted (Outcome A; review-006.md)

An independent Python arbitrary-precision check found the centered target for M=589 and r=1 strictly between consecutive integer polynomial values. Formalize that strict bracket in Lean using the already-proved monotone-image exclusion. Then, if the proof succeeds, transport to exact receiver nonexistence at this **single core**, including the full divisor-allocation sieve via the coarse size guard. Do not infer no cheap allocation at 589 (it does pass the cheap filter), arbitrary-core emptiness, or unconditional FLT7. This is a fresh exact-image route, not a forced perfect-sixth conjecture or a repeat of the same-packet audit.

## Gate 007 — completed and accepted (Outcome A; review-007.md)

Investigate a uniform **modulo-five image obstruction** of the existing exact centered sextic for r=1. Derive a missing-target-residue theorem for all M≡1 (mod 5), then formally contrast an unbounded family of cheap passing allocations M=631+210*k with absence of exact GN/RHS endpoint witnesses at the **same fixed divisor one**. Do not generalize r=1 exclusion to all divisors for unbounded M, or conflate this local-image test with the adjacent integer bracket at 589. Treat the residue observations as unproved prechecks until Lean accepts them.

## Gate 008 — completed and accepted (Outcome A; review-008.md)

Examine the **actual divisor-dependent centered gap** D=7^27*r^49. A Python-checked residue table suggests that when 5∤r, a complementary factor s≡r² (mod 5) is outside the centered target image. Formalize that statement in Lean, then transport to the exact receiver and verify a concrete fixed allocation with r=2 that still passes both the existing cheap filter and separate sixth-power sieve. Exclusion of the chosen r does not establish absence of all allocations at M. No new general FLT7 or reconstruction conclusion is authorized.

## Gate 009 — completed and accepted (Outcome A; review-009.md)

Synthesize the already-proved mod42 necessary-condition exclusion and general-gap mod5 exact-image obstruction **without altering the chosen divisor**. At M=9653618, prove the membership+coarse-size premise forces r=1 or r=2, apply different exact receiver exclusions to these cases, and if successful prove the entire fixed-core SixthPowerSievedNestedCondition false. This is *not* a general FLT7 theorem. Codex implements/verifies/reports only and performs no Git actions.

## Gate 010 — completed and accepted (Outcome A; review-010.md)

Generalize the mixed mod42 and mod5 exact allocation obstruction to a parameter s: if s≡1 (mod42), s≡4 (mod5) and 2*s<343*5^7, all eligible divisors of M=2*s should be excluded. Derive this by the actual divisor and coarse bound guards; do not wrap an unproved global exclusion as an assumption. If successful, apply it to M=2*(589+210*k) for k≤63799 (63800 distinct bounded cores). Preserve the finite bound; the same argument does not automatically reach an infinite family or actual source packet values. Codex only implements, checks and reports, with no Git operations.

## Gate 011 — completed and accepted (Outcome A; review-011.md)

Look beyond gate 010's finite size window: exploit the existing **Nat.Coprime r (M/r)** premise in the exact full sieve for M=2*13^n. For an eligible r containing 13, its coprime complement should divide 2, contradicting the coarse size guard; otherwise r divides 2. Formalize this dichotomy, then use the already proved mod42 obstruction at r=1 and mod5 centered-image obstruction at r=2 for every M=2*13^(6+4*k). Check genuine unboundedness/injectivity. This is a proposed source-free arithmetic full-sieve exclusion, not a claim about actual source packet occurrence or FLT7 closure. Codex implements/verifies/reports only; no Git operations.

## Gate 012 — completed and accepted (Outcome A; review-012.md)

Separate the structural prime-power ownership proof from the special residue computations for 13. For arbitrary prime p and exponent n, membership plus actual quotient coprimality and coarse size should imply eligible r=1/2. Under additional **explicit** congruences p^n≡1 (mod42) and p^n≡4 (mod5), prove absence of the exact full-sieve at M=2*p^n. Verify p=223,n=2 as a distinct prime-base regression. The assumptions do not hold for all primes/exponents; do not infer arbitrary-M impossibility, source-packet existence, or FLT7 closure. Codex implements, checks and reports only; no Git operations.

## Gate 013 — completed and accepted (Outcome A; review-013.md)

Test a new *factor-support* obstruction rather than another necessary congruence on s alone. For the actual centered sextic, a Python residue enumeration suggests that 13∤D forces its mod13 image to avoid zero. Since D=7^27*r^49, 13∤r and 13|s would then make F(D,q)=448*s^49 impossible, excluding the same chosen exact receiver. Verify this universally in Lean, and check the concrete composite allocation M=3*13^12, r=3: previous cheap, literal-sixth and mod5 image-compatibility tests pass, while the new mod13 obstruction should reject the exact receiver. No full-sieve exclusion follows from a single chosen divisor; no source packet or FLT7 closure is claimed. Codex reports results without Git actions.

## Gate 014 — completed and accepted (Outcome A; review-014.md)

Investigate a structural coefficient bound: if M=c*p^n with p prime and c≤343, the full-sieve's actual quotient coprimality and coarse inequality should force any eligible r to divide c. At c=3,p=13 this leaves r=1/3; the r=1 exact receiver violates the existing mod42 condition because M is divisible by3, while r=3 violates the gate-013 mod13 prime-support image condition for n>0. If Lean checks both, prove full exact-sieve exclusion for all n>0 and an injective infinite core family M=3*13^(k+1). This is an unproved target until implemented; not actual source packet existence or FLT7 closure. Codex only implements/verifies/reports and never commits or pushes.

## Gate 015 — completed and accepted (Outcome A; review-015.md)

Gate 014's proof rules out the p|r branch, a stronger fact than its exported conclusion r|c. Formalize this **prime-base avoidance** for every eligible primitive allocation of c*p^n (prime p, c≤343); when n>0, exact factorization and prime divisibility put p on the quotient M/r side even if p divides c. For p=13 apply gate 013's exact centered image exclusion to the same selected r, aiming to prove ¬SixthPowerSievedNestedCondition (c*13^n) for **all** c≤343 and n>0. Optional n=0 is a separate size-vacuity proof. No actual packet existence, arbitrary-M sieve closure or FLT7 proof is implied. Codex only implements/verifies/reports; no Git operations.

## Gate 016 — completed and accepted (Outcome A; review-016.md)

Explain the mod13 nonvanishing structurally via the identity 2D*F(D,q)=(q+D)^7−(q−D)^7 over a ring and finite-field injectivity of seventh powers. For odd prime ℓ with gcd(7,ℓ−1)=1, test general nonvanishing when ℓ∤D and translate it into a support-based exact receiver exclusion when ℓ≠7, ℓ∤r and ℓ|M/r. Check ℓ=11 as a genuine new positive example and ℓ=29,D=1,q=5 as a counterexample to unrestricted prime generalization. A broad small-coefficient ℓ-power corollary is optional. Keep mathematical prechecks distinct from Lean proofs; do not infer actual source-packet core realization or FLT7. Reassess returning to the gate-005 source bridge after 016. Codex implements/verifies/reports only, with no Git actions.

## Gate 017 — Part A accepted; bridge unresolved (review-017.md)

After gate 016's completed structural prime-field theorem, **return to the genuine source-frontier**. For p:RamifiedSignedRootRoutingPacket with explicit equality internalDepthFourSeventhCore p=c*ℓ^n (prime ℓ satisfying odd, non7 and seventh-power permutation conditions; c≤343,n>0), transport the full-sieve obstruction through the proven iff to exclude p's reconstruction obligation and finite additive charts. This is strictly **conditional on the core equality** and does not restrict bare p by itself. Audit the actual same-packet norm roots, complementary factor, real-pair loads, orientation and finite chart construction; identify the first *unsupplied constructive arrow*, without using a reconstruction obligation to prove its own existence. Record a precise missing lemma and honest Outcome B if no further source-side bridge is available. No new modulus hunt or FLT7 claim. Codex implements and reports only, no Git operations.

## Gate 018 — accepted as derived source ledger (review-018.md)

The required source-to-chart additive pair remains unavailable and must not be manufactured from bare packet p or a reconstruction iff. Explore a **source-only valuation conservation theorem** for the actual inner core M, its genuinely sourced complementary root N and the product V*C, with M*N=V*C and Coprime M N. For each prime ℓ|M, test ℓ∤N and vℓ(M)=vℓ(V)+vℓ(C) using the correct positive-factor valuation API. Check existing source prime-support theorem for duplicates and distinguish this local conservation from an unsupported small-coefficient factorization or chosen exact receiver divisor. If only a restatement is possible, report Outcome B and reconsider strategy; no FLT7 closure is authorized. Codex implements/verifies/reports only and performs no Git operations.

## Gate 019 — completed (Outcome B); strategic pause (review-019.md)

After gate 018's source valuation readout, test whether the **scalar ledger alone** could imply a gate-016 usable prime-power factorization. A finite arithmetic example M=29², N=1, V=M, C=1 meets positivity, product equality, both coprimality conditions and 7-nondivisibility but has no prime factor satisfying gcd(7,ℓ−1)=1. This is **not** an actual packet or FLT7 witness. Inspect genuinely independent source quadratic-coordinate, cubic-norm, ramified-axis and orientation statements for a stronger necessary condition on actual M. Prove one only if warranted; otherwise record an honest negative frontier, recommend a strategic pause and do not automatically launch 020. Neither this scalar model nor an API failure proves no source-side bridge can ever exist. Codex implements/tests/reports only; no Git actions.

## Research pause after gate 019 — no gate 020 authorization

The gate-019 scalar-ledger model M=841,N=1,V=M,C=1 has no prime satisfying the gate-016 permutation condition, but is **not** an actual source packet. The actual same-coordinate cubic source proves N>1, so that scalar tuple cannot realize the source's complementary root; M=841 with some other source factors is not excluded. The new proof is test-only and proves no M-only factorization bound. Source facts still do not supply primitive natural endpoints at the prescribed carrier or a provable factorization M=c*ℓ^n, c≤343 with a usable prime. Stop adding gates until a concrete independent source-side mechanism and falsifiable target are specified. Potential research redesign topics: eliminate auxiliary A and signed cubic norm roots using their simultaneous equations with B=7^4*m^7, or find a sound orientation/positive-endpoint descent with a proven well-founded measure. These are research directions **not** instructions to Codex. No instruction-020 exists/has been authorized; the user controls a future restart.

## Explicit non-goals

- No unconditional FLT7 proof or strict descent claim.
- No new inhabited `InternalDepthFourCounterexampleReconstructionObligation`.
- No diagonal arguments based solely on smaller 7-adic carrier depth.
- No redo of GTailSelection, GTailFactor, GTailTransport, GTailSeven.
- No changing existing production file proofs to conform to a new aesthetic.
- No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` as a proof
  substitute, or untracked assumptions.
- Build strategy is for the local implementing agent to decide; no hardware-dependent restrictions in instructions.

## Negative-evidence rule

A sieve can exclude local allocation candidates without showing global
impossibility. Record the surviving cases as clearly as exclusions.
In particular, for `r=1` the modulus `r^49=1` makes the existing
`SixthPowerAllocationSieve` vacuous; the new mod-42 condition is a
different necessary filter. The Python slice (`r=1, s=589`) cannot be
promoted to all `M,r`.

## Source control roles

Codex is not responsible for Git staging, publication, commits, pushes, branch creation, PRs, or merges. Review and instructions are published to the research branch by Wise Wolf (ChatGPT); integration decisions remain with the user.

## Records and logs policy

`logs/` is temporary and ignored by Git; do not commit bulk output. Store only compact, decisive, provenance-marked artifacts in `evidence/` (see `evidence/README.md`), and summarize command outcomes in the gate report. Tool/resource choices are left to the executing Codex environment.

## Deliverables per cycle

For gate N, create and update `findings-NNN.md` early, and write
`report-NNN.md` at the stable stopping point. Gate 005 additionally
requires `source-coupling-map-005.md`. Existing reports remain authoritative
for earlier gates.
Report status as:

- Outcome A: goal fully kernel-checked with correct premises.
- Outcome B: a strictly narrower correct lemma that advances the gate.
- Outcome C: blocked or falsified; give the exact counterexample / missing
  premise / compiler error, do not insert false hypotheses.

Include an inventory of touched files, commands, output, axiom list, and
one proposed next step. Stop after the gate.
