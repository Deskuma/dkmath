# Codex instruction-006 — centered integer-image exclusion at M=589

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-005.md` (Outcome B accepted)
Implementer: GPT-6.1 Sol (light)

## One mathematical target

The cheap filter allows `(M,r)=(589,1)`, but this does not
establish an exact nested GN/RHS receiver. Test a **different,
stronger obstruction**: the target of the existing centered integer
sextic lies strictly between two adjacent image values.

The sixth-power *literal equality* hypothesis from the previous
perfect-sixth route is **not required** in this experiment.

We already have (read and reuse the actual Lean declarations):

- `DkMath.FLT.Seven.centeredSevenSextic`,
  `centeredSevenSextic_strictMono`,
  `nestedAllocation_iff_centered` in
  `SevenRamifiedFusionCenteredPolynomial.lean`;
- `centeredSevenSextic_no_image_of_adjacent_bracket` in
  `SevenRamifiedFusionCenteredGnomonGap.lean`;
- `SixthPowerSievedNestedCondition`,
  `internalDepthFourReconstruction_iff_sixth_power_sieved`,
  and existing `M.divisors` and coarse-bound lemmas;
- `ModFortyTwoCheapAllocation 589 1` from the gate-003
  test `candidate589_passes`.

## Independent arithmetic precheck — NOT YET A LEAN PROOF

Let

```text
D = 7^27 = 65712362363534280139543
F(D,q) = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6
T = 448*589^49
k = 52382010648825907313680
```

Python arbitrary-precision integer evaluation verified the **strict**
bracket

```text
F(D,k) < T < F(D,k+1).
```

This result must be independently confirmed by Lean before it becomes
a proof. The nearby interval is for the actual polynomial defined
in the repository, not a numerical interpolation or approximation.

## Requested Lean results (example API shapes)

1. Prove two strict inequalities `F(D,k)<T` and
   `T<F(D,k+1)` in Lean, using whatever exact arithmetic,
   reduction or efficient certificate the implementer finds suitable.
   Do not assert a result based only on the Python precheck.

2. Reuse the existing adjacent-image theorem to prove:

```lean
theorem centeredSevenSextic_589_no_image :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * 589 ^ 49
```

3. Use `nestedAllocation_iff_centered` to exclude the **exact**
   `NestedGNAllocationCondition 589 1 ∨
     NestedRHSAllocationCondition 589 1`.
   The scalar chart equation is
   `64 * (7*(589/1)^49) = 448*589^49`.
   Preserve the actual centered candidate's parity,
   positivity, orientation and coprimality premises; the
   no-image theorem may simply forget those extra constraints.

4. If the above checks, upgrade the pointwise exclusion to
   `¬ SixthPowerSievedNestedCondition 589` by proving that every
   eligible divisor `r` must equal 1:
   `r ∈ 589.divisors` gives `r>0`, and
   `343*r^7<589` excludes `r≥2`.

5. A thin conditional source consequence is optional:

```lean
theorem no_reconstruction_of_core_eq_589
    (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 589) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

Reuse the *existing* reconstruction iff, not a new chart constructor.
This implication does **not** assert that any packet with core 589
exists, nor that FLT7 is proved.

The implementer may choose better theorem names/API factoring. Do
not duplicate existing lemmas merely to reproduce the suggested
shapes.

## Research significance and boundaries

This differs from gates 003–004: `589` **passes** the mod-42
necessary filter, yet its *exact integer centered image* would be
excluded by an adjacent-value bracket, rather than an unproved
perfect-sixth assumption.

A single-core result is useful as a verified new obstruction, but
**cannot** be extrapolated to an arbitrary `M` or to the infinite
cheap-survivor family. In particular do not claim
`¬ HasModFortyTwoCheapAllocation 589`; that proposition is
false, as already checked.

If the large numeral certificate is expensive or fails to verify,
find the smallest genuine subproblem and report it. A cheaper
independent proof using existing arithmetic is welcome.
Do not solve complexity issues by adding axioms, `sorry`,
`admit`, `unsafe`, `native_decide` in place of proof, or
a fake chart constraint.

**Do not restart a global source-coupling audit in gate 006**;
the prior map remains the accepted reference. The purpose here
is to test a fresh exact-image obstruction without forcing
`M/r=t^6`.

## Artifacts, tests and finish

Implement only the minimal genuinely new theorem(s) and tests.
A small new production module next to the centered gap family is
appropriate if the certificate compiles; local environment/build
choices belong to Codex.

Write:

- `findings-006.md` — checked symbols, both strict inequality
  checks, failures/changes, whether the path is sound;
- `report-006.md` — Outcome A/B/C, exact APIs, theorem meaning,
  tests, proof limits, proposed next question;
- `evidence/006-verification-summary.md` — only compact,
  source-attributed proof evidence if formal verification was done.

For new exports, run appropriate focused Lean checks and
`#print axioms`; report actual exit status and unexpected
axioms. `logs/` is disposable; no large transcript is needed.

**Codex only implements, verifies and reports. Do not stage, commit,
push, create branches or PRs, or merge. Stop after gate 006.**

Outcomes:
- **A:** the centered no-image theorem and fixed-core exact
  exclusion are Lean checked (full-sieve exclusion if obtainable);
- **B:** a smaller rigorously checked bracket / candidate exclusion
  with a precise remaining bridge;
- **C:** precise obstacle, false claim or incomplete certificate.
