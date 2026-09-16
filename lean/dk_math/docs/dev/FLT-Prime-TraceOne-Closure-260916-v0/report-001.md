# FPTC-001 report — finite class-group cardinality criterion

## Outcome

```text
Outcome A — FINITE CLASS-GROUP COPRIMALITY BRIDGE GREEN
```

The neutral finite-cardinality bridge, its Lean 4.34 API audit, the p=7
cardinality-route regression, and the load-bearing axiom audit are complete.
FPTC-000 work was preserved.  No class-number estimate or new FLT theorem was
added.

## Repository and scope audit

The current checkout is on
`research/FLT-Prime-TraceOne-Closure-260916-v0` at commit `2180029cb` when
this report was prepared.  The repository root is
`/home/deskuma/develop/lean/dkmath`, and Lake builds were run from its nested
Lean project `lean/dk_math`.

The required FPTC-001 documents and the existing neutral bridge were read
before editing.  The requested outer `SUMMARY.md` was not present at the
repository location searched; the checkpoint-local README, ROADMAP,
`instruction-000.md`, and `report-000.md` were available and were used as the
scope context.  The attached instruction was treated as a bounded
implementation contract, separate from the user's request.

The explicit non-goals remain in force: no Minkowski or class-number bound, no
generic coprimality theorem for the prime-discriminant TraceOne family, no
real-sector elimination, no arbitrary-power coordinate kernel, no p=3/p=5
adapter, no q-adic global descent, and no general FLT claim.

## Exact Lean and Mathlib API audit

The project toolchain is:

```text
Lean (version 4.34.0, x86_64-unknown-linux-gnu)
Lake version 5.0.0-src+293d5d0 (Lean version 4.34.0)
```

The focused audit file is
`DkMathTest/Lib/NumberTheory/ClassGroupTorsionCardinalityApiAudit.lean`.
Its `#check` output confirmed these DkMath declarations:

```text
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
  (R : Type) (p : ℕ) [CommRing R] [IsDomain R]

DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_subsingleton_classGroup
  [Subsingleton (ClassGroup R)] (p : ℕ)

DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing
  [IsPrincipalIdealRing R] (p : ℕ)

DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
  (hI : I ∈ nonZeroDivisors (Ideal R))
  (hfree : classGroupPTorsionFreeAt R p)
  (hIPrincipal : Submodule.IsPrincipal (I ^ p))
```

The finite-group APIs have these exact current signatures:

```text
orderOf_dvd_of_pow_eq_one
  {G} [Monoid G] {x : G} {n : ℕ} (h : x ^ n = 1) : orderOf x ∣ n

orderOf_dvd_card
  {G} [Group G] [Fintype G] {x : G} : orderOf x ∣ Fintype.card G

orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1

Nat.eq_one_of_dvd_coprimes
  (h_ab_coprime : a.Coprime b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
```

The audit also checked `Fintype.card`, `Nat.Coprime`, and
`Nat.Coprime.gcd_eq_one`.  For the generic neutral theorem,
`Fintype (ClassGroup R)` is taken as an explicit typeclass assumption.  This
is the weakest natural assumption for the class-group statement and avoids
adding number-field or principal-ideal hypotheses.  Under the p=7 Euclidean
carrier, `#synth` successfully supplied:

```text
Fintype (ClassGroup (TraceOneInt (-2)))
IsPrincipalIdealRing (TraceOneInt (-2))
IsDedekindDomain (TraceOneInt (-2))
```

The direct Mathlib principalization APIs were also checked:

```text
Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime
  [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Fintype (ClassGroup R)]
  {n : ℕ} (hn : n.Coprime (Fintype.card (ClassGroup R)))
  {I : Ideal R} (hI : (I ^ n).IsPrincipal) : I.IsPrincipal

FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime
  [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDomain R] [IsDedekindDomain R]
  [Fintype (ClassGroup R)]
  {n : ℕ} (hn : n.Coprime (Fintype.card (ClassGroup R)))
  (I : FractionalIdeal (nonZeroDivisors R) K)
  (hI : (↑(I ^ n)).IsPrincipal) : (↑I).IsPrincipal
```

An initial audit build failed because the p=7 examples used
`TraceOneInt (-2)` without importing the module that defines its carrier and
Euclidean instance.  The test-only import
`DkMath.FLT.Seven.QuadraticEuclidean` corrected that boundary.  It was not
added to the neutral production module.

## Implemented neutral bridge

The production module is
`DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean`.  It imports only the
existing neutral `DkMath.Lib.NumberTheory.IdealPowerFactor` layer and adds:

```lean
theorem classGroupPTorsionFreeAt_of_coprime_card
    {R : Type*} [CommRing R] [IsDomain R]
    [Fintype (ClassGroup R)] {p : ℕ}
    (hcop : Nat.Coprime p (Fintype.card (ClassGroup R))) :
    classGroupPTorsionFreeAt R p
```

The proof is the finite-group order argument.  For `a` with `a ^ p = 1`,
`orderOf_dvd_of_pow_eq_one` gives `orderOf a ∣ p`, while
`orderOf_dvd_card` gives `orderOf a ∣ Fintype.card (ClassGroup R)`.  The
coprimality hypothesis and `Nat.eq_one_of_dvd_coprimes` yield
`orderOf a = 1`, and `orderOf_eq_one_iff` yields `a = 1`.

The theorem is independent of FLT, primality of `p`, any particular
quadratic field, and any class-number estimate.

## Principalization decision

No new DkMath principalization convenience corollary was added.  The direct
Mathlib theorem `Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime` already
expresses the integral-ideal result with the same finite-cardinality idea and
is thinner than routing through the DkMath torsion predicate.  The existing
DkMath theorem remains available when its nonzero-ideal and torsion-predicate
interface is the intended abstraction.  Adding a wrapper would duplicate the
current Mathlib API without materially improving the public surface.

No optional Phase-26 FLT wrapper was added; the existing generic endpoint can
be supplied with `classGroupPTorsionFreeAt_of_coprime_card` by the caller, so
the neutral dependency direction is preserved.

## p=7 cardinality-route regression

The focused audit proves:

```lean
Nat.Coprime 7 (Fintype.card (ClassGroup (TraceOneInt (-2))))
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

The first follows from the existing p=7 principal-ideal-ring instance and
`card_classGroup_eq_one`; the second applies the new neutral bridge and repeats
the cardinality computation.  This establishes:

```text
FPTC-P7-CARDINALITY-ROUTE-CONSISTENT-GREEN
```

The FPTC-000 structural theorem
`classGroupPTorsionFreeAt_traceOneNegTwo_seven` remains the preferred p=7
production path and was not replaced by this longer regression proof.

## Validation

Successful focused builds under Lean 4.34:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMathTest.Lib.NumberTheory.ClassGroupTorsionCardinalityApiAudit
lake build DkMathTest.Lib.NumberTheory.ClassGroupTorsionCardinalityAxiomAudit
lake build DkMath.Lib
```

The API audit build completed all 8953 jobs successfully.  The only reported
messages are existing informational file markers and non-fatal style or
deprecation warnings elsewhere in the dependency graph.

The axiom audit file
`DkMathTest/Lib/NumberTheory/ClassGroupTorsionCardinalityAxiomAudit.lean`
prints:

```text
classGroupPTorsionFreeAt_of_coprime_card depends on
[propext, Classical.choice, Quot.sound]
```

No DkMath-defined axiom, `sorry`, `sorryAx`, `admit`, or `unsafe` was added in
the new production/test sources.  `git diff --check` and the repository
forbidden-source scan were run after the final edits.

## Remaining frontier and handoff

The formal bridge now available is exactly:

```text
Coprime(p, |ClassGroup R|)
  -> classGroupPTorsionFreeAt R p
```

What remains unproved for the generic FLT family is:

```text
Coprime(p, |ClassGroup (TraceOne prime-discriminant order)|).
```

The latter is an arithmetic class-number/coprimality problem and is not
implied by this checkpoint.  The next bounded checkpoint is FPTC-002,
`TraceOneInt` arbitrary-power coordinate kernel; no part of that work is
started here.
