# GCNB-009A implementation report

## Result

Outcome A is reached at the stated local boundary.  The new neutral theorem
is in `DkMath/Lib/NumberTheory/ConjugatePrimeIdealOwnership.lean`, and the
current degree-six specialization is a test-only probe in
`DkMathTest/FLT/Prime/CurrentCarrierOwnershipProbe.lean`.  No file in the
closed `DkMath/FLT/Seven/` production tower was changed.

The probe proves:

```lean
theorem currentLinearCarrier_not_mem_currentKernel_pow_succ
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∉ c.address.currentKernel ^
      (14 * currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1)
```

This is a local ownership cutoff only.  It is not a global aggregation,
terminal contradiction, or an FLT7 theorem.

## Neutral theorem

```lean
theorem not_mem_primePower_succ_of_conjugate_norm_cutoff
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (Q : Ideal A) (P Pbar : Ideal B)
    (alpha alphaBar : B) (beta : A) (m : ℕ)
    (hstarMem : alpha ∈ P ^ (m + 1) → alphaBar ∈ Pbar ^ (m + 1))
    (hpair : alpha * alphaBar = f beta)
    (hmapPow : Ideal.map f (Q ^ (m + 1)) = P ^ (m + 1) * Pbar ^ (m + 1))
    (hcontract : Ideal.comap f (Ideal.map f (Q ^ (m + 1))) = Q ^ (m + 1))
    (hBetaNot : beta ∉ Q ^ (m + 1)) :
    alpha ∉ P ^ (m + 1)
```

Its hypotheses are deliberately minimal.  It assumes only a one-way
conjugate-membership transport, the paired product identity, the mapped
ideal-power factorization, the exact contraction equality, and the base
non-membership.  It assumes neither a prime ideal, a PID/UFD, a class-group
calculation, nor a named involution.  In particular, faithful flatness is not
hidden in the theorem: a specialization must supply the contraction equality
explicitly.

## Current degree-six discharge

For a `CurrentCommonPrimeCyclotomicPacket c`, the specialization uses:

| Neutral object | Current object / discharge |
| --- | --- |
| `A` | `SevenRealCubicInt.Ring` |
| `B` | `SevenCyclotomicDegreeSixInt.Ring` |
| `f` | `SevenCyclotomicDegreeSixInt.ofReal` |
| `Q` | `RingHom.ker c.residue.evalReal` |
| `P`, `Pbar` | `c.address.currentKernel`, `c.address.conjugate.currentKernel` |
| `alpha`, `alphaBar` | `currentLinearCarrier c`, `currentConjugateLinearCarrier c` |
| `beta` | `selectedRealPairCarrier c` |
| `m` | `14 * currentIdealPrimeMultiplicity c.residue.Q (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot)` |

The R64 ideal called `c.residue.Q` lives in the ring-of-integers model.  The
neutral theorem instead takes the compatible real-cubic coordinate ideal
`RingHom.ker c.residue.evalReal`.  The probe transfers the exact cutoff across
`modelEquivRingOfIntegers` using `c.residue.evalReal_kernel_eq` and
`Ideal.map_comap_eq_self_of_equiv`; no historical cutoff is used.

The five hypotheses are discharged as follows.

- `hstarMem`: a direct coordinate calculation proves that applying `star`
  sends the current local evaluation to the conjugate local evaluation; the
  induced equality of mapped kernels and `Ideal.map_pow` transport membership.
- `hpair`: `c.currentLinearCarrier_mul_conjugate`.
- `hmapPow`: `c.residueFiberIdeal_eq_currentConjugateProduct`, followed by
  `Ideal.map_pow` and `mul_pow`.
- `hcontract`: `Ideal.comap_map_eq_self_of_faithfullyFlat` for `ofReal`.
- `hBetaNot`: the R64 base cutoff
  `c.selectedRealPairCarrier_not_mem_Q_pow_succ`, transported through the
  ring-of-integers equivalence as above.

The reusable insight is thus a two-stage bridge: first transport a proposed
current-kernel ownership to the conjugate kernel through the explicit star
coordinate identity; then descend the product through an explicitly supplied
contraction equality.  This avoids conflating the cyclotomic carrier's
coordinate kernel with the ring-of-integers ideal where the R64 multiplicity
is measured.

## Audit and validation

The probe invokes
`DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff`
directly.  It does not call the historical oriented-carrier cutoff.

Both required declarations were audited with `#print axioms`; each reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
The changed Lean files contain no `sorry`, `admit`, `sorryAx`, `unsafe`,
`native_decide`, or newly declared axiom.

The following commands completed successfully:

```text
lake build DkMath.Lib.NumberTheory.ConjugatePrimeIdealOwnership
lake build DkMathTest.FLT.Prime.CurrentCarrierOwnershipProbe
lake build DkMath.FLT.Prime
lake build DkMath
```

The latter two builds replay pre-existing project warnings, including warnings
outside this checkpoint that use `sorry`; they do not originate in either new
Lean file.

## Re-entry status

**OPEN, only for a new FLT7 branch.**  The exact local ownership cutoff now
has a generic production theorem and a kernel-checked current specialization.
The remaining work is still separate: aggregating current degree-six factors,
deriving a terminal contradiction, and proving an FLT7 theorem were not
undertaken here.
