# FLT7 re-entry handoff: GCNB-009A

## Gate

**OPEN for a new FLT7 branch only.**  Keep the R64/R65 frozen production tower
unchanged.  The entry point is the local carrier-ownership cutoff below, not a
claim of a completed descent or an FLT7 theorem.

## Reusable bridge

Use the generic theorem:

```lean
DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff
```

Its current kernel-checked specialization is:

```lean
DkMathTest.FLT.Prime.SevenRealCubic
  .currentLinearCarrier_not_mem_currentKernel_pow_succ
```

For `c : CurrentCommonPrimeCyclotomicPacket h q`, it proves:

```lean
currentLinearCarrier c ∉ c.address.currentKernel ^
  (14 * currentIdealPrimeMultiplicity c.residue.Q
    (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1)
```

The specialization uses `ofReal`, the real-cubic coordinate ideal
`RingHom.ker c.residue.evalReal`, and the current/conjugate degree-six kernels.
Its base cutoff is transferred from the R64 ring-of-integers ideal
`c.residue.Q` by `modelEquivRingOfIntegers`; its contraction step is supplied
by `Ideal.comap_map_eq_self_of_faithfullyFlat`.

## First task in the new branch

Create a successor-only wrapper or successor proof around the exact theorem
above, preserving all five explicit inputs to the neutral theorem:

1. current-to-conjugate membership transport through `star`;
2. `currentLinearCarrier_mul_conjugate`;
3. `residueFiberIdeal_eq_currentConjugateProduct`;
4. faithful-flat contraction for `ofReal`;
5. the R64 base cutoff transferred through the ring-of-integers equivalence.

Any next step must state which additional deterministic bridge it establishes.
In particular, a local cutoff alone does not allocate all current degree-six
factors and does not produce a contradiction.

## Still closed at this checkpoint

- global aggregation of current degree-six factors;
- a terminal counterexample contradiction;
- an FLT7 theorem.
