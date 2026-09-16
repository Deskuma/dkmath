# CPG-V1-004a — arbitrary target-congruence child observer

Date: 2026-09-12  
Status: complete

## Implemented theorem

Extended the existing production owner
[PrimeWorldRefinement.lean](../../../DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean)
with the requested theorem:

```lean
DkMath.NumberTheory.Primitive.existsUnique_child_eq_target
```

Its statement is:

```lean
theorem existsUnique_child_eq_target
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S)
    (a : ZMod q) :
    ∃! j : ℕ,
      j < q ∧
      (primeWorldChild S r j : ZMod q) = a
```

The proof constructs the bounded CRT representative with target `a.val` and
old coordinate `r`. The old-modulus congruence yields a decomposition
`z = r + j * primeWorldModulus S`; the CRT bound gives `j < q`. The equality
`a = (a.val : ZMod q)` converts the natural `Nat.ModEq` result to the requested
`ZMod q` equality. For uniqueness, cancellation of the old modulus modulo `q`
uses the fresh-prime coprimality already provided by the module.

Added the focused regression
[PrimeWorldChildTarget.lean](../../../DkMathTest/NumberTheory/PrimeWorldChildTarget.lean).
It checks targets `0`, `3`, and `6` in the concrete world `{2, 3, 5}` with
fresh `q = 7`, and verifies the concrete target-`3` witness is index `1`.

## Scope boundary

- This generalizes the finite child coordinate observer from zero target to an
  arbitrary `ZMod q` target.
- The child remains a candidate coordinate; no primality, Goldbach existence,
  short-interval, or universal escape conclusion is added.
- The existing zero-target theorem is retained and was not silently treated as
  the arbitrary-target theorem.
- This prerequisite does not yet construct paired left/right Goldbach
  reserved children; that is CPG-V1-004.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement \
  DkMathTest.NumberTheory.PrimeWorldChildTarget
```

Result: exit 0, `Build completed successfully (3003 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-004a-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the changed production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for `existsUnique_child_eq_target`: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-004a` is complete. The next checkpoint is `CPG-V1-004`, the paired
fresh-prime refinement, which must use the arbitrary-target observer for the
left and right Goldbach targets without conflating raw and proper obstruction.

