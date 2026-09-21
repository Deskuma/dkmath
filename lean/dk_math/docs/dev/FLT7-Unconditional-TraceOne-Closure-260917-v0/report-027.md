# FLT7TC-005R21 — Sign-free three-conjugate gap height and strict smaller norm

## Scope

Instruction-027 was implemented over the current
`DirectOrbitPowerSplitPacket`.  The construction stays receiver-free: it does
not create a successor arithmetic state and does not assert infinite descent
or unconditional FLT7 closure.

## Implemented results

The new production module
`DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitGapHeight` now provides:

- one chosen complex embedding, its total-reality reduction, and the composed
  `realEval : SevenRealCubicInt →+* ℝ`;
- cyclic real evaluation of the existing cubic norm identity;
- the `seventhQuotient`/`H7` evaluation formula and the three-cycle sign-free
  height inequality;
- the exact direct orbit norm product
  `norm gap * norm quotient = 7^35 * gapRoot^42`;
- positivity of both direct orbit norms;
- the stripped gap absolute-norm identity with the seventh-power root factor;
- the strict bound
  `Int.natAbs (norm gapRoot) < gapSplit.a`;
- `DirectOrbitSmallerNormPacket` and its constructor, including positivity and
  `gapSplit.a ≤ r.summit.gapRoot`.

The new module is exported by `DkMath.FLT.Seven`.  Dedicated API and axiom
test files were added.

## Boundary

The proof uses one real embedding and sign-free inequalities; it does not use
total positivity, maximal-real-subfield identification, numerical roots, the
unresolved projective unit classes, a successor state, or an infinite-descent
consumer.  The result is a strict smaller norm inside the current direct
provenance packet, not a general FLT7 theorem.

## Verification log

The source file was checked with:

```text
lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitGapHeight.lean
```

The following sequential builds also completed successfully:

```text
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitGapHeightApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitGapHeightAxiom
lake build DkMath.FLT.Seven
```

The axiom audit for the new production declarations reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The production source has
no `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom` declaration.
`git diff --check` and the corresponding new-file whitespace checks also
completed without diagnostics.
