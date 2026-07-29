# FLT7-TERM-009 implementation report

## Outcome

Outcome C: the planned terminal chart resolution is complete, and the exact
remaining bridge has been isolated.

```text
Row Y   -> swapped natural ramified chart
Row Sum -> contradiction
Row Z   -> signed primitive ramified-gap chart
           + one signed quadratic extraction obligation
```

This is not terminal exclusion and is not an FLT7 proof.

## A. Natural summand exchange

Implemented:

```lean
CounterexamplePack.swapXY
```

It preserves positivity, `Nat.Coprime`, and `Fermat7Equation`.

## B. Row Y

Implemented:

```lean
AwaySevenBaseTerminalRowYProfile.to_swapped_ramified
```

The Row-Y profile gives `7 ∣ y`.  The mod-seven Fermat equation then gives
`x ≡ z`, hence `7 ∣ z - x`.  Case analysis on the existing coordinate route
for `source.swapXY` excludes its away constructor and returns its ramified
constructor.

## C. Row Sum

Implemented:

```lean
AwaySevenBaseTerminalRowSumProfile.false_of_swapped_away
```

The Row-Sum divisibility selects the `awaySum` residue sector.  For the
exchanged chart, Lean proves:

```text
7 does not divide x
7 does not divide z
7 does not divide x + z
7 does not divide z - x
```

The last fact excludes the ramified route.  The resulting away route requires
`7 ∣ x * z * (x + z)`, and primality of seven contradicts the first three
facts.

## D. Signed odd-power chart

Implemented:

```lean
SignedFermatSevenChart
CounterexamplePack.signedOddPermutation
AwaySevenBaseTerminalRowZProfile.seven_dvd_signed_gap
```

The chart `(z,-y,x)` is nonzero, primitive over `ℤ`, and satisfies
`z ^ 7 + (-y) ^ 7 = x ^ 7`.  In Row Z its gap
`x - (-y) = x + y` is divisible by seven.

## E. Signed ramified extraction audit

The requested thin-wrapper route breaks at the natural/integer domain
boundary.  The existing ramified extractor depends on:

```text
SevenAdicCounterexamplePacket over Nat
natural subtraction z - y
GN 7 (z - y) y over Nat
strict positivity of gap and GN residual
padicValNat
natural coprime seventh-power factor splitting
SevenAdicPowerSplit with positive natural roots
```

The signed endpoint `-y` cannot enter that chain.  This is not a missing cast:
the factorization required by the signed chart is the alternating sum attached
to `x ^ 7 - (-y) ^ 7`, whereas the current implementation packages the
positive-natural difference chart through `GN`.

The exact continuation target is now recorded as:

```lean
AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation
```

It asks only for:

```lean
cyclotomicSevenToTraceOne (x : ℤ) (-(y : ℤ)) =
  sevenAxis * root ^ 7
```

and is sufficient to construct:

```lean
SignedRamifiedCoordinateNormalForm (z : ℤ) (-(y : ℤ)) (x : ℤ)
```

The completed decision theorem is:

```lean
AwaySevenBaseTerminalUnitSectorPacket.fermatChartResolution
```

It has no Row-Sum constructor.  Its only outcomes are the existing natural
Row-Y ramified chart or the fully verified signed Row-Z chart packet.

## Verification

Focused and facade builds:

```text
lake build DkMath.FLT.Seven.SevenBaseTerminalFermatChartResolution  success
lake build DkMath.FLT.Seven                                     success
lake build DkMath.FLT                                           success
```

`git diff --check` succeeds.  The new module contains no `sorry`, `admit`,
`native_decide`, or axiom declaration.  `#print axioms` on its public
construction and resolution theorems reports only the project-standard
`propext`, `Classical.choice`, and `Quot.sound`.

The aggregate `DkMath.FLT` build still reports pre-existing `sorry` warnings
in unrelated research modules; none is introduced or imported specifically
by TERM-009.
