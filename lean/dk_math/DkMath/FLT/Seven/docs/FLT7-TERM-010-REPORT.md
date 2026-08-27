# FLT7-TERM-010 implementation report

## Outcome

Outcome A: the Row-Z alternating power split and signed residual-core
seventh-power extraction are complete.

The TERM-009 arithmetic receiver is inhabited.  Every surviving terminal away
row now reaches a ramified quadratic chart.

## Alternating natural factor

Implemented:

```lean
alternatingCyclotomicSeven
add_mul_alternatingCyclotomicSeven
alternatingCyclotomicSeven_intCast
```

Lean proves:

```text
(x + y) * A7(x,y) = x^7 + y^7
(A7(x,y) : Int) = cyclotomicSeven x (-y)
```

The signed substitution expansion gives `A7 ≡ 7*y^6 mod (x+y)`.  Primitive
endpoints therefore imply:

```lean
gcd_add_alternatingCyclotomicSeven_dvd_seven
```

and the Row-Z sum channel strengthens this to equality with seven.

## Exact Row-Z split

The Row-Z profile supplies `7 ∣ x+y`, `7 ∤ y`, and
`(x+y) * A7 = z^7`.  The existing signed cyclotomic depth theorem excludes
`49 ∣ A7`.

After dividing both factors by their common seven and assigning the remaining
`7^2` to the sum side, the normalized factors are coprime.  Natural unique
factorization produces:

```lean
AwaySevenBaseTerminalRowZAlternatingPowerSplit
```

with:

```text
x + y = 7^6 * a^7
A7(x,y) = 7 * b^7
z = 7 * a * b
Nat.Coprime a b
```

## Signed residual core

Implemented:

```lean
rowZ_signed_cyclotomicSeven_coordinates_isCoprime
AwaySevenBaseTerminalRowZSignedResidualCore
```

The integer endpoint pair `(x,-y)` is passed directly to
`exists_cyclotomicSeven_terminal_core`.  Its unique `sevenAxis` layer is
peeled, and the alternating split identifies the residual norm with `b^7`.

Signed cubic-coordinate coprimality implies every common divisor of the
cyclotomic coordinate and its conjugate divides `sevenAxis`.  Terminality of
the residual excludes that axis, giving:

```lean
AwaySevenBaseTerminalRowZSignedResidualCore.gcd_conj_isUnit
```

The existing TraceOne UFD extraction then proves:

```lean
AwaySevenBaseTerminalRowZSignedResidualCore
  .exists_residualCore_eq_seventh_power
```

## TERM-009 receiver and terminal decision

Implemented:

```lean
AwaySevenBaseTerminalRowZProfile
  .signedRamifiedArithmeticObligation
AwaySevenBaseTerminalRowZProfile.signedRamified
AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution
```

Thus:

```text
Row Y   -> natural ramified chart
Row Z   -> signed ramified chart
Row Sum -> impossible
```

The remaining boundary is the common ramified summit.  TERM-010 does not
prove terminal contradiction or FLT7.

## Verification

All requested verification succeeded:

```text
lake build DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit
lake build DkMath.FLT.Seven.SevenBaseTerminalRowZSignedResidualCore
lake build DkMath.FLT.Seven
lake build DkMath.FLT
git diff --check
```

The new Lean modules contain no `sorry`, `admit`, `native_decide`, or axiom
declaration.  `#print axioms` on the principal split, residual, extraction,
and final resolution APIs reports only the project-standard `propext`,
`Classical.choice`, and `Quot.sound`.

The aggregate `DkMath.FLT` build continues to display pre-existing `sorry`
warnings in unrelated research modules; TERM-010 introduces none.
