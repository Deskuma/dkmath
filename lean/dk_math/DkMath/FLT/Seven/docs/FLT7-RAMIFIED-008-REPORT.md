# FLT7-RAMIFIED-008 verification and inference report

## Outcome

Outcome A for the receiver branch.

The checkpoint's initial correction was essential: `gapRoot = inner^7` does
not follow from RAMIFIED-007. The correct root to extract is the quadratic
summit root, using the receiver's residual seventh-power key.

## Lean facts fixed

The new module
`SevenBaseTerminalRamifiedQuadraticInnerRoot.lean` proves:

```text
IsUnit (gcd summit.root (conj summit.root))

receiver
  → ∃ innerRoot,
      summit.root = innerRoot^7
      norm innerRoot = residualNormRoot
      gcd(innerRoot.fst, innerRoot.snd) = 1

cyclotomicSevenToTraceOne(endpointLeft, endpointRight)
  = sevenAxis * innerRoot^49.
```

The second coordinate undergoes an exact internal drop:

```text
outer root.snd depth = 5
innerRoot.snd depth = 4

|innerRoot.snd| = 7^4 * innerVerticalRoot^7
|seventhPowerSndCore(innerRoot)| = innerHorizontalRoot^7.
```

The next immediate consequence was also implemented. Primitive coordinates
and seven-unit norm make the two cubic core factors coprime, hence:

```text
seventhPowerSndLeftCubic(innerRoot) = leftRoot^7
seventhPowerSndRightCubic(innerRoot) = rightRoot^7
```

with signed integer roots.

## Boundary and branch logic

The construction assumes the existing
`RamifiedCubicGapSeventhShapeReceiver`. It does not prove that every terminal
summit inhabits this receiver.

Thus the exact branch split remains:

```text
receiver false
  → residual or compensation seventh-power obstruction

receiver true
  → quadratic 49th-power layer
  → internal second-coordinate depth four
  → two signed cubic seventh-power equations.
```

No new Fermat endpoint pair is constructed, so this is not yet recursive
descent.

## Prediction for RAMIFIED-009

The most economical next module is a small integral cubic-order carrier with
the relation

```text
alpha^3 = 2*alpha^2 + alpha - 1.
```

The now-proved signed equations should be transported through exact norm
identities for

```text
a - alpha*n
a + (1 + alpha)*n.
```

The required verification order is:

1. define multiplication and norm by determinant;
2. prove both cubic-form norm identities;
3. define `pi = 1 + 2*alpha`;
4. prove `norm pi = -7`, `pi^3 = 7*epsilon`, and that `epsilon` is a unit;
5. prove the exact source-element difference formula.

Norms being seventh powers will not by itself justify element-level
seventh-power extraction in the cubic order. Conjugate-ideal coprimality,
class-group input, and unit classes must remain explicit later obligations.
Inverse cyclotomic reconstruction is also independent of RAMIFIED-009.
