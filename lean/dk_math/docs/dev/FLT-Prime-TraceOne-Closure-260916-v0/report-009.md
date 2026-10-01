# FPTC-009 report — generic odd-prime counterexample routing

## 1. Outcome

```text
Outcome A — GENERIC TWO-BRANCH COUNTEREXAMPLE ROUTING GREEN
```

The new low-level routing surface accepts a primitive positive odd-prime FLT
counterexample without assuming `p ∣ z - y`.  It exposes both branches:

```text
primitive counterexample
  |-- p ∣ z-y  -> PrimeAdicFactorPacket p (z-y) y x
  `-- p ∤ z-y  -> gap = a^p and GTail = b^p
```

The away branch is not declared contradictory.  FPTC-007 class-number work
and the FPTC-008 p=5 Golden packet bridge were not reopened.

## 2. Current front-end API audit

The existing production packet is:

```lean
PrimeAdicFactorPacket p g u x : Prop
```

with fields `prime`, `odd`, `gap_pos`, `distinguished_pos`,
`coprime_gap_unit`, `prime_dvd_gap`, and `factor_eq`.  Its downstream power
normal form is:

```lean
PrimeAdicPowerSplit p g u x
```

The checked arithmetic kernels are:

```text
DkMath.pow_eq_sub_mul_GN_of_add_pow_eq
DkMath.CosmicFormula.gcd_GN_prime_eq_one_of_not_dvd
DkMath.CosmicFormula.gcd_GN_prime_eq_prime_of_dvd
DkMath.Lib.NumberTheory.power_factor_split
```

The old provider stack also contains:

```text
DkMath.FLT.PrimeCounterexamplePack
DkMath.FLT.PrimeGe5CounterexamplePack
```

The former stores `hp`, `hxy`, `hyz`, `hyz_lt`, and `hEq`; the latter extends
it with `hp5`, `hx0`, `hy0`, and `hz0`.  These remain old-stack vocabulary and
were not imported into the new low-level production module.

The specialized packets audited are:

```text
DkMath.FLT.Five.CounterexamplePack
DkMath.FLT.Seven.CounterexamplePack
DkMath.FLT.Seven.SevenAdicCounterexamplePacket
DkMath.FLT.Three.EisensteinConjugateCoprimePacket
```

The neutral facts were extracted into the new production namespace rather than
copied from the specialized namespaces.

Status:

```text
FPTC-GENERIC-COUNTEREXAMPLE-API-AUDITED
```

## 3. Neutral primitive input and gap facts

The new structure is:

```lean
structure PrimitivePrimeCounterexample (p x y z : ℕ) : Prop where
  prime : Nat.Prime p
  odd : 3 ≤ p
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  coprime_x_y : Nat.Coprime x y
  equation : x ^ p + y ^ p = z ^ p
```

The following checked lemmas are provided:

```text
PrimitivePrimeCounterexample.y_lt_z
PrimitivePrimeCounterexample.gap_pos
PrimitivePrimeCounterexample.coprime_y_z
PrimitivePrimeCounterexample.coprime_gap_y
PrimitivePrimeCounterexample.gap_mul_GTail_eq
```

The first four establish `y < z`, `0 < z-y`, `Nat.Coprime y z`, and
`Nat.Coprime (z-y) y`.  The last one uses the existing cosmic identity and
returns exactly:

```text
(z-y) * GTail p 1 (z-y) y = x^p
```

No provider, q-adic, or fixed-exponent theorem is needed by this production
surface.

## 4. Gap-divisible branch

The front-door theorem is:

```lean
primeAdicFactorPacket_of_counterexample_of_prime_dvd_gap
    (P : PrimitivePrimeCounterexample p x y z)
    (hgap : p ∣ z - y) :
    PrimeAdicFactorPacket p (z - y) y x
```

It populates the packet from the generic facts and preserves `hgap` as the
packet's explicit `prime_dvd_gap` field.  The output type is exactly the type
consumed by the existing `PrimeAdicPowerSplit` and TraceOne packet chain; no
adapter fiction or cyclotomic coordinate construction is introduced.

Status:

```text
FPTC-GAP-DIVISIBLE-TO-PRIMEADIC-PACKET-GREEN
```

## 5. Away branch

For `hgap : ¬ p ∣ z-y`, the production theorems are:

```lean
away_branch_coprime_gap_GTail
away_branch_power_factor_split
```

They first apply the prime-GTail gcd theorem to obtain

```text
Nat.Coprime (z-y) (GTail p 1 (z-y) y)
```

and then apply `power_factor_split` to the checked factorization.  The result
is:

```text
∃ a, z-y = a^p
∃ b, GTail p 1 (z-y) y = b^p
```

This is a structural power split, not a contradiction and not a proof that
the away branch is empty.

Status:

```text
FPTC-GENERIC-GAP-AWAY-POWER-SPLIT-GREEN
```

## 6. Honest two-branch route

The route is exposed by:

```lean
inductive PrimeCounterexampleRoute (p x y z : ℕ) : Prop
  | away
      (hgap : ¬ p ∣ z-y)
      (gapPow : ∃ a, z-y = a^p)
      (residualPow : ∃ b, GTail p 1 (z-y) y = b^p)
  | ramified
      (packet : PrimeAdicFactorPacket p (z-y) y x)
```

and the constructor theorem:

```lean
counterexampleRoute_of_primitive
    (P : PrimitivePrimeCounterexample p x y z) :
    PrimeCounterexampleRoute p x y z
```

The branch condition is selected by an explicit `by_cases`; it is not hidden
inside a classical witness or choice.

Status:

```text
FPTC-GENERIC-TWO-BRANCH-ROUTE-GREEN
```

## 7. Downstream and fixed-exponent compatibility

The API audit confirms the downstream shape:

```text
PrimeAdicFactorPacket
  -> PrimeAdicPowerSplit
```

For p=7, an adapter from `Seven.CounterexamplePack` constructs the generic
primitive input.  Under `7 ∣ z-y`, the generic route returns exactly
`PrimeAdicFactorPacket 7 (z-y) y x`.  The existing
`SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket` returns the same target
type, while the specialized packet and valuation fields remain untouched.

For p=5, the analogous adapter from `Five.CounterexamplePack` returns exactly
`PrimeAdicFactorPacket 5 (z-y) y x` under `5 ∣ z-y`.  No claim was made that
the existing Branch-B-to-signed-Branch-A machinery is generic.

For p=3, positive primitive scalar data constructs the generic packet input in
the audit.  The existing production FLT3 vocabulary instead uses
`EisensteinInt = TraceOneInt (-1)` and an Eisenstein-specific packet.  No
generic-to-Eisenstein packet equality was asserted and no completed FLT3
theorem was changed.

## 8. Real front-end frontier

The checked answers to the required boundary questions are:

1. A primitive positive odd-prime counterexample does not directly enter
   `PrimeAdicFactorPacket`; that packet requires the explicit branch field
   `p ∣ z-y`.
2. For the current TraceOne architecture, the exact entrance gate is the
   ramified gap condition.  Its negation is routed separately rather than
   silently rejected.
3. No checked generic coordinate permutation/orientation theorem was found.
   p=5 and p=7 fixed-exponent orientation facts do not generalize here.
4. The strongest checked away-branch result is the simultaneous p-th-power
   split of the gap and `GTail` residual.
5. The old PrimeProvider stack contains conditional/provider routes.  In
   particular, the clean away refuter route is conditional on
   `TriominoCosmicNonLiftableGNBridge`; the older default route is documented
   as `sorryAx`-contaminated.  Neither is imported or treated as an
   unconditional generic theorem in this checkpoint.

Thus the exact architecture is:

```text
primitive odd-prime counterexample
        |
        +-- ramified gap branch
        |      -> PrimeAdicFactorPacket
        |      -> existing conditional TraceOne architecture
        |
        `-- away branch
               -> gap = a^p
               -> GTail = b^p
               -> separate arithmetic frontier
```

## 9. Validation

The following builds passed under Lean 4.34:

```text
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMathTest.FLT.Prime.PrimeCounterexampleRoutingApiAudit
lake build DkMathTest.FLT.Prime.PrimeCounterexampleRoutingAxiomAudit
```

The API audit includes p=5, p=7, and p=3 regression examples.  The axiom
audit reports only ordinary foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound` where applicable).  Fresh production and
test files contain no `sorry`, `sorryAx`, `admit`, `axiom`, or `unsafe` token.
`git diff --check` and the corresponding checks for untracked files are clean.

## 10. Stop boundary

FPTC-009 is classified and closed at the routing layer.  The away branch is
not advanced to a new contradiction proof.  FPTC-010 may summarize the public
facade and this exact two-branch architecture.
