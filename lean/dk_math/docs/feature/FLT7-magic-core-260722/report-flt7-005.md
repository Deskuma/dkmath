# FLT7-005 implementation report

## Outcome

Outcome A.  The direct mod-49 residue, primitive cyclotomic depth `0/1`
classification, terminal residual core, natural coprime bridge, and exact
`GN 7` valuation classification are complete.

## Files changed

- `DkMath/FLT/Seven/PrimitiveCyclotomicDepth.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenPrimitiveCyclotomicDepth.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-005.md`

## Exact theorem surface

- `cyclotomicSeven_substitution_expansion`
- `fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow`
- `not_fortyNine_dvd_cyclotomicSeven`
- `cyclotomicSevenToTraceOne_ne_zero_of_not_seven_dvd_right`
- `sevenAxisDepth_cyclotomicSeven_eq_one`
- `sevenAxisDepth_cyclotomicSeven_eq_zero`
- `sevenAxisDepth_cyclotomicSeven_eq_if`
- `exists_cyclotomicSeven_terminal_core`
- `not_seven_dvd_right_of_coprime_of_seven_dvd_sub`
- `sevenAxisDepth_cyclotomicSeven_nat_eq_one`
- `padicValNat_GN_seven_sub_eq_if`
- `padicValNat_GN_seven_sub_le_one`
- `padicValNat_GN_seven_sub_eq_one_iff`
- `not_fortyNine_dvd_GN_seven_sub`

## Direct expansion and mod-49 route

With `z=y+d`, the implementation proves directly

```text
Phi7(y+d,y)
 = d^6 + 7d^5y + 21d^4y^2 + 35d^3y^3
   + 35d^2y^4 + 21dy^5 + 7y^6.
```

For `d=7k`, the first six terms are explicitly written as `49` times an
integer polynomial.  Therefore

```text
49 ∣ Phi7(z,y)-7y^6.
```

If `49∣Phi7(z,y)`, subtraction gives `49∣7y^6`.  The proof cancels the
concrete nonzero integer factor `7`, obtains `7∣y^6`, and uses primality of `7`
to derive `7∣y`.  Thus `7∤y` forbids the second layer.  No LTE or ideal
factorization is used.

## Primitive saturation and terminal core

On `7∣z-y`, FLT7-002 gives one axis factor.  The mod-49 result excludes two
axis factors through FLT7-003, so the FLT7-004 maximal characterization forces
depth exactly `1`.  Off the gap channel the one-layer criterion forces depth
`0`.  The stable integer API is

```text
sevenAxisDepth (cyclotomicSevenToTraceOne z y)
  = if 7∣z-y then 1 else 0              (7∤y).
```

Consequently even `49∣z-y` produces only one primitive cyclotomic axis layer:
the surviving term `7y^6` is nonzero modulo `49`.

`exists_cyclotomicSeven_terminal_core` reuses the maximal terminal-core
theorem after rewriting the exact depth to one.  Its residual is nonzero,
not axis-divisible, has norm not divisible by `7`, satisfies exact norm scaling
by `7`, and lies on a norm shell at least one.

## Natural coprime and GN bridges

For `b≤a`, `Nat.Coprime a b`, and `7∣a-b`, divisibility of `b` by `7` would
also make `a=(a-b)+b` divisible by `7`, contradicting `gcd(a,b)=1`.  This
supplies the primitive integer right-endpoint hypothesis after casting.

The existing `GN_seven_sub_eq_traceOneNorm_negTwo` identity then identifies
the natural GN value with the natural absolute value used by `sevenAxisDepth`.
The summit classification is

```text
padicValNat 7 (GN 7 (a-b) b)
  = if 7∣a-b then 1 else 0
```

under `b≤a` and coprimality.  Convenient `≤1`, `=1 iff`, and
`49∤GN 7 (a-b) b` consequences are also exposed.

## Scope preserved

No general LTE, ideal ramification, PID/UFD/Euclidean/class-number argument,
general prime cyclotomic theorem, both-endpoints-divisible classification,
gap-valuation equality, FLT7 theorem, descent, or FLT3/FLT5 change was added.

## Verification and axiom audit

Focused builds, tests, forbidden-token scan, and `git diff --check` are run at
checkpoint close.  Exact exceptional axiom sets are:

- substitution expansion: `propext`;
- natural coprime right-endpoint lemma: `propext`, `Quot.sound`;
- all other audited summit theorems: `propext`, `Classical.choice`,
  `Quot.sound`.

No `sorryAx` or DkMath-defined axiom appears, and the implementation/test use
no active `native_decide`, `admit`, or `sorry`.

## Recommended FLT7-006 boundary

Build a primitive FLT7 counterexample packet and valuation-routing layer that
consumes the exact `GN 7` valuation bound.  Keep the next checkpoint free of
UFD/PID/ideal assumptions and stop before a complete descent or no-solution
theorem.
