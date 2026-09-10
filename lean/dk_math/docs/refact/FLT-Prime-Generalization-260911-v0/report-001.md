# FLT prime-generalization Phase 1 — PrimeAdicPowerSplit

## Scope

This report implements the bounded Phase 1 contract in `instruction-001.md`.
The generic production module does not import `DkMath.FLT.Seven`, and no file
under `DkMath/FLT/Seven/**` was modified.  The result is an odd-prime
arithmetic normal form; it is not a general FLT theorem and does not claim a
contradiction.

## Part A — promoted production API

The following probe results are now production declarations.

| Area | Production declaration | Classification | Minimal assumptions |
|---|---|---|---|
| Boundary gcd | `DkMath.CosmicFormula.gcd_GN_eq_gcd_of_one_le` | `CORE-PROMOTED` | `1 ≤ d`, `Nat.Coprime g u` |
| Prime gcd branches | `gcd_GN_prime_eq_one_of_not_dvd`, `gcd_GN_prime_eq_prime_of_dvd` | `CORE-PROMOTED` | `Nat.Prime p`, `Nat.Coprime g u`, and the indicated branch `p ∤ g` or `p ∣ g` |
| Prime divisibility address | `DkMath.CosmicFormula.prime_dvd_GN_iff_dvd_gap` | `CORE-PROMOTED` | `Nat.Prime p`; no coprimality or positivity |
| Mod-`p²` head | `DkMath.CosmicFormula.GN_modEq_head_mod_sq_of_odd_prime_dvd_x` | `CORE-PROMOTED` | `Nat.Prime p`, `3 ≤ p`, `p ∣ g` |
| Exact residual valuation | `DkMath.CosmicFormula.padicValNat_GN_prime_eq_one_of_dvd_gap` | `CORE-PROMOTED` | `Nat.Prime p`, `3 ≤ p`, `Nat.Coprime g u`, `p ∣ g` |
| Direct residual square obstruction | `not_prime_sq_dvd_GN_of_dvd_gap` | `CORE-PROMOTED` | Same odd-prime assumptions as exact valuation |
| Coprime power split | `DkMath.Lib.NumberTheory.power_factor_split` | `CORE-PROMOTED` | `Nat.Coprime a b`, `a*b = x^d`; no prime or positivity assumption on `d` |
| Valuation conservation | `padicValNat_carrier_shape_of_mul_eq_prime` | `CORE-PROMOTED` | Prime/nonzero/product/residual-valuation hypotheses; no `3 ≤ p` |
| Divisibility consequence | `prime_pow_sub_one_dvd_carrier` | `CORE-PROMOTED` | Same generic valuation hypotheses |

The existing `5 ≤ p` mod-`p²` wrapper remains available.  The exact-one
residual theorem remains intentionally odd-prime only: at `p = 2`, the
boundary value `GTail 2 1 2 1 = 4` has 2-adic valuation 2.  Thus exact depth
one is `PGEN-BOUNDARY` at `p = 2`, while the divisibility-address and valuation
conservation APIs still include `p = 2` where their stated assumptions allow
it.

## Part B — generic packet and normal form

`DkMath.FLT.Prime.AdicPowerSplit` defines the minimal input
`PrimeAdicFactorPacket` with exactly the prime, oddness, positivity,
coprimality, ramified-divisor, and factorization assumptions.  Consequences
are derived rather than stored as packet fields:

| Packet step | Classification | Derived content |
|---|---|---|
| Prime residual divisibility | `PGEN-GREEN` | `p ∣ GTail p 1 g u` from `prime_dvd_GN_iff_dvd_gap` |
| Gap/residual gcd | `PGEN-GREEN` | `gcd g (GTail p 1 g u) = p` |
| Exact residual depth | `PGEN-GREEN` | `padicValNat p R = 1` for `3 ≤ p` |
| No residual `p²` layer | `PGEN-GREEN` | `¬ p² ∣ R` |
| Distinguished divisibility | `PGEN-GREEN` | `p ∣ x` from primality and `p ∣ x^p` |
| Stripping | `PGEN-GREEN` | `g=p*c`, `R=p*r`, `x=p*d` |
| Stripped coprimality | `PGEN-GREEN` | `Coprime c r`, then `Coprime (p²*c) r` |
| Normalized product | `PGEN-GREEN` | `(p²*c)*r=(p*d)^p` |
| Coprime power factorization | `PGEN-GREEN` | `p²*c=A^p` and `r=b^p` via the generic Mathlib-backed split |
| Prime extraction | `PGEN-GREEN` | `p ∣ A`, hence `A=p*a` |
| Carrier exponent arithmetic | `PGEN-GREEN` | `c=p^(p-2)*a^p`, hence `g=p^(p-1)*a^p` |
| Residual normal form | `PGEN-GREEN` | `R=p*b^p` |
| Distinguished normal form | `PGEN-GREEN` | `x=p*a*b` |
| Positivity | `PGEN-GREEN` | `0<a` and `0<b` from `g>0` and `R>0` |
| Coprimality transfer | `PGEN-GREEN` | `Nat.Coprime a b` |
| Residual unit condition | `PGEN-GREEN` | `¬ p ∣ b` from `¬ p² ∣ R` |

The public output is `PrimeAdicPowerSplit p g u x`, whose fields are the input
packet, positive `a,b`, coprimality, the three normal-form equalities, and
`¬ p ∣ b`.  Its constructor theorem is
`nonempty_primeAdicPowerSplit_of_packet`; a noncomputable choice wrapper is
also provided.

No step is classified `ASSUMPTION`, `MISSING-CORE`, or `FALSE` on the stated
odd-prime packet contract.  The only explicit boundary is the `p = 2`
failure of exact residual depth one.  Seven-specific algebraic layers remain
outside this module and are not claimed to follow from the normal form.

## Part C — Seven compatibility

`DkMathTest.FLT.Prime.AdicPowerSplitCompatibility` constructs a generic
`PrimeAdicFactorPacket 7 (z-y) y x` from the existing
`SevenAdicCounterexamplePacket x y z`.  It then derives
`PrimeAdicPowerSplit 7 (z-y) y x` and checks the corresponding shape:

```text
z - y = 7^6 * a^7
GN 7 (z-y) y = 7 * b^7
x = 7 * a * b
0 < a, 0 < b, Coprime a b, ¬ 7 ∣ b
```

The compatibility test does not require the generic witnesses to be
definitionally equal to the specialized Seven witnesses.

## Verification

Focused builds passed:

```text
lake build DkMath.Lib.Cosmic.GTailBoundary
lake build DkMath.Lib.Cosmic.GTailCongruence
lake build DkMath.Lib.Cosmic.GTailPadic
lake build DkMath.Lib.NumberTheory.PadicValNat
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMathTest.FLT.Prime.GeneralizationProbe
lake build DkMathTest.FLT.Prime.AdicPowerSplitCompatibility
```

The compatibility build printed axioms for the promoted declarations and the
generic final theorem.  Each reported only
`propext`, `Classical.choice`, and `Quot.sound`; no checked declaration
depends on `sorryAx` or a newly introduced `axiom`.

The requested `lake build DkMath.FLT.Seven` regression was also started.  Its
existing dependency graph reached the ungenerated target
`DkMath.FLT.Seven.SevenRealCubicThetaSeventhPower`, but produced no further
output or generated object for several minutes; the run was stopped with
exit code 130.  The focused Seven compatibility build above did complete, and
no source under `DkMath/FLT/Seven/**` was changed.

## Phase-1 boundary

Phase 1 is complete for the requested arithmetic normal form.  The next
seven-specific frontier is still downstream of this packet: `TraceOneInt
(-2)`, axis-depth, real-cubic, degree-six, and terminal ramified machinery.
Those routes were intentionally not generalized or modified here.
