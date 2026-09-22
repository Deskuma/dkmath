# GCNB-005 / instruction-003 — Connect the generic FLT gap packet to the cyclotomic ideal carrier

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-002.md
- DkMath/CFBRC/CyclotomicIdeal.lean
- DkMath/FLT/Prime/AdicPowerSplit.lean
- DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5Core.lean
- DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
- DkMath/FLT/Prime/PrimeTraceOneCoordinateCoprime.lean

## 1. Mission

GCNB-004 completed the neutral arithmetic carrier:

~~~text
alpha = (g+u) - zeta*u
I_alpha = (alpha)

Ideal.absNorm I_alpha = GN p g u
g * Ideal.absNorm I_alpha = (g+u)^p - u^p
~~~

The generic FLT arithmetic front end already contains:

~~~text
PrimeGe5CounterexamplePack
PrimeAdicFactorPacket
PrimeAdicPowerSplit
~~~

with the key identities

~~~text
x^p = gap * GN p gap y
~~~

and, in the p-divides-gap branch,

~~~text
gap = p^(p-1) * a^p
GN p gap y = p * b^p
x = p*a*b
padicValNat p (GN p gap y) = 1.
~~~

The goal of this checkpoint is to connect those two existing towers without
specializing to p = 7.

The required representation chain is:

~~~text
generic FLT counterexample packet
    -> gap/base coordinates
    -> cyclotomic linear-factor ideal
    -> exact ideal absNorm = GN
    -> complete FLT equation through ideal absNorm
    -> ramified adic split when p divides the gap.
~~~

Do not perform TraceOne projection yet.

## 2. Module placement

Prefer a new FLT-generic adapter module:

~~~text
DkMath/FLT/Prime/PrimeCyclotomicIdeal.lean
~~~

This module may import:

~~~text
DkMath.CFBRC.CyclotomicIdeal
DkMath.FLT.Prime.AdicPowerSplit
~~~

and the minimum PrimeProvider module needed only if the
PrimeGe5CounterexamplePack constructor is implemented here.

Do not make CFBRC import FLT modules.

The dependency direction must remain:

~~~text
CFBRC generic carrier
        ↑
FLT.Prime adapter
~~~

not the reverse.

## 3. Generic arithmetic packet from PrimeAdicFactorPacket

First support the already normalized generic arithmetic input:

~~~lean
P0 : PrimeAdicFactorPacket p g u x
~~~

together with a cyclotomic extension K and primitive p-th root zeta.

Define a thin packet or theorem family that exposes the canonical carrier and
ideal at the same g,u.

Suggested shape:

~~~lean
structure PrimeCyclotomicIdealPacket
    (K : Type*) [Field K] [NumberField K] [CharZero K]
    {p g u x : Nat} [Fact p.Prime]
    [IsCyclotomicExtension {p} Rat K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    (P0 : PrimeAdicFactorPacket p g u x) : Type where
  ideal : Ideal (O K)
  ideal_eq :
    ideal = cyclotomicLinearFactorIdeal hzeta g u
  absNorm_eq_residual :
    Ideal.absNorm ideal = GTail p 1 g u
  gap_mul_absNorm_eq_distinguished_pow :
    g * Ideal.absNorm ideal = x^p
~~~

This exact structure is optional. A theorem family is acceptable if cleaner.

Do not duplicate carrier fields already definable canonically.

## 4. Required exact theorem: FLT equation through ideal absNorm

For every PrimeAdicFactorPacket prove the direct theorem:

~~~text
g * Ideal.absNorm
      (cyclotomicLinearFactorIdeal hzeta g u)
  = x^p.
~~~

The proof should be short:

~~~text
absNorm = GN = GTail
P0.factor_eq
~~~

or by combining the GCNB-004 complete-gap theorem with the packet's endpoint
identity if that is cleaner.

This theorem is the main GCNB-005 bridge.

It must preserve the distinguished x^p, not merely restate absNorm = GN.

## 5. Exact residual valuation and ramified split

PrimeAdicFactorPacket already assumes p divides g and proves:

~~~text
padicValNat p (GTail p 1 g u) = 1.
~~~

Transport this to the cyclotomic ideal:

~~~text
padicValNat p
  (Ideal.absNorm (cyclotomicLinearFactorIdeal hzeta g u))
  = 1.
~~~

Also derive:

~~~text
p divides Ideal.absNorm I
not p^2 divides Ideal.absNorm I.
~~~

Reuse:

~~~text
PrimeAdicFactorPacket.prime_dvd_residual
PrimeAdicFactorPacket.residual_exact_one
PrimeAdicFactorPacket.residual_not_prime_sq
cyclotomicLinearFactorIdeal_absNorm_eq_GN
~~~

Do not re-prove the p-adic arithmetic.

## 6. Connect PrimeAdicPowerSplit

For

~~~text
S : PrimeAdicPowerSplit p g u x
~~~

or the canonical

~~~text
primeAdicPowerSplit_of_packet P0
~~~

prove the ideal-norm normal form:

~~~text
Ideal.absNorm I = p * S.b^p.
~~~

Also retain the gap side:

~~~text
g = p^(p-1) * S.a^p.
~~~

If useful, package both as a small ramified cyclotomic-ideal packet.

The target is not a new split theorem. It is only the existing split rewritten
through the new ideal carrier.

## 7. PrimeGe5CounterexamplePack adapter

If dependency placement stays clean, add an adapter from:

~~~text
hpack : PrimeGe5CounterexamplePack p x y z
~~~

to the neutral cyclotomic ideal carrier with:

~~~text
g = hpack.gap
u = y.
~~~

For **all** such counterexample packs, independently of whether p divides the
gap, prove:

~~~text
hpack.gap *
  Ideal.absNorm
    (cyclotomicLinearFactorIdeal hzeta hpack.gap y)
  = x^p.
~~~

This follows from:

~~~text
hpack.xpow_eq_gap_mul_GN
cyclotomicLinearFactorIdeal_absNorm_eq_GN.
~~~

This is the preferred generic FLT-facing theorem.

## 8. Preserve away / ramified distinction

Do not assume p divides the gap for every PrimeGe5CounterexamplePack.

If you add a route type, use the generic shape:

~~~lean
inductive PrimeCyclotomicIdealRoute ...
  | away (hp_not_dvd_gap : not p divides gap) ...
  | ramified (hp_dvd_gap : p divides gap) ...
~~~

but only if it materially improves downstream use.

A simple by_cases theorem family is also acceptable.

### Away branch

Record only facts genuinely available from:

~~~text
not p divides gap.
~~~

Do not manufacture a p-th-power ideal statement.

### Ramified branch

Here it is legitimate to construct:

~~~text
PrimeAdicFactorPacket
PrimeAdicPowerSplit
absNorm I = p * b^p
padicValNat p (absNorm I) = 1.
~~~

If there is no existing generic constructor
PrimeGe5CounterexamplePack + p divides gap -> PrimeAdicFactorPacket,
implement only the thin constructor from existing facts:

~~~text
prime
odd
gap_pos
x_pos
gap_coprime_right
p divides gap
x^p = gap * GN.
~~~

Do not duplicate the full split proof.

## 9. Important distinction: ideal norm normal form is not ideal p-th power

From

~~~text
Ideal.absNorm I = p * b^p
~~~

do not conclude:

~~~text
I = P * J^p
~~~

or

~~~text
I = J^p.
~~~

Those require local prime-ideal multiplicity and coprimality information.

This checkpoint is intentionally global.

GCNB-004L remains the possible later layer for chosen-prime-ideal aggregation.

## 10. No TraceOne work in this checkpoint

Do not import or modify:

~~~text
PrimeTraceOneStrippedIdeal
TraceOnePowerLanding
TraceOneLatticeLanding
~~~

unless only for a non-production API audit.

GCNB-006 will compare the cyclotomic ideal carrier to the TraceOne shadow after
the FLT packet adapter is stable.

## 11. Recommended public theorem surface

Aim for a small set resembling:

~~~text
PrimeAdicFactorPacket.cyclotomicIdeal_absNorm_eq_residual
PrimeAdicFactorPacket.gap_mul_cyclotomicIdeal_absNorm_eq_pow
PrimeAdicFactorPacket.padicValNat_cyclotomicIdeal_absNorm_eq_one
PrimeAdicFactorPacket.prime_dvd_cyclotomicIdeal_absNorm
PrimeAdicFactorPacket.prime_sq_not_dvd_cyclotomicIdeal_absNorm

PrimeAdicPowerSplit.cyclotomicIdeal_absNorm_eq_prime_mul_pow

PrimeGe5CounterexamplePack.gap_mul_cyclotomicIdeal_absNorm_eq_pow
~~~

Names may be adjusted to DkMath style.

Avoid a very large packet if direct theorems remain clearer.

## 12. Tests

Add a focused test module, suggested:

~~~text
DkMathTest/FLT/Prime/PrimeCyclotomicIdeal.lean
~~~

Required checks:

1. a generic PrimeAdicFactorPacket theorem elaborates;
2. ideal absNorm rewrites to residual GTail/GN;
3. gap * ideal absNorm = x^p;
4. p-adic valuation of the ideal absNorm is exactly 1;
5. p divides absNorm but p^2 does not;
6. PrimeAdicPowerSplit rewrites absNorm as p * b^p;
7. p = 7 compatibility with the existing seven ramified packet, if the
   existing compatibility constructor is already available and cheap to reuse;
8. p = 3/5 may be used only as type-level calibration if suitable packets
   exist; do not invent fake FLT counterexamples.

Add #print axioms for every new public theorem.

## 13. Validation

Run at least:

~~~text
lake build DkMath.FLT.Prime.PrimeCyclotomicIdeal
lake build DkMathTest.FLT.Prime.PrimeCyclotomicIdeal
lake build DkMath.FLT.Prime
lake build DkMath.CFBRC
lake build DkMath
git diff --check
~~~

No:

~~~text
sorry
admit
sorryAx
new axiom
unsafe proof shortcut
~~~

## 14. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-003.md
~~~

Classify:

### Outcome A — generic FLT cyclotomic-ideal adapter complete

PrimeAdicFactorPacket and PrimeGe5CounterexamplePack both reach the canonical
cyclotomic ideal, complete x^p identity, and ramified exact residual norm
normal form without p=7 specialization.

### Outcome B — arithmetic packet complete, counterexample-pack adapter partial

The PrimeAdicFactorPacket bridge is complete, but the PrimeGe5 adapter would
require an unwanted dependency or a missing generic constructor. Record the
exact boundary.

### Outcome C — branch distinction blocks a clean adapter

Do not add a p-divides-gap assumption globally. Record the minimal generic
route type or constructor required next.

## 15. Completion gate

GCNB-005 is complete once the generic FLT arithmetic packet can be read in the
new representation as:

~~~text
g * absNorm(I_alpha) = x^p
~~~

and the p-divides-gap branch additionally yields:

~~~text
absNorm(I_alpha) = p * b^p
padicValNat p (absNorm I_alpha) = 1.
~~~

Only after that should GCNB-006 compare this full cyclotomic carrier with the
existing TraceOne shadow.
