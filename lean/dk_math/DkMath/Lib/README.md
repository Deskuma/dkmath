# DkMath.Lib

## 1. Purpose

`DkMath.Lib.*` is the reusable intermediate layer extracted from DkMath research code.

Its purpose is to separate **neutral mathematical kernels** from theorem-owner-specific experiments such as FLT, ABC, RH, Goldbach, or one fixed GN degree.

Recommended public development import for the current aggregator-exposed subset:

```lean
import DkMath.Lib
```

`DkMath.Lib.lean` intentionally exposes a promoted subset without importing the whole experimental DkMath workspace. Some neutral modules in this directory are currently direct-import APIs and are not yet listed by the aggregator.

The intended flow is:

```text
research owner
  -> repeated useful structure
  -> remove owner-specific assumptions / names
  -> DkMath.Lib.*
  -> reuse from later owners
```


## 1.1 Aggregator coverage in this snapshot

`DkMath.Lib.lean` currently imports the following promoted families directly:

```text
Basic
TwoChannel
NumberTheory.PadicValNat
NumberTheory.TraceOneLatticeLanding
NumberTheory.TraceOnePowerLanding
NumberTheory.EisensteinCoordinates
NumberTheory.EisensteinLatticeLanding
NumberTheory.SquarefreePowerFactor
Cosmic.GTail
Cosmic.GTailCyclotomic
Cosmic.GTailPascal
Cosmic.GTailBoundary
Cosmic.GTailNat
Cosmic.GTailCongruence
Cosmic.GTailPadic
```

The following neutral modules exist under `DkMath.Lib.NumberTheory` and are used by current research through direct imports, but are not yet re-exported by `DkMath.Lib.lean` in this snapshot:

```text
PowerFactor
IdealPowerFactor
PrincipalIdealPower
UnitPowerSector
```

This is an API/export-state distinction, not a statement that the latter modules are less reusable.

## 2. Cosmic family: `GTail`

The main promoted cosmic/binomial kernel is `GTail`.

For a commutative semiring, `GTail d r x u` is defined so that

$$
\begin{aligned}
(x+u)^d &\;=\; \sum_{j<r}\binom dj x^j u^{d-j}\\
&\qquad +x^r\operatorname{GTail}(d,r,x,u).
\end{aligned}
$$

The standard gap-normalized `GN` layer is the $r=1$ specialization:

$$
GN_d(x,u)=\operatorname{GTail}(d,1,x,u).
$$

This is the main abstraction shift behind the `[GNZC]` promotion work: new neutral code should use the `GTail` theorem family when the statement is not intrinsically tied to a legacy `GN` surface.

### `DkMath.Lib.Cosmic.GTail`

Core decomposition and recursion.

Representative APIs:

```text
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
add_pow_eq_mul_GTail_one_add_gap
GTail_rec
GN_tail_rec
GN_tail_decomposition
GTail_eval_zero
GN_zero_eval
```

### `GTailBoundary`

Exact gcd / first-boundary structure.

Representative APIs:

```text
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
gcd_GN_eq_gcd_of_one_le
gcd_GN_prime_eq_one_of_not_dvd
gcd_GN_prime_eq_prime_of_dvd
```

### `GTailCongruence`

Natural-number congruence propagation and head-collapse results.

Representative APIs include:

```text
GTail_congr_of_modEq
GTail_modEq_eval_zero_of_dvd_x
prime_dvd_GN_iff_dvd_gap
GN_mod_p2_head
GN_mod_p3_head
```

### `GTailCyclotomic`

Neutral algebraic bridge between the $r=1$ tail and cyclotomic shells.

Representative APIs:

```text
prod_cyclotomicEval_eq_geomSum
add_pow_eq_mul_GTailCyclotomicShell_add_gap
GTail_one_eq_cyclotomicHomEval_of_prime
```

### `GTailNat`

Natural-number divisibility consequences.

Representative APIs:

```text
pow_dvd_higher_tail
GTail_not_dvd_of_head_unit_of_prime_dvd_x
GN_not_dvd_of_head_unit_of_prime_dvd_x
```

### `GTailPadic`

`padicValNat` consequences of the tail decomposition.

Representative APIs:

```text
padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x
padicValNat_tail_exact_of_head_unit
padicValNat_GN_exact_of_head_unit
not_prime_sq_dvd_GN_of_dvd_gap
padicValNat_GN_prime_eq_one_of_dvd_gap
```

### `GTailPascal`

Finite-depth Pascal filtration.

Main API:

```text
GTail_split_at
```

## 3. Number-theory family

### `PadicValNat`

Reusable natural-number valuation utilities, independent of ABC/FLT/RH owners.

Includes zero criteria, bounds, powers, carrier-shape lemmas, and prime-power divisibility tools.

### `PowerFactor`

Neutral coprime power-factor splitting.

Representative APIs:

```text
associated_prime_power_of_coprime_mul_eq_pow
eq_pow_of_associated_pow_of_unit_pow_surjective
power_factor_split
```

### `IdealPowerFactor`

Neutral ideal-power / class-group kernel.

Key definition:

```lean
def classGroupPTorsionFreeAt (R : Type*) (p : ℕ) : Prop := ...
```

Representative APIs:

```text
ideal_isPrincipal_of_classGroupPTorsionFreeAt
ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
exists_eq_pow_of_isCoprime_mul_eq_pow
```

This module deliberately stops at the ideal/class-group layer; unit absorption is separated.

### `PrincipalIdealPower`

Bridges principal-ideal equality to associated / unit-times-power element statements.

Representative APIs:

```text
associated_of_span_singleton_eq_span_singleton
exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
```

### `UnitPowerSector`

Neutral interface for unit groups modulo $p$-th powers.

The abstraction provides representatives and completeness without asserting global surjectivity of the unit $p$-th-power map.

### `TraceOneLatticeLanding`

Integral-coordinate divisibility criterion for the existing `TraceOneInt s` carrier.

The key equivalence converts element divisibility into divisibility of the coordinates of multiplication by the conjugate, under the explicit nonzero-norm hypothesis.

Representative API:

```text
traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
```

### `TraceOnePowerLanding`

Current power-image receiver layer for `TraceOneInt s`. The present production theorem explicitly records square coordinates and square-core landing; it does not provide a general arbitrary-power root provider.

Representative APIs:

```text
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_sq_core_landing_iff
```

### `EisensteinCoordinates`

Neutral standard Eisenstein coordinates represented inside `TraceOneInt (-1)`.

```lean
def eisensteinCoord (m n : ℤ) : TraceOneInt (-1) := ...
```

The module reuses the existing TraceOne ring/norm instead of defining a second arithmetic carrier.

### `EisensteinLatticeLanding`

Integral-coordinate divisibility criterion specialized to the standard Eisenstein model.

Representative API:

```text
eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
```

### `SquarefreePowerFactor`

Neutral UFD-side square-factor extraction:

```text
exists_squarefree_mul_sq
```

This was extracted from ABC Eisenstein provider work but is not ABC-specific.

## 4. Other promoted kernel

### `TwoChannel`

A neutral real-linear sum/difference coordinate kernel

$$
(u,v)\longmapsto(u+v,u-v),
$$

with domain-specific interpretation left to owner modules.

## 5. Promotion policy

A theorem is a good `DkMath.Lib.*` candidate when:

- its statement is not inherently tied to one research conjecture or checkpoint;
- owner-specific assumptions can be removed or made explicit parameters;
- its dependencies can point downward into Mathlib / neutral DkMath kernels;
- a later owner can reasonably import it without inheriting unrelated research machinery.

Avoid promoting a theorem merely to rename it. The promoted statement should expose a genuinely reusable mathematical boundary.

## 6. GN5 and the origin of the promoted layer

GN5 / FLT5 work was a major source of reusable structures: binomial-tail identities, divisibility, p-adic splitting, power-factor extraction, algebraic coordinate landing, and unit-sector organization.

The current architecture treats the fixed-degree GN5 project as an important historical success and test case, while `DkMath.Lib.*` is the long-lived home for the abstractions that survived generalization.

## 7. Current status

As of the 2026-09-16 documentation snapshot, `DkMath.Lib` is an established promoted layer but is still evolving. Some reusable mathematics remains in older owner namespaces and may be migrated in later refactors.

Snapshot provenance:

```text
1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7  __snapshot-dk_math-lean-code-260916-1826.tar.gz
```
