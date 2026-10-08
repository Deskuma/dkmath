# GTail Selective-Gap / FLT7 Bridge

Branch: **feature/GTail-SelectiveGap-FLT7-261009-v0**  
Base: **develop** (create a dedicated implementation branch; do not commit to develop)  
Status: **planning / Codex instruction 001 prepared — no theorem implementation claimed**

## Research purpose

Build a reusable GN/GTail observation layer inside `DkMath.Lib.Cosmic.*`.

The objective is not to restate the Cosmic Formula with different notation. Regard an existing theorem or power expansion as a complete **Big**, select a mathematically justified **Gap**, and expose the resulting **Body**, its **Core / Beam** decomposition, exact divisibility, valuation, and the invariants preserved while the Gap changes.

```text
Big = Gap + Body
Body = Core + Beam
Core can be a smaller Big' for another structurally justified decomposition
```

A deliberate Gap selection ("reasoned subtraction") is a source of new observable constraints. Equalities alone must not be mistaken for new arithmetic obstructions.

## Existing canonical basis

Implementation is under `lean/dk_math`. Inspect and reuse:

- `DkMath.Lib.Cosmic.GTail`: `GTail`, `add_pow_eq_prefix_add_xpow_mul_GTail`, `higher_tail_eq_pow_mul_GTail`, `GTail_rec`.
- `DkMath.Lib.Cosmic.GTailPascal`: `GTail_split_at`.
- `DkMath.Lib.Cosmic.GTailBoundary`: `gcd_GTail_eq_gcd_choose`.
- `DkMath.Lib.Cosmic.GTailNat`, `GTailCongruence`, `GTailPadic`, `GTailCyclotomic`.
- `DkMath.Lib.lean`: promoted public imports.

**Indexing warning:** the existing `GTail d r x u` removes the **first r layers counted by powers of x** (j=0,...,r-1) and returns an `x^r`-divisible Body. Thus the cubic example

```text
(x+y)^3 - (y^3+3*x*y^2) = x^2*(x+3*y)
```

is `GTail 3 2 x y`. Keep this indexing; do not silently reverse it.

## Mathematical construction

For `t_k = choose(d,k) * x^k * y^(d-k)`, define a selection `S` of indices within `0..d`:

```text
Big       = sum of all t_k = (x+y)^d
Body(S)   = sum of selected t_k
Gap(S)    = sum of unselected t_k
Big       = Gap(S) + Body(S)
```

Prove the balanced decomposition over a commutative semiring first (no subtraction needed). Subtraction-shaped identities belong to a commutative-ring corollary.

Recover the ordinary prefix/suffix GTail from interval selections rather than redefining the existing canonical `GTail`. For nonempty S, the smallest and largest selected indices control mandatory monomial factors; the gcd of the selected Pascal coefficients controls the integer polynomial content. Removing both endpoints for prime degree exposes an additional degree-prime coefficient factor and an `xy` factor. These are separate mechanisms.

When changing selection `S -> T`, track exactly which terms move and prove the equality, not preservation of divisibility without its hypotheses.

## Degree-seven calibration

Expected exact identities to verify in Lean, without any FLT assumption:

```text
GTail 7 6 x y = x + 7*y
GTail 7 5 x y = x^2 + 7*x*y + 21*y^2
(x+y)^7 - x^7 - y^7
  = 7*x*y*(x+y)*(x^2+x*y+y^2)^2
```

The degree-seven endpoint-removal identity is a polynomial identity; it does **not** imply Fermat's Last Theorem on its own.

## Proposed boundary to FLT7 (later milestone)

Assume `a^7 + b^7 = c^7` and independently `c + g = a + b` in naturals (or use a typed integer coordinate with explicit positivity). Derive, without importing an existing FLT7 impossibility endpoint:

```text
g * GTail 7 1 g c
  = 7*a*b*(a+b)*(a^2+a*b+b^2)^2
```

Test what *new* arithmetic constraints follow (gcd, prime support, p-adic valuations, normalization/unit gauge). A restatement of an identity is **not** an FLT7 closure.

## Scope discipline

1. `DkMath.Lib.Cosmic.*` contains neutral, reusable kernels and degree-seven algebraic calibration, not FLT-specific assumptions.
2. The FLT7 research bridge stays under `DkMath.FLT.Seven.*` and must import the library layer, never the reverse.
3. Lean proofs are the source of truth. No `sorry`, `admit`, added `axiom`, `unsafe`, proof by vacuous reliance on a known FLT7 theorem, or unjustified mathematics.
4. Record proof dependencies, executable focused builds, and `#print axioms` audits.
5. Prefer isolated tests and low-memory builds; only widen to façade/whole-library builds after focused checks.
6. Do not claim the GTail approach closes FLT7 until an independent, non-circular terminal contradiction is kernel checked.

## Documents

- [ROADMAP.md](ROADMAP.md): incremental implementation plan and acceptance gates.
- [instruction-001.md](instruction-001.md): first Codex implementation request.

The broad external 13-million-line proof corpus is explicitly **deferred** until this local GTail instrument has been implemented and measured.
