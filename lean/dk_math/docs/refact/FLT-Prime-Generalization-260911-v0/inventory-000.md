# FLT7 → prime-exponent generalization inventory 000

Branch: `refact/FLT-Prime-Generalization-260911-v0`
Base: `develop` after PR #89 (`8ffaa2da7671d197c7663b921d3353419155734b`)

## Purpose

Audit the current `DkMath.FLT.Seven` implementation from the new GTail-centric point of view and classify which theorems are genuinely exponent-seven mathematics and which are instances of a reusable prime-exponent kernel.

This phase does **not** attempt to prove FLT for general prime exponent.  It extracts the arithmetic layer that can be stated independently of the `p = 7` real-cubic / degree-six / ramified number-field machinery.

The central normalization is

```text
GN p x u = GTail p 1 x u.
```

For prime `p`, this is the prime cyclotomic shell already exposed by `DkMath.Lib.Cosmic.GTailCyclotomic`.

## Classification marks

- `CORE-ALREADY`: the general theorem already exists in `DkMath.Lib.*`; the FLT7 theorem should ultimately become a specialization/corollary.
- `PGEN-HIGH`: generalization looks structurally direct; Lean should be asked to certify the minimal assumptions.
- `PGEN-TEST`: plausible generalization, but assumptions or proof route are not yet fixed.
- `PGEN-BOUNDARY`: the generalization is expected to fail at a small boundary value; record the exact counter-boundary.
- `P7-STRUCTURAL`: depends on a representation intrinsically specialized to seven, such as discriminant `-7`, degree six, or the real cubic subfield.
- `P7-TERMINAL`: downstream terminal/descent arithmetic whose current implementation is seven-specific even if some sublemmas may later split off.

## Existing generic core after GTail refactor

### Exact boundary gcd

`DkMath.Lib.Cosmic.GTailBoundary` already proves

```lean
gcd_GTail_eq_gcd_boundary
gcd_GTail_eq_gcd_choose
```

and therefore, for `Nat.Coprime g u` and `1 ≤ p`,

```text
gcd g (GTail p 1 g u) = gcd g p.
```

This subsumes the hand-expanded Pascal calculation currently used by several FLT7 gcd lemmas.

### Prime-row mod-p² congruence

`DkMath.Lib.Cosmic.GTailCongruence` already proves the general interior theorem

```lean
GTail_modEq_head_mod_sq_of_prime_dvd_x
```

under

```text
Prime p, 1 ≤ r, r + 1 < p, p ∣ x.
```

For `r = 1`, the mathematical boundary is therefore `2 < p`.

The current convenience theorem

```lean
GN_modEq_head_mod_sq_of_prime_dvd_x
```

uses the stronger assumption `5 ≤ p`.  This is an API-strengthening candidate: the underlying theorem already suggests that odd prime `p ≥ 3` is the natural range.

### Generic valuation utilities

`DkMath.Lib.NumberTheory.PadicValNat` now owns the reusable valuation lemmas independently of ABC/FLT/RH, including

```lean
Vp_ge_one_iff
padicValNat_le_iff_dvd
padicValNat_pow
padicValNat_pow'
```

so FLT prime-generalization probes should import this lower layer directly.

## Initial FLT7 candidate map

| Current theorem / structure | Initial mark | Proposed general target | Notes |
| --- | --- | --- | --- |
| `gcd_gap_GN_seven_dvd_seven` | `CORE-ALREADY` | `gcd g (GTail p 1 g u) = gcd g p` under `Coprime g u` | Replace explicit degree-7 Pascal expansion with `gcd_GTail_eq_gcd_choose`. |
| `gcd_gap_GN_seven_eq_one_of_not_seven_dvd` | `PGEN-HIGH` | prime `p`, `¬ p ∣ g` ⇒ gcd is `1` | Corollary of generic boundary gcd. |
| `gcd_gap_GN_seven_eq_seven_of_seven_dvd` | `PGEN-HIGH` | prime `p`, `p ∣ g` ⇒ gcd is `p` | Corollary of generic boundary gcd. |
| `seven_dvd_GN_seven_sub_iff` | `PGEN-TEST` | `Prime p` ⇒ `p ∣ GTail p 1 g u ↔ p ∣ g` | Current seven theorem has no coprimality hypothesis. Reverse direction needs a prime-row mod-`p` argument, not merely boundary gcd. Test `p = 2` separately; the divisibility iff itself is expected to survive. |
| `not_seven_dvd_right_of_coprime_of_seven_dvd_sub` | `PGEN-HIGH` | generic divisor `q > 1`, coprime endpoints | Not intrinsically prime or seven-specific. |
| `padicValNat_GN_seven_sub_eq_if` | `PGEN-HIGH` + `PGEN-BOUNDARY` | odd prime `p`: valuation of `GTail p 1 g u` is `1` on `p ∣ g`, `0` off it, under primitive endpoint hypotheses | `p = 2` is a genuine boundary: e.g. `GTail 2 1 2 1 = 4`, so the on-channel valuation is `2`, not `1`. |
| `not_fortyNine_dvd_GN_seven_sub` | `PGEN-HIGH` | odd prime `p`: `¬ p^2 ∣ GTail p 1 g u` on primitive `p ∣ g` channel | Expected corollary of exact valuation one / mod-`p²` head congruence. |
| `seventh_power_factor_split` | `PGEN-HIGH` | arbitrary exponent `d`: coprime `a*b = x^d` splits each factor as a `d`-th power | Current proof already delegates to generic Mathlib `exists_eq_pow_of_mul_eq_pow`. |
| `padicValNat_carrier_shape_of_mul_eq_seventh` | `PGEN-HIGH` | prime `p`: if `carrier*residual = distinguished^p` and `v_p(residual)=1`, then `v_p(carrier) = (p-1) + p*m` | Algebraic valuation conservation; no degree-7 field structure is used in the current proof. |
| `padicValNat_gap_shape_of_counterexample` | `PGEN-HIGH` after generic packet | FLT prime packet specialization of previous theorem | Depends only on feeding the generic carrier theorem with FLT factorization and residual valuation one. |
| `seven_pow_six_dvd_gap_of_counterexample` | `PGEN-HIGH` after previous | `p^(p-1) ∣ gap` | Immediate expected consequence of the valuation shape. |
| `SevenAdicPowerSplit` | `PGEN-TEST` phase 2 | `PrimeAdicPowerSplit` with `gap = p^(p-1)*a^p`, `residual = p*b^p`, `distinguished = p*a*b` | Do not generalize this first. Prove the lower arithmetic lemmas independently, then rebuild this packet. |
| `coprime_y_z_of_counterexamplePack` | `PGEN-HIGH` phase 2 | positive exponent `d` counterexample packet | The proof uses a prime divisor of a gcd and `dvd_of_dvd_pow`; exponent seven appears parametrically. |
| `coprime_gap_y_of_counterexamplePack` | `PGEN-HIGH` phase 2 | generic positive exponent packet | Ordinary coprime/subtraction routing. |
| `body7_eq_seventh_power_of_counterexample` | `PGEN-HIGH` phase 2 | generic exponent factorization via `GTail d 1` | Direct Cosmic/GTail identity. |
| `sevenAxis_*`, `sevenAxisDepth_*` | `P7-STRUCTURAL` | no direct `p` replacement in phase 0 | Uses `TraceOneInt (-2)`, discriminant `-7`, `sevenAxis`, and norm `7`. Generalization requires a different carrier family, not textual replacement. |
| `cyclotomicSevenToTraceOne*` | `P7-STRUCTURAL` | later cyclotomic carrier abstraction | Current coordinate model is specialized. Keep separate from generic GTail arithmetic. |
| `SevenRealCubic*` | `P7-STRUCTURAL` | later `(p-1)/2` real cyclotomic layer | Cubic degree is exactly `(7-1)/2 = 3`. |
| `SevenRamifiedFusionCyclotomicDegreeSix*` | `P7-STRUCTURAL` | later `p-1` cyclotomic-degree layer | Degree six is exactly `7-1`. |
| `SevenBaseTerminal*`, `SevenRamifiedFusion*` terminal closures | `P7-TERMINAL` | reconsider only after generic front-half extraction | Do not assume generality from naming or local algebra alone. |

## Prime-row target hierarchy

The initial reusable kernel should be tested in the following dependency order:

```text
PGEN-001  exact GTail/GN boundary gcd at r=1
     ↓
PGEN-002  prime divisibility address: p ∣ GN_p ↔ p ∣ gap
     ↓
PGEN-003  odd-prime exact residual valuation: v_p(GN_p) ∈ {0,1}
     ↓
PGEN-004  valuation conservation in p-th-power product
     ↓
PGEN-005  generic coprime p-th-power factor split
     ↓
PGEN-006  prime-adic normal-form packet
```

The purpose of this ordering is diagnostic.  A Lean failure should identify the first place where the current seven proof uses information not supplied by the generic GTail / prime-row kernel.

## Expected mathematical boundary

For primitive `Nat.Coprime g u`, prime `p`, and `p ∣ g`, the desired odd-prime mechanism is

```text
GTail p 1 g u ≡ p * u^(p-1)  [MOD p^2].
```

If `p ∤ u`, the right side has exactly one factor of `p`, hence the GTail/GN residual should have exact valuation one.  The current general interior congruence supports this already for `2 < p`.

At `p = 2`, this exact-one statement fails:

```text
GTail 2 1 2 1 = 4,
padicValNat 2 4 = 2.
```

Thus `p = 2` should be recorded as a true theorem boundary rather than patched away by an arbitrary `5 ≤ p` hypothesis.

## Phase-0 non-goals

Do not:

- rewrite `DkMath.FLT.Seven` consumers yet;
- rename or deprecate legacy `GN` wrappers in this branch;
- generalize `TraceOneInt (-2)` by replacing `7` with a parameter;
- claim that the real-cubic / degree-six / ramified terminal layers generalize;
- introduce `sorry`, `axiom`, or unverified theorem placeholders.

The first deliverable is a focused Lean probe and a report stating exactly which candidate statements compile, which assumptions were necessary, and where the first genuine seven-specific obstruction appears.
