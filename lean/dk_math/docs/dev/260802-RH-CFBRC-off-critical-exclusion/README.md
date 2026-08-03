# 260802 RH–CFBRC Off-Critical Exclusion

- Date: 2026-08-02 / Update: 2026/08/04  4:44
- Authors: D. and Wise Wolf
- Base branch: `develop`
- Work branch: `wip/RH-CFBRC-off-critical-exclusion-260802-v2`
- Status: active

## Purpose

This project separates the Riemann-hypothesis program into two independent layers.

1. Prove, inside the algebraic CFBRC world and without importing zeta-zero facts, that the selected CFBRC closure polynomial cannot vanish away from the centered line.
2. Construct a later zero-preserving bridge from a nontrivial zeta zero into that CFBRC closure polynomial.

The proof order is deliberate:

```text
CFBRC off-critical exclusion
  -> abstract zero-preserving bridge interface
  -> completed-zeta / Hardy / HOPC realization of the bridge
  -> RH conclusion
  -> optional prime-mass interpretation of the zero state
```

The prime-distribution interpretation is not an assumption of the main exclusion theorem. It belongs to a later explanatory layer.

## Centered coordinate

Use

$$
X=\sigma-\frac12.
$$

Thus `X = 0` is the critical line and `X ≠ 0` is an off-critical candidate.

The standard real-input CFBRC polynomial is

$$
C_d(X,\Theta)
=(X+i\Theta)^d-(i\Theta)^d.
$$

The first implemented kernel uses `d = 2`:

$$
C_2(X,\Theta)=X^2+2iX\Theta.
$$

Hence

$$
C_2(X,\Theta)=0
\quad\Longleftrightarrow\quad
X=0.
$$

This is a zeta-independent algebraic exclusion theorem.

## Bridge target

The final analytic bridge need not prove a complete function isomorphism. For RH it is sufficient to prove a zero-preserving implication of the form

$$
\operatorname{NontrivialZero}(s)
\longrightarrow
C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right)=0.
$$

Once combined with the off-critical exclusion theorem, the conclusion is immediate:

$$
s.\operatorname{re}=\frac12.
$$

The bridge must satisfy the following audit rules.

- It must be defined off the critical line as well as on it.
- It must not assume `s.re = 1 / 2`.
- Its phase or normalization must not branch on the zero predicate.
- Any multiplier used in a factorization must be proved nonzero independently.
- The algebraic exclusion module must not import zeta-zero theorems.

## Current implementation slice

The first slice introduces:

- `centeredSigma`
- `offCriticalCFBRC`
- `cfbrcR_two_eq_zero_iff_x_eq_zero`
- `offCriticalCFBRC_two_eq_zero_iff_re_eq_half`
- an abstract `ZeroToCFBRCTwoBridge`
- the generic conclusion `re_eq_half_of_zeroToCFBRCTwoBridge`

This isolates the entire future analytic difficulty in one field, `map_zero`.

## Next targets

1. Generalize the exclusion theorem from `d = 2` to every positive `d`.
2. Add the mirror-CFBRC threat model and classify its nontrivial cyclotomic branches.
3. Define the completed-zeta zero predicate used by the bridge.
4. Construct a finite vector-closure bridge.
5. Lift the finite closure through the existing HOPC finite-to-infinite API.
6. Prove the nonzero multiplier / normalization obligations.
7. Instantiate the abstract bridge and derive the RH statement.
8. Only after the location theorem, add the natural-number and prime-factor mass interpretation.

See [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md) for the detailed event sequence.
