# FLT3-Unconditional Completion Note

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Status: completed — Outcome A

## Final public endpoint

Standalone import:

    import DkMath.FLT.Three

Primitive endpoint:

    DkMath.FLT.Three.FLT_d3_unconditional

Full positive-natural endpoint:

    DkMath.FLT.Three.fermatThree_no_positive_solution

The final theorem states:

$$
\forall a,b,c\in\mathbb N_{>0},
\qquad
a^3+b^3\ne c^3.
$$

## Proof spine

The completed independent route is:

    positive solution
      ↓
    gcd normalization
      ↓
    PrimitiveCubicPack
      ↓
    signed 3-adic routing
      ↓
    carrier = 9 A^3
    residual = 3 B^3
    distinguished = 3 A B
      ↓
    Eisenstein ramifier stripping
      ↓
    N(beta) = B^3
    beta.snd = 3 A^3
      ↓
    beta and conj(beta) relatively prime
      ↓
    EuclideanDomain / GCDMonoid extraction
      ↓
    beta = epsilon * gamma^3
      ↓
    six Eisenstein units
      ↓
    modulo-cube sectors 1, tau, tau^2
      ↓
    tau / tau^2 sectors excluded modulo 3
      ↓
    beta = gamma^3
      ↓
    r s (r+s) = A^3
    r^2 + rs + s^2 = B
      ↓
    |r| = R^3
    |s| = S^3
    |r+s| = T^3
      ↓
    R S T = A
      ↓
    sign routing
      ↓
    smaller positive primitive cubic solution
      ↓
    next product = A < a b c
      ↓
    Nat.strong_induction_on (a*b*c)
      ↓
    False

## Main arithmetic transition

After exact cube extraction:

$$
\beta=\gamma^3,
\qquad
\gamma=r+s\tau.
$$

The trace-one cube coordinate gives:

$$
(\gamma^3)_{\rm snd}=3rs(r+s).
$$

Comparing with the stripped second coordinate:

$$
\beta_{\rm snd}=3A^3
$$

yields:

$$
rs(r+s)=A^3.
$$

Together with:

$$
r^2+rs+s^2=B,
\qquad
\gcd(A,B)=1,
$$

the three absolute factors are pairwise coprime cubes.

## Strict descent invariant

The reconstructed positive primitive solution has coordinates given by a permutation of R,S,T and satisfies:

$$
x^3+y^3=z^3,
$$

$$
\gcd(x,y)=1,
$$

$$
xyz=RST=A.
$$

Origin-preserving routing gives:

$$
A<abc.
$$

Hence:

$$
xyz<abc.
$$

This strict natural-number measure is the only recursive axis used by the closure theorem.

## Independence boundary

The production Three tower does not use as proof steps:

- DkMath.FLT.Main.FLT_d3_by_padicValNat
- hS0_not_sq
- NoSqOnS0
- DkMath.FLT.GEisensteinBridge provisional descent
- DkMath.FLT.Five.* production modules
- DkMath.FLT.Seven.* production modules
- a completed Mathlib FLT3 theorem

The standalone public aggregator is:

    DkMath/FLT/Three.lean

and imports only:

    DkMath.FLT.Three.PositiveCubicNormalization

The legacy top-level DkMath.FLT aggregator remains unchanged and still imports legacy Main.

## Axiom audit

The final endpoint reports only:

    propext
    Classical.choice
    Quot.sound

No sorryAx or project-specific axiom is introduced by the completed Three tower.

## Build evidence

Final focused builds reported green:

    lake build DkMath.FLT.Three.PositiveCubicNormalization
    Build completed successfully (8723 jobs).

    lake build DkMath.FLT.Three
    Build completed successfully (8724 jobs).

## Scope boundary

This project completes a new independent DkMath FLT3 endpoint.

It does not:

- delete the legacy conditional FLT3 theorem;
- refactor DkMath.Basic's broad import Mathlib;
- remove legacy Main from the top-level DkMath.FLT aggregator;
- claim repository-wide cleanup of historical FLT3 routes.

Those are maintenance tasks separate from the mathematical completion recorded here.
