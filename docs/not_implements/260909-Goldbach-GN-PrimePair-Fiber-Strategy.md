# Goldbach via GN Prime-Pair Fiber — Strategy Note

Date: 2026-09-09  
Updated: 2026-09-12  
Status: original strategy largely implemented; static fixed-center normalization audited; universal short-fiber escape unresolved  
Target branch: `develop`  
Current frontier: a genuinely new cross-seat / cross-fiber invariant; next research branch not yet fixed  
cid: `6aa15236-f2b0-83ee-bfbf-a1b3c5615e5d`

Implementation follow-ups:

- 2026-09-10: [`NumberTheory-Goldbach-GNFiber-260910-v0`](../../lean/dk_math/docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/README.md)
- 2026-09-12: [`NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0`](../../lean/dk_math/docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/report-005.md)
- GTail core refactor: [`Lib-GTail-Core-260908-v0`](../../lean/dk_math/docs/refact/Lib-GTail-Core-260908-v0/analysis-001.md)

The original strategy below is retained as the research proposal, but the current frontier has moved substantially. The finite GN-fiber reduction, proper small-prime obstruction model, CRT / PrimeWorld layer, exact survivor criterion, overlap accounting, Pascal residual layer, and primitive/parity normalization have all been formalized or audited. Strong Goldbach remains unproved.

## 0. Current Status — 2026-09-12

### 0.1 What is now implemented

The original plan has been realized through almost all of its finite/static layers.

Implemented and kernel-checked components include:

1. `GoldbachPairAt`, `GoldbachGNFiberAt`, and exact equivalence with the usual fixed-center prime-pair statement.
2. The degree-two identity

$$
n^2=(n-u)(n+u)+u^2.
$$

3. Proper left/right obstruction predicates with endpoint exceptions.
4. The complete small-prime cutoff up to the square-root boundary.
5. Exact equivalence between survival from all proper small-prime obstructions and primality of both endpoints.
6. PrimeWorld residue coordinates, CRT periodicity, and exact full-period survivor cardinality.
7. Exact finite covered/survivor capacity accounting and
   `strongGoldbach_iff_capacityEscape`.
8. PCK / old-fresh bridge results, with explicit limitations showing that pointwise primitive escape does not force a simultaneous prime pair.
9. Exact overlap conservation and pair-overlap accounting.
10. Pascal residual decomposition of pair overlap.
11. Canonical GTail core promotion, including tail filtration, exact boundary gcd, prime-row congruence, p-adic support, and cyclotomic bridge.
12. Degree-two primitive/parity normalization and left/right support separation, audited by GPT-6 Astra.

The key static capacity statement is therefore no longer merely a proposed theorem shape. It is an exact reformulation of Goldbach itself.

### 0.2 Exact current bottleneck

The missing step is still a universal **short fixed-center fiber escape**:

$$
\boxed{
\forall n\ge2,\;
\exists u<n,\;
\operatorname{Prime}(n-u)
\land
\operatorname{Prime}(n+u)
}
$$

or equivalently a proof that not every admissible seat is covered by proper small-prime obstructions.

Full-period CRT existence is already available. The unresolved problem is **location inside the short fiber**, not existence somewhere in the periodic world.

### 0.3 Astra quadratic-primitive audit: Outcome B

The 2026-09-12 research pass tested whether the newly promoted GTail boundary theorem creates a genuinely stronger degree-two Goldbach route.

The following normalization facts were proved in scratch Lean:

- every positive non-diagonal Goldbach prime pair forces `Nat.Coprime n u`;
- primitive coordinates plus opposite parity give coprime reflected endpoints;
- center divisors and `2` disappear from the retained primitive-parity obstruction world;
- proper left/right supports become disjoint;
- pair overlap splits exactly into `LL + LR + RR`;
- the `LR` term admits the expected oriented CRT/product-wave description;
- parity improves the same-orientation spacing to `2*p*q` for odd coprime moduli.

However, the exact survivor comparison shows that normalization creates no new positive survivors:

$$
S' = \{u\in S : 0<u\},
$$

with the omitted zero seat present exactly when the center itself is prime.

After restoring that diagonal, the normalized capacity criterion is exactly equivalent to both `GoldbachCapacityEscape` and `StrongGoldbach`.

Hence the audit result is:

> **Outcome B — structural normalization only.**
>
> The primitive/parity and left/right product-wave structure is correct and useful as a canonical normal form, but it is not an independent escape provider.

Important branch-cutting counterexamples were also fixed:

- strict incidence still fails after normalization (`n = 19`);
- higher overlap remains (`n = 31, u = 4`);
- the `2*p*q` spacing bound is sharp (`n = 47, p = 3, q = 5`);
- candidate cardinality cannot replace geometric interval width, even for proper LR occupancy (`n = 162`).

### 0.4 Updated research direction

Further normalization of a **single fixed fiber** is now unlikely, by itself, to create strict information gain. In particular, merely refining

- primitive candidate density,
- CRT moduli,
- residue cardinalities,
- local support counts,
- or same-orientation spacing

risks reproducing an already equivalent capacity ledger.

The next promising direction should introduce information not present in one static fiber. Candidate forms include:

- relations between multiple seats in the same fiber that are not reducible to independent CRT coordinates;
- transport between neighboring centers `n → n+1`;
- scale/fiber morphisms linking survivor or overlap structures across different square fibers;
- a dynamic conservation law for prime-wave mass / overlap under center motion;
- a genuinely new invariant carried by GTail / PCK / Pascal structure across fibers rather than at one seat.

In DkMath terminology, the frontier has shifted from **static normalization** toward **dynamic harmonic arithmetic**.

---

## 1. Purpose

This note preserves the original strategy before implementation began.

The immediate observation was that DkMath already contained many of the structural tools needed to reformulate the strong Goldbach conjecture inside the GN / Cosmic Formula framework:

- canonical GN / GTail decomposition;
- prime-row Pascal divisibility;
- composite-degree factorization of GN;
- finite positive representation bounds;
- prime-target residue constraints;
- finite prime-world residue spaces;
- Primitive Conservation Kernel machinery.

The original remaining task was to choose a proof architecture that forces a prime-pair point to survive on every square fiber. Most finite/static infrastructure proposed below has since been implemented; the universal forcing theorem has not.

## 2. Important correction: “all primes are representable by GN” is too weak

For the canonical degree-two kernel,

```text
GN 2 x u = x + 2u.
```

Hence every odd number \(P\) has the trivial positive representation

$$
P = GN_2\!\left(1,\frac{P-1}{2}\right).
$$

Therefore the statement

$$
\forall P>2,\quad \operatorname{Prime}(P)
\to
\exists d,x,u,\quad GN_d(x,u)=P
$$

is not strong enough to imply Goldbach. In fact degree \(2\) already represents every odd target, not only primes.

The Goldbach problem must keep the **fiber center fixed**.

## 3. Goldbach as a degree-two GN fiber theorem

For an even target \(2n\), write

$$
p=n-u,\qquad q=n+u.
$$

Set

$$
x:=n-u.
$$

Then

$$
x+u=n
$$

and

$$
GN_2(x,u)=x+2u=n+u.
$$

Therefore the strong Goldbach statement at \(2n\) is equivalent to the existence of a degree-two GN point satisfying

$$
x+u=n,
\qquad
\operatorname{Prime}(x),
\qquad
\operatorname{Prime}(GN_2(x,u)).
$$

This equivalence is now implemented by the production Goldbach modules.

## 4. Body / Big / Gap interpretation

The degree-two Cosmic Formula gives

$$
(x+u)^2=x(x+2u)+u^2.
$$

With \(n=x+u\),

$$
n^2=(n-u)(n+u)+u^2.
$$

Hence

$$
\mathrm{Big}=n^2,
\qquad
\mathrm{Gap}=u^2,
\qquad
\mathrm{Body}=n^2-u^2=(n-u)(n+u).
$$

Goldbach becomes:

> For every \(n\ge2\), the square fiber
>
> $$
> \mathrm{Body}_n(u)=n^2-u^2
> $$
>
> contains at least one point whose two canonical factors are both prime.

This remains the preferred DkMath reading.

## 5. DkMath weapons and their present role

### 5.1 Pascal / GTail

Prime-row Pascal divisibility and the canonical GTail filtration are now lower-level reusable infrastructure. The Goldbach overlap ledger also exposes a Pascal hierarchy, but no theorem identifies that hierarchy with GTail as an escape mechanism.

### 5.2 Composite-degree GN factorization

`GN_mul_degree` gives

$$
GN_{ab}(x,u)
=
GN_a(x,u)\,
GN_b\!\left(x\,GN_a(x,u),u^a\right).
$$

In the positive nondegenerate region,

$$
GN_d(x,u)\text{ prime}
\Longrightarrow
d\text{ prime}.
$$

This remains important for higher-degree classification, but Goldbach itself is intrinsically the degree-two fiber.

### 5.3 Prime-target constraints and signatures

For positive prime-target representations, DkMath constrains the possible degree by conditions such as

$$
d\text{ prime},
\qquad
d\mid P-1,
\qquad
2^d-1\le P.
$$

These signatures are finite and thin, but current formalization does not transport primality from one reflected endpoint to the other. They should therefore be treated as classifiers, not as a solved Goldbach bridge.

### 5.4 Primitive / PrimeWorld / PCK

The Primitive and PrimeWorld infrastructure now supports the implemented Goldbach residue, cardinality, and conservation layers. PCK provides useful old/fresh decomposition facts, but current bridges do not force simultaneous escape of both reflected endpoints.

### 5.5 Exact GTail boundary gcd

The GTail refactor added the general theorem

$$
\gcd(x,GTail(d,r,x,u))
=
\gcd\!\left(x,\binom dr u^{d-r}\right),
$$

and, under `Coprime x u`,

$$
\gcd(x,GTail(d,r,x,u))
=
\gcd\!\left(x,\binom dr\right).
$$

At `r = 1` this yields

$$
\gcd(x,GN_d(x,u))=\gcd(x,d).
$$

Its degree-two specialization supplied the primitive/parity normalization audited in QP-001 through QP-005. This is a useful canonical normal form, but not a strict capacity improvement.

## 6. The obstruction problem — implemented form

For fixed \(n\), define

$$
L_n(u):=n-u,
\qquad
R_n(u):=n+u.
$$

For a prime \(r\), the raw forbidden conditions are

$$
r\mid n-u
\quad\Longleftrightarrow\quad
u\equiv n\pmod r,
$$

and

$$
r\mid n+u
\quad\Longleftrightarrow\quad
u\equiv -n\pmod r.
$$

The implementation distinguishes these raw waves from **proper** obstruction, because endpoint equality `r = n-u` or `r = n+u` must not kill an endpoint that is itself prime.

This endpoint correction is essential and makes the proper obstruction predicate nonperiodic even though its raw residue skeleton is periodic.

## 7. Finite reduction by small prime divisors — implemented

Every composite endpoint in the admissible fiber has a proper prime divisor bounded by the square-root cutoff. Since

$$
n-u\le2n,
\qquad
n+u\le2n,
$$

the complete obstruction world is finite.

The production theorem now gives the exact equivalence

$$
\text{survives all proper small-prime obstructions}
\iff
\operatorname{Prime}(n-u)\land\operatorname{Prime}(n+u).
$$

Thus the unresolved conjecture is exactly the nonemptiness of the finite survivor set for every `n ≥ 2`.

## 8. Paired PrimeWorld / CRT — implemented frontier

The paired residue structure and CRT periodicity have been formalized. For a finite prime world, local forbidden residue counts and the full-period survivor cardinality are exact.

This proves that raw survivors exist in a full product period. It does **not** locate one inside the short admissible Goldbach interval.

The Astra audit further decomposed primitive-parity pair overlap into

$$
LL+LR+RR,
$$

where the cross term `LR` is an oriented CRT product wave. Same-orientation seats are separated by `pq`, or by `2pq` after adjoining the parity coordinate for odd moduli. These spacing results are sharp and still do not imply short-fiber survival.

## 9. Main strategic theorem shape — exact but still open universally

The decisive statement remains

$$
\text{proper old-prime obstruction capacity}
<
\text{Goldbach fiber capacity}.
$$

Production code now packages the exact fixed-center form of this condition as `GoldbachCapacityEscape`, and proves its equivalence with Strong Goldbach.

Therefore any future theorem advertised as a new capacity criterion must be compared against this exact baseline. If it is merely equivalent after a coordinate normalization, it is not strict information gain.

## 10. Parity barrier warning — confirmed

A plain density heuristic such as

$$
\prod_{r\le\sqrt{2n}}
\left(1-\frac{2}{r}\right)
$$

is not a proof strategy.

The subsequent implementation has reinforced this warning:

- exact residue counts do not control short-interval placement;
- local incidence can exceed the number of seats while survivors still remain;
- higher overlap persists after primitive/parity normalization;
- reducing the candidate set can improve relative survivor density without increasing the number of positive survivors;
- candidate cardinality is not a substitute for interval width.

The required next ingredient must be structurally independent of these static sieve/counting reformulations.

## 11. Higher-degree GN as a classifier, not the direct Goldbach equation

Goldbach itself lives naturally at \(d=2\).

For a prime target \(P\), one may still define conceptually

$$
\Sigma(P)
=
\{q\text{ prime}:
\exists x,u,\ GN_q(x,u)=P\}.
$$

Existing DkMath theorems make \(\Sigma(P)\) finite and thin. The open research question is not the existence of such signatures, but whether some **nontrivial transported invariant** across different endpoints or fibers can be extracted from them.

Current code does not supply such a transport theorem.

## 12. Original implementation checkpoints — present status

| # | Original checkpoint | 2026-09-12 status |
|---|---|---|
| 1 | `GoldbachGNFiberAt` | complete |
| 2 | exact equivalence with standard Goldbach pair | complete |
| 3 | `goldbachBody_eq_square_sub_square` | complete |
| 4 | left/right obstruction predicates | complete |
| 5 | small-prime obstruction witness | complete |
| 6 | finite square-root obstruction world | complete |
| 7 | paired residue / PrimeWorld layer | complete |
| 8 | CRT / periodicity | complete |
| 9 | exact local forbidden-seat count | complete |
| 10 | global incidence / capacity | exact ledger complete; universal strict bound unresolved |
| 11 | PCK bridge | implemented, insufficient for simultaneous escape |
| 12 | survivor ⇒ prime-pair closure | complete |
| 13 | final Goldbach endpoint | open |

Post-plan additions now also include:

- exact overlap conservation;
- pair-overlap double counting;
- Pascal pair residual;
- GTail core promotion;
- quadratic primitive/parity normalization;
- LL/LR/RR support split;
- oriented product-wave / spacing audit;
- exact proof that the normalized capacity criterion is only a reformulation of the existing one.

## 13. Stop / success criteria

Do not claim progress toward Goldbach merely from any of the following:

- all odd primes are representable by \(GN_2\);
- prime-row Pascal divisibility;
- full-period finite residue survival;
- primitive/parity normalization;
- reduced obstruction worlds;
- improved relative survivor density;
- CRT spacing or product-wave uniqueness in one period;
- numerical verification over large ranges.

A future branch becomes mathematically decisive only when it supplies **new information** strong enough to force a short-fiber survivor, or proves a genuinely stronger theorem that is not equivalent to the existing capacity condition.

## 14. Current assessment

The original strategy succeeded in converting Goldbach into a concrete formal finite research problem and in implementing almost all static infrastructure proposed in 2026-09-09.

The strongest exact package currently available is

$$
\text{fixed GN fiber}
+
\text{complete proper obstruction world}
+
\text{CRT / PrimeWorld periodicity}
+
\text{exact capacity conservation}
+
\text{overlap / Pascal ledger}
+
\text{primitive/parity normal form}.
$$

What it still lacks is an invariant that changes the **short-fiber location problem** rather than merely reparameterizing it.

Accordingly, the next real decision point is no longer “can the fixed fiber be normalized further?” The Astra audit answered that route at the current level: yes structurally, but without strict information gain.

The next search should target a genuinely dynamic relation — between seats, between neighboring centers, or between scaled fibers — capable of transporting or conserving information that is invisible to one static obstruction cover.
