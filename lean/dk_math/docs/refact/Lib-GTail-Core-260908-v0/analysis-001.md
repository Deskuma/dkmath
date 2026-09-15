# GTail Core Promotion and Boundary-Kernel Unification

Date: 2026-09-08  
Status: research / refactor design note  
Target branch: `develop`

## 0. Executive summary

The central conclusion of the current cross-project investigation is:

> **`GN` is not the canonical mathematical object.  The canonical object is the general higher-tail family `GTail d r x u`; `GN` is only its `r = 1` specialization.**

This was already anticipated and partially implemented in the March 2026 GN/GTail refactor, but subsequent FLT3 / FLT5 / ABC / RH-CFBRC / Primitive / Pascal work has supplied enough evidence that the migration can now be promoted from a compatibility refactor into a DkMath core-design decision.

The intended long-term direction is:

```text
DkMath.Lib.Cosmic.GTail
  ├─ generic decomposition / recursion
  ├─ congruence / boundary-collapse
  ├─ Nat divisibility
  ├─ p-adic depth
  ├─ prime-row / Pascal boundary
  ├─ cyclotomic bridge
  └─ r = 1 specialization
       └─ legacy GN compatibility surface
```

New research code should increasingly reference `DkMath.Lib.*` canonical theorems directly rather than treating `DkMath.CosmicFormulaBinom.GN` or `cosmic_id_csr'` as the mathematical spine.

This note records:

1. what is already implemented and verified,
2. what the recent GN / Primitive / CFBRC investigation reveals,
3. which stronger `GTail` theorems should be formalized,
4. which legacy names should become compatibility wrappers / deprecated names,
5. how to refactor without destabilizing FLT3, FLT5, ABC, RH, or current downstream work,
6. why this work should precede restarting FLT7.

---

## 1. Historical context

The March 2026 GN-tail refactor already reached the key design decision:

```lean
GN d x u := GTail d 1 x u
```

and recorded that downstream code should migrate gradually rather than by a destructive global rename.

The existing history also records why a compatibility layer was necessary:

- downstream code frequently unfolded the explicit old GN sum,
- direct replacement by `GTail` changed reduction shape,
- `GN_eq_sum` was introduced as a compatibility shim,
- targeted and full builds were recovered without rollback.

The May 2026 `Lib-GTail` discussion then generalized the goal: stable, reusable theorems that are not specific to FLT / ABC / RH should be promoted into `DkMath.Lib.*`.

The current investigation shows that the project has now accumulated enough mathematical evidence to finish that promotion.

---

## 2. Canonical definition

The current library definition is:

```lean
@[simp] def GTail {R : Type _} [CommSemiring R]
    (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) *
      x ^ k * u ^ (d - (r + k))
```

Mathematically,

$$
GTail(d,r,x,u)
=
\sum_{k=0}^{d-r}
\binom{d}{r+k}
x^k u^{d-r-k}.
$$

The intended range is

$$
0 \le r \le d.
$$

The standard GN kernel is only

$$
GN_d(x,u)=GTail(d,1,x,u).
$$

This distinction must become visible in the public API and documentation.

---

## 3. The actual core theorem

The strongest already-implemented algebraic theorem is not the old GN identity but the general tail decomposition:

$$
(x+u)^d=\sum_{j<r}\binom dj x^j u^{d-j}+x^r GTail(d,r,x,u).
$$

Lean:

```lean
add_pow_eq_prefix_add_xpow_mul_GTail
```

with the subtraction-shaped companion:

```lean
higher_tail_eq_pow_mul_GTail
```

This should be treated as the canonical Cosmic/GTail decomposition theorem.

The familiar identity

$$
(x+u)^d=u^d + x\,GN_d(x,u)
$$

is only the `r = 1` corollary.

Accordingly, legacy theorems such as `cosmic_id_csr'` should eventually become thin compatibility wrappers over the `DkMath.Lib.Cosmic.GTail` theorem surface.

---

## 4. Existing GTail core already present in `DkMath.Lib.*`

As of this investigation, the following layers already exist.

### 4.1. `DkMath.Lib.Cosmic.GTail`

Verified core:

- `GTail`
- `add_pow_eq_prefix_add_xpow_mul_GTail`
- `higher_tail_eq_pow_mul_GTail`
- `GTail_zero_eq_add_pow`
- `GTail_self_eq_one`
- `GTail_rec`
- `GTail_one_eq_sum`
- `GTail_eval_zero`
- `GN_tail_rec`
- `GN_zero_eval`

The generic recursion is:

$$
GTail(d,r,x,u)=\binom dr u^{d-r}+x\,GTail(d,r+1,x,u).
$$

This equation is the key to the newly clarified boundary interpretation.

### 4.2. `DkMath.Lib.Cosmic.GTailNat`

Verified natural-number consequences include:

- `pow_dvd_higher_tail`
- `GTail_not_dvd_of_head_unit_of_prime_dvd_x`
- the `r = 1` wrapper `GN_not_dvd_of_head_unit_of_prime_dvd_x`

Thus the higher tail already has a generic divisibility layer independent of FLT hypotheses.

### 4.3. `DkMath.Lib.Cosmic.GTailCongruence`

Verified:

- `GTail_congr_of_modEq`
- `GTail_modEq_eval_zero_of_dvd_x`
- `GN_modEq_choose_mul_pow_of_dvd_x`
- `GN_modEq_head_of_dvd_x`
- `GN_modEq_mul_pow_self_of_dvd_x`
- `GN_modEq_head_mod_sq_of_prime_dvd_x`
- `GN_mod_p2_head`
- `GN_eq_head_add_p_sq_mul_of_prime_dvd_x`
- conditional `mod p^3` wrappers

In particular, the generic theorem already implies the boundary collapse

$$
x \equiv 0 \pmod n \quad\Longrightarrow\quad GTail(d,r,x,u) \equiv \binom dr u^{d-r} \pmod n.
$$

This is one of the most important facts for the new interpretation.

### 4.4. `DkMath.Lib.Cosmic.GTailPadic`

Verified:

- valuation-zero theorem for normalized higher tails under a head-unit condition,
- lower bound for the unnormalized higher-tail valuation,
- exact valuation under a head-unit condition,
- `r = 1` GN specialization.

However, this module currently imports:

```lean
DkMath.ABC.PadicValNat
```

This is an architectural inversion: a DkMath core library module should not need to depend on the ABC research package for generic `padicValNat` lemmas.

A refactor should promote the reusable `padicValNat` support lemmas into an appropriate `DkMath.Lib.NumberTheory.*` or equivalent lower layer, and let ABC depend on that canonical layer.

---

## 5. The newly clarified meaning of the tail index `r`

The most important conceptual result of this investigation is that `r` is not merely an implementation index.

From

$$
GTail(d,r,x,u)=\binom dr u^{d-r}+x\,GTail(d,r+1,x,u),
$$

we obtain the boundary reading

$$
GTail(d,r,x,u)\equiv\binom dr u^{d-r}\pmod x.
$$

Therefore:

> **The tail coordinate `r` selects the Pascal coefficient exposed on the boundary `x = 0`.**

The map

$$
r \longmapsto \binom dr
$$

is therefore a boundary-support scan across Pascal row `d`.

This gives a precise connection:

```text
Pascal row
   ↓ choose(d,r)
GTail boundary head
   ↓ modulo x
divisibility support exposed at tail depth r
```

The traditional GN layer uses only `r = 1`, where

$$
\binom d1=d.
$$

For a prime exponent `p`,

$$
\binom p1=p,
$$

so the boundary support of the `r = 1` layer is exceptionally pure: it exposes only the exponent prime.

This explains why GN has repeatedly behaved as a strong Primitive extractor.

---

## 6. Why `r = 1` is special but not fundamental

For prime `p`, the Pascal row begins

$$
1,\;p,\;\binom p2,\;\binom p3,\dots.
$$

For example, at `p = 7`:

$$
1,7,21,35,35,21,7,1.
$$

Thus:

$$
GTail(7,1,x,u) \equiv 7u^6 \pmod x,
$$

$$
GTail(7,2,x,u) \equiv 21u^5 \pmod x,
$$

$$
GTail(7,3,x,u) \equiv 35u^4 \pmod x.
$$

The `r = 1` tail sees the pure support `{7}`, whereas deeper tails expose additional prime support inherited from interior Pascal coefficients.

Therefore the previous empirical success of GN should be reformulated:

> `GN = GTail(_,1,_,_)` is the first nontrivial tail layer, and for prime degree it has the cleanest possible boundary support.

The general theory should nevertheless be stated for all `r`.

---

## 7. Candidate theorem: exact boundary gcd

The generic congruence theorem strongly suggests the following reusable theorem.

### Candidate A

Under suitable natural-number hypotheses,

$$
\gcd\!\left(x,GTail(d,r,x,u)\right)=\gcd\!\left(x,\binom dr u^{d-r}\right).
$$

If additionally

$$
\gcd(x,u)=1,
$$

then the expected simplification is

$$
\boxed{
\gcd\!\left(x,GTail(d,r,x,u)\right)=\gcd\!\left(x,\binom dr\right).
}
$$

For `r = 1` this becomes

$$
\gcd(x,GN_d(x,u))=\gcd(x,d),
$$

again under the appropriate coprimality hypotheses.

For prime degree `p`:

$$
\gcd(x,GN_p(x,u))=\gcd(x,p).
$$

This would compress a large family of downstream boundary / coprimality / exceptional-prime arguments.

**Status:** research target.  Do not treat as already formalized until a repository-wide theorem search confirms the exact theorem or it is proved in the Lib layer.

---

## 8. Candidate theorem: tail-depth transport / filtration

`GTail_rec` transports by one step in `r`.

The natural generalization is an `r → s` split:

for

$$
r \le s \le d,
$$

expect

$$
GTail(d,r,x,u)=\sum_{k=0}^{s-r-1}\binom{d}{r+k}x^k u^{d-r-k}+x^{s-r}GTail(d,s,x,u).
$$

Possible Lean names:

```text
GTail_split_at
GTail_eq_prefix_between_add_pow_mul_GTail
GTail_transport_depth
```

This would make the sequence

$$
GTail(d,0) \to GTail(d,1) \to \cdots \to GTail(d,d)=1
$$

an explicit filtration rather than a collection of unrelated recurrences.

**Status:** research target.

---

## 9. Candidate theorem: prime-row interior `p`-adic rigidity

The current `GN_modEq_head_mod_sq_of_prime_dvd_x` is an `r = 1` theorem.

The general tail structure suggests a stronger prime-row statement.

Let `p` be prime, assume

$$
p\mid x,\qquad p\nmid u.
$$

For interior rows

$$
1 \le r \le p-2,
$$

all interior Pascal coefficients satisfy

$$
v_p\!\left(\binom pr\right)=1.
$$

Using the recurrence, the expected stronger congruence is

$$
GTail(p,r,x,u) \equiv \binom pr u^{p-r} \pmod{p^2},
$$

and hence

$$
v_p(GTail(p,r,x,u))=1.
$$

At the terminal nontrivial layer:

$$
GTail(p,p-1,x,u)=pu+x.
$$

If `x = pt`, then

$$
GTail(p,p-1,x,u)=p(u+t),
$$

so any excess valuation is concentrated in the final linear factor.

This suggests the structural picture:

```text
r = 1 ... p-2:
    normalized tail has rigid p-depth 1

r = p-1:
    excess depth is transferred into a linear terminal kernel

r = p:
    GTail = 1
```

This may be relevant to the ramified-depth machinery appearing in FLT / ABC work.

**Status:** research target.  The current repository contains the `r = 1` `mod p^2` theorem, not this complete `r`-general statement.

---

## 10. Cyclotomic relation

The existing CFBRC cyclotomic work already contains a general-`d` bridge between shifted cyclotomic divisor products and the GN / Cosmic core.

For prime degree `p`, the familiar identity

$$
\frac{X^p-Y^p}{X-Y}=\Phi_p(X,Y)
$$

combined with

$$
X=x+u,\qquad Y=u
$$

identifies

$$
GTail(p,1,x,u)=GN_p(x,u)
$$

with the homogeneous `p`-th cyclotomic shell.

For composite `d`, the full quotient decomposes over divisors:

$$
\frac{X^d-Y^d}{X-Y}=\prod_{\substack{m\mid d\\m>1}}\Phi_m(X,Y).
$$

This gives the structural distinction:

- prime degree: `GTail(p,1)` is a single primitive cyclotomic shell,
- composite degree: the `r = 1` tail contains multiple divisor shells.

The existing `DkMath.CFBRC.CyclotomicProduct` module should be reviewed for promotion / bridge extraction so that this relationship does not remain hidden under the CFBRC package name.

---

## 11. Relation to Pascal / Primitive boundary work

The recent Primitive / Pascal work and the GTail boundary theorem point at the same structure from different directions.

Pascal-side work detects where a prime first appears in binomial coefficients.

GTail-side work exposes a selected Pascal coefficient on the boundary:

$$
GTail(d,r,x,u) \equiv \binom dr u^{d-r} \pmod x.
$$

The `r = 1` prime-degree specialization then exposes exactly the exponent prime.

Therefore a future core API should make the chain explicit:

```text
Pascal coefficient
    ↓
GTail boundary head
    ↓
boundary gcd / congruence
    ↓
exceptional support
    ↓
Primitive / fresh support separation
```

This is a stronger and more reusable abstraction than maintaining separate GN5, GN3, GN7 boundary packages.

---

## 12. Relation to CF2D / CFBRC / RH

The current RH-CFBRC code already bridges complex arithmetic to the CF2D quadratic form:

```text
Complex.normSq ↔ Vec.q2
Complex multiplication ↔ Vec.star
polarization ↔ q2(A+B) - q2(A-B)
```

The analogy with GTail should be treated as a research program, not yet as an established theorem:

- GTail separates a conserved power-difference object into a boundary factor and a normalized residual kernel;
- gcd / valuation measure arithmetic intersection across that boundary;
- CF2D keeps a quadratic invariant and CFBRC polarization measures interaction / collision between states.

A package-wide audit should test whether these are projections of one common “conservation boundary kernel” abstraction.

No claim of equivalence should be made until a precise bridge is formalized.

---

## 13. Architectural issue: `DkMath.Lib.*` must not depend upward on research packages

Current example:

```text
DkMath.Lib.Cosmic.GTailPadic
    imports
DkMath.ABC.PadicValNat
```

This should be inverted.

Reusable theorems currently located in `DkMath.ABC.PadicValNat`, such as generic facts about:

- `padicValNat` and divisibility,
- valuation of powers,
- basic lower / upper conversions,

should be audited and promoted into a lower library module, for example:

```text
DkMath.Lib.NumberTheory.PadicValNat
```

or another naming-compatible lower layer.

Then:

```text
DkMath.Lib.NumberTheory.PadicValNat
       ↓
DkMath.Lib.Cosmic.GTailPadic
       ↓
ABC / FLT / Primitive / other research packages
```

must replace the current reverse dependency.

---

## 14. GNZC migration policy

The `[GNZC]` marker already exists specifically to identify naming / migration sites.

The next audit should classify every `[GNZC]` occurrence into one of four classes.

### A. Canonical GTail theorem

Keep / strengthen in `DkMath.Lib.Cosmic.*`.

### B. Useful `r = 1` theorem

Create a generic GTail theorem first, then keep the GN theorem only as a thin specialization if the name remains useful.

### C. Compatibility-only legacy name

Mark deprecated after the canonical replacement is available.

Examples likely include old `Gbinom_*` names and duplicated GN names whose only purpose is compatibility.

### D. Separate mathematical family

Do not mechanically migrate merely because the name contains `G`, `GN`, or `[GNZC]`.

For example, Body-normalized `GZ` and future complex `GC` may be related families but are not necessarily aliases of the gap-normalized tail.

---

## 15. Deprecation direction

The migration should be staged.

### Phase 0 — inventory

Run repository-wide searches, at minimum:

```bash
rg -n "\[GNZC\]" DkMath docs
rg -n "abbrev GN|def GN|GTail d 1|CosmicFormulaBinom\.GN|CosmicFormula\.GN" DkMath
rg -n "cosmic_id_csr'|cosmic_id_csr" DkMath
rg -n "unfold GN|simp \[GN\]|rw \[GN_eq_sum\]" DkMath
rg -n "GTail" DkMath
```

Classify by import layer and semantic role.

### Phase 1 — complete canonical GTail theorem surface

Before adding deprecations, implement / locate the generic theorems needed by downstream code.

Priority candidates:

1. exact boundary gcd,
2. `r → s` tail transport,
3. prime-row generic `mod p^2`,
4. exact interior prime-row valuation,
5. terminal linear-layer theorem,
6. lightweight cyclotomic bridge,
7. generic finite-difference / higher-remainder interpretation where useful.

### Phase 2 — fix Lib dependency direction

Move reusable `padicValNat` support out of ABC.

No `DkMath.Lib.*` core module should import FLT / ABC / RH research modules.

### Phase 3 — canonical wrappers

Rewrite existing GN-specific theorems as thin corollaries of GTail theorems wherever possible.

### Phase 4 — deprecations

Add `@[deprecated ...]` only when:

- replacement theorem exists,
- replacement import path is stable,
- downstream migration is mechanically clear,
- focused builds demonstrate no hidden semantic mismatch.

### Phase 5 — downstream migration

Suggested order:

1. CosmicFormula legacy surface,
2. NumberTheory / Gcd / Primitive,
3. Pascal / StructuralArithmetic,
4. FLT3 / FLT5,
5. ABC,
6. RH / CFBRC / CFZP,
7. FLT7 experimental branch.

### Phase 6 — compatibility facade

Keep old public names only where external documents or standalone proofs benefit from them.

New DkMath research code should prefer canonical `DkMath.Lib.*` imports.

---

## 16. `cosmic_id_csr'` migration

The identity represented by `cosmic_id_csr'` remains mathematically useful, but its implementation status should change.

Rather than treating it as a root theorem, define / prove the canonical Lib-side specialization directly from:

```lean
add_pow_eq_prefix_add_xpow_mul_GTail
```

at `r = 1`.

Then make `cosmic_id_csr'` a compatibility theorem pointing to the canonical Lib theorem.

This preserves old proof scripts while making the dependency graph reflect the true mathematics:

```text
GTail general decomposition
       ↓
r = 1 power-difference identity
       ↓
legacy cosmic_id_csr'
       ↓
old downstream code
```

---

## 17. Why this should precede FLT7

FLT3 and FLT5 have now shown that relatively small, standalone-capable proof models can be obtained when the correct arithmetic kernel is exposed.

The current hypothesis is not that each of

```text
GN3
GN5
GN7
GN11
GN13
...
```

should be developed independently.

Instead, the relevant structure is:

```text
GTail(d,r)
  ↓ boundary coefficient choose(d,r)
  ↓ divisibility / gcd boundary
  ↓ valuation depth
  ↓ primitive support
  ↓ cyclotomic shell
```

with the prime-exponent / `r = 1` case being the particularly pure specialization used by FLT.

Therefore FLT7 should not be restarted until the GTail core refactor can answer:

1. Which FLT7 lemmas are already corollaries of generic GTail boundary theorems?
2. Which ramified-depth lemmas are instances of generic prime-row tail valuation?
3. Which cyclotomic machinery can be replaced by a lightweight GTail/cyclotomic bridge?
4. Which old GN-specific theorems should disappear from the FLT7 dependency graph?

FLT7 should become a test instance of the general core, not another independent source of core arithmetic.

---

## 18. Connection to general FLT

The already-known composition structure of GN / power differences suggests that once the prime-degree boundary kernel is understood, composite degrees should be handled through factor / divisor structure rather than independently.

The long-term research target is therefore not “prove FLT7, then FLT11, then FLT13”.

It is:

> **formalize the prime-degree GTail boundary / primitive / valuation mechanism once, then determine whether FLT at prime exponent is a uniform specialization.**

The current work does not claim this general FLT closure has been achieved.

It defines the correct pre-FLT7 research program.

---

## 19. Proposed DkMath core module shape

A tentative module layout:

```text
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailNat
DkMath.Lib.Cosmic.GTailCongruence
DkMath.Lib.Cosmic.GTailBoundary
DkMath.Lib.Cosmic.GTailPascal
DkMath.Lib.Cosmic.GTailPadic
DkMath.Lib.Cosmic.GTailCyclotomic

DkMath.Lib.NumberTheory.PadicValNat
```

Possible role split:

- `GTail`: algebra over `CommSemiring / CommRing`
- `GTailNat`: `ℕ` divisibility
- `GTailCongruence`: `Nat.ModEq`
- `GTailBoundary`: gcd / coprimality / support intersection
- `GTailPascal`: `Nat.choose` prime-row support results
- `GTailPadic`: exact depth / valuation
- `GTailCyclotomic`: prime-degree and divisor-product bridges
- `Lib.NumberTheory.PadicValNat`: research-independent valuation utilities

This is a proposal, not a mandatory final naming scheme.

---

## 20. Acceptance criteria for the refactor

A GTail-core promotion branch should not be considered complete merely because files have moved.

Minimum criteria:

1. `GTail` has one canonical definition.
2. generic decomposition is the root theorem.
3. GN is visibly documented as `r = 1` specialization.
4. no core `DkMath.Lib.*` file imports ABC / FLT / RH packages.
5. all promoted theorems are free of `sorry` / `admit`.
6. focused builds for the Lib modules succeed.
7. FLT3 and FLT5 focused builds remain green.
8. representative ABC and RH/CFBRC builds remain green.
9. deprecated names have explicit canonical replacements.
10. standalone / museum builds that intentionally retain compatibility names continue to work.
11. theorem axioms are checked for important new core endpoints.
12. the documentation distinguishes proved facts from research conjectures / candidates.

---

## 21. Immediate next implementation tasks

Recommended order:

### GTCORE-000 — inventory

Produce a machine-readable / Markdown inventory of:

- all `[GNZC]` sites,
- all `GN` definitions / abbreviations,
- all `cosmic_id_csr*` references,
- all generic `GTail` theorems,
- all duplicated gcd / valuation / congruence theorems in ABC / FLT / Primitive / CFBRC.

### GTCORE-001 — dependency inversion

Extract generic `padicValNat` utilities from `DkMath.ABC.PadicValNat` into `DkMath.Lib.NumberTheory.*`, then migrate `GTailPadic`.

### GTCORE-002 — exact boundary gcd

Locate an existing theorem or prove the generic boundary gcd theorem.

### GTCORE-003 — tail filtration

Implement the `r → s` transport theorem.

### GTCORE-004 — prime-row higher-tail boundary

Generalize the current `r = 1` `mod p^2` theorem to interior `r`.

### GTCORE-005 — cyclotomic promotion audit

Extract the reusable core of `DkMath.CFBRC.CyclotomicProduct` into an appropriate Lib bridge without importing analytic CFBRC machinery.

### GTCORE-006 — compatibility / deprecated layer

Convert old GN / `cosmic_id_csr'` endpoints into documented wrappers with staged deprecations.

### GTCORE-007 — cross-project replay

Replay FLT3, FLT5, ABC representative targets, Primitive / Pascal targets, and RH-CFBRC focused targets against the canonical GTail core.

### GTCORE-008 — FLT7 re-entry report

Only after the above, compare the FLT7 dependency graph with the new GTail core and decide what can be deleted or replaced.

---

## 22. Final research statement

The present DkMath evidence supports the following interpretation:

> **GTail is a general boundary-kernel extractor for the binomial conservation identity.**
>
> The tail depth `r` selects a Pascal coefficient on the boundary.  
> The `r = 1` specialization, historically named GN, is unusually powerful at prime degree because its boundary coefficient is exactly the exponent prime.  
> Divisibility, gcd, valuation, Primitive support, and cyclotomic structure should therefore be organized below the GTail family rather than rebuilt independently in FLT / ABC / RH packages.

This interpretation remains partly a research program: the exact gcd theorem, the full prime-row higher-tail valuation theorem, the common abstraction with CF2D/CFBRC, and a uniform general-FLT closure are not claimed here as completed results.

But the repository is now mature enough that `GTail` should become a first-class DkMath core object and legacy GN-centric APIs should begin a controlled deprecation cycle.

---

## 23. Source files reviewed for this note

Primary current sources on `develop`:

```text
lean/dk_math/DkMath/Lib/Cosmic/GTail.lean
lean/dk_math/DkMath/Lib/Cosmic/GTailNat.lean
lean/dk_math/DkMath/Lib/Cosmic/GTailCongruence.lean
lean/dk_math/DkMath/Lib/Cosmic/GTailPadic.lean
lean/dk_math/DkMath/CosmicFormula/Defs.lean
lean/dk_math/DkMath/ABC/PadicValNat.lean
lean/dk_math/DkMath/CFBRC/CyclotomicProduct.lean
lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiPrimeSideCF2DPolarizationBridgeAudit.lean
lean/dk_math/docs/dev/GN-Tail-260326-v0/History-001.md
lean/dk_math/docs/refact/Lib-GTail-260501/discussion.md
```

The `[GNZC]` search tag remains the primary migration marker for follow-up inventory.
