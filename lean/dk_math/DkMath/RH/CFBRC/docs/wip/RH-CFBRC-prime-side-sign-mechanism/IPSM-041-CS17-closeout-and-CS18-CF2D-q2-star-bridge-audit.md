# IPSM-041 — CS17 closeout and CS18 CF2D q2/star bridge audit

## Status

CS17 is accepted as **Green-B**.

The normalized finite-ray polarization layer now closes, in ordinary complex analysis, all of the following finite identities without importing CF2D:

- exact polarization of `Re (A * conj B)`;
- normalized plus/minus densities;
- nonnegativity of each density;
- finite ray kernel as one half-window plus/minus energy difference;
- nonnegativity of the two interval energies;
- single-ray ordering equivalence;
- prime-weighted aggregate plus/minus energy ledger;
- exact transport of finite block projection to cutoff differences of aggregate energies;
- explicit named gap for the missing independent aggregate ordering provider.

No infinite exchange, endpoint sign theorem, or RH conclusion has been introduced.

The next checkpoint is intentionally a **bridge audit**, not a sign theorem.

The goal is to determine whether the complex polarization structure already exposed by CS17 is literally the existing CF2D `star/q2` algebra, and whether that translation reduces the aggregate ordering frontier or merely renames it.

---

## Why CS18 is now authorized

Earlier checkpoints deliberately kept CF2D out of the prime-side derivation. That firewall has served its purpose: the prime-side structure has now independently produced

```text
complex multiplication
+ conjugation
+ normSq
+ plus/minus polarization
+ prime-power repeated modes
```

without assuming any CF2D theorem.

The existing general library already has

```text
DkMath.CosmicFormula.Rotation.CF2D.Basic
DkMath.CosmicFormula.Rotation.CF2D.KernelPower
DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
DkMath.CosmicFormula.ThreeElement.Assimilation
DkMath.CosmicFormula.ThreeElement.Collision
```

The bridge audit may therefore compare two independently constructed surfaces.

Do not modify the general CF2D library unless a genuinely reusable missing theorem is discovered. Prefer a chained RH audit module first.

Suggested file:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCF2DPolarizationBridgeAudit
```

Import CS17 and only the minimum CF2D modules needed.

---

## CS18-A — canonical complex-to-CF2D coordinate bridge

Define a local exact coordinate embedding, conceptually

```lean
noncomputable def complexAsCF2DVec (z : ℂ) : CF2D.Vec ℝ :=
  ⟨z.re, z.im⟩
```

Use a repository-appropriate name with the usual long prefix if kept in the RH namespace.

Prove the basic adapters:

```text
core (vec z) = z.re
beam (vec z) = z.im
Vec.q2 (vec z) = Complex.normSq z
vec (conj z) = Vec.conj (vec z)
vec 0 = (0,0)
vec 1 = (1,0)
```

The crucial multiplication theorem is

```text
vec (z * w) = Vec.star (vec z) (vec w).
```

This should be a direct coordinate/ring proof because `Vec.star` is the complex multiplication polynomial.

Consequences worth recording if they are cheap:

```text
Complex.normSq (z * w)
  = Vec.q2 (Vec.star (vec z) (vec w))
  = Vec.q2 (vec z) * Vec.q2 (vec w).
```

Do not use these identities to infer a sign that was not already present.

---

## CS18-B — CS17 polarization is literally a q2 polarization

Let

```text
A = finite geometric-ray endpoint amplitude,
B = finite geometric-ray denominator vector.
```

CS17 proved

$$
4\operatorname{Re}(A\overline B)
=|A+B|^2-|A-B|^2.
$$

Transport this to CF2D:

$$
4\operatorname{Re}(A\overline B)
= q2(\operatorname{vec}(A+B))
- q2(\operatorname{vec}(A-B)).
$$

Prefer exact theorem statements connecting the existing CS17 plus/minus numerator masses to `Vec.q2` rather than reproving polarization from scratch.

Then transport the normalized densities:

```text
PlusDensity(t)
  = q2(vec (A+B)) / q2(vec B)

MinusDensity(t)
  = q2(vec (A-B)) / q2(vec B).
```

The denominator is already strictly positive from CS16.

This gate establishes that the two nonnegative CS17 densities are genuinely normalized CF2D square masses.

---

## CS18-C — quotient-normalized ray state

CS17 already proves the finite ray amplitude is the quotient

```text
R(t) = A(t) / B(t).
```

Because `B(t) ≠ 0`, derive the cleaner normalized identities if proof friction is reasonable:

$$
E_+(t)=|R(t)+1|^2,
\qquad
E_-(t)=|R(t)-1|^2.
$$

Then express them in CF2D form:

$$
E_+(t)=q2(\operatorname{vec}(R(t)+1)),
\qquad
E_-(t)=q2(\operatorname{vec}(R(t)-1)).
$$

This is the smallest pointwise state currently visible.

Record the exact ordering equivalence:

$$
E_-(t)\le E_+(t)
\iff 0\le \operatorname{Re}R(t).
$$

This is an adapter only. It is not an independent sign provider.

---

## CS18-D — two-channel ThreeElement interpretation

The ordinary complex polarization decomposes into independent real and imaginary coordinate channels.

For arbitrary `A B : ℂ`, define two CF2D states conceptually

```text
Z_re = (A.re, B.re),
Z_im = (A.im, B.im).
```

Using `CF2D.ThreeElementBridge`, prove exact identities of the form

$$
\operatorname{cf2dPlusWhole}(Z_{re})
+\operatorname{cf2dPlusWhole}(Z_{im})
=|A+B|^2,
$$

$$
\operatorname{cf2dMinusWhole}(Z_{re})
+\operatorname{cf2dMinusWhole}(Z_{im})
=|A-B|^2,
$$

and

$$
\operatorname{cf2dInteractionBeam}(Z_{re})
+\operatorname{cf2dInteractionBeam}(Z_{im})
=2\operatorname{Re}(A\overline B).
$$

Hence

$$
(\text{plus whole total})-(\text{minus whole total})
=4\operatorname{Re}(A\overline B).
$$

This is the precise place to test the old Core / interaction-Beam / Gap vocabulary against the newly derived prime-side surface.

Important: `Vec.beam` and `cf2dInteractionBeam` remain distinct. Preserve the existing library firewall.

---

## CS18-E — prime-power phase powers versus CF2D kernel powers

CS14/CS15 exposed a fixed-prime ray as repeated powers of

```text
q_p(s) = p^(-s).
```

The complex-to-CF2D multiplication bridge should give a purely algebraic finite law

```text
vec (q ^ n)
```

as an `n`-fold `Vec.star` product.

If convenient, package a finite theorem by induction rather than introducing new global instances.

Then audit the unit-phase specialization. On the right edge

```text
q_p(σ + it)
```

has a fixed radial magnitude `p^(-σ)` and a repeated phase increment `-t log p`.

The existing `CF2D.KernelPower` API gives

```text
K(n • θ) = K(θ)^n
```

for unit kernels.

A useful optional theorem is therefore a finite decomposition of a prime-power mode into

```text
radial scale p^(-n σ)
×
unit CF2D kernel power at phase -t log p.
```

Do not force this theorem if complex `cpow` normalization creates disproportionate proof overhead. CS18 is Green-B without it.

Do not introduce an infinite Euler product or infinite geometric ray.

---

## CS18-F — aggregate q2 energy ledger

Transport the already-proved CS17 aggregate energies to q2 notation.

The target is not a new numeric theorem; it is an exact structural identity showing that

```text
AggregateRayPlusEnergy
AggregateRayMinusEnergy
```

are finite positive `log p` weighted sums of interval integrals of normalized q2 masses.

Then restate the CS17 frontier as

```text
AggregateMinusQ2Energy ≤ AggregatePlusQ2Energy
```

if useful.

The new theorem must remain equivalent to the existing CS17 ordering gap.

A mere q2 rename is not progress toward the provider unless an additional independent CF2D theorem applies.

---

## CS18-G — collision applicability audit

This gate is critical.

The existing general collision theorem is a **same-object / same-filter / same-target limit theorem**:

```text
PairWholeAssimilation F l B
+
InteractionAssimilation F l B
+
B ≠ 0
→ False.
```

The current CS17 problem is a **finite ordering** problem at fixed `ε`, `W`, and cutoff `X`.

Therefore do not apply `SameObjectCollisionObstruction` merely because plus/minus masses and an interaction term have appeared.

Audit explicitly whether the prime-side construction provides all of the following from independent source data:

1. one actual `ThreeElementFlow`;
2. one filter;
3. one common target `B` for plus and minus wholes;
4. the same interaction observation tending to that same target;
5. a source-derived proof `B ≠ 0`.

If any one is missing, record the collision route as not yet applicable.

A suitable named frontier may be

```lean
inductive PascalCenteredXiPrimeSideCF2DCollisionBridgeGap : Prop
  | noSourceDerivedSameObjectAssimilationPackage
```

or a more precise split gap if the audit identifies separate missing contracts.

Do not manufacture any of these providers from RH-equivalent fixed-defect facts.

---

## CS18-H — what would count as a real shortcut

The CF2D audit is successful as a mathematical shortcut only if it supplies something strictly stronger than the already-known algebraic equivalence.

Examples of genuine progress would be:

- an existing q2/star theorem that implies an aggregate plus/minus ordering without assuming that ordering;
- a preservation law that makes the aggregate difference a boundary term with a certified sign;
- a same-object assimilation package whose hypotheses are independently supplied by the prime-side finite/limit construction;
- a noncollapse/collision theorem that excludes the forbidden ordering configuration from source-derived contracts.

The following do **not** count as progress:

```text
normSq renamed q2
polarization reproved in CF2D notation
ordering assumed as a provider
RH-equivalent fixed defect imported to force the sign
same-object collision invoked with synthetic assimilation hypotheses
```

A negative audit result is acceptable and should be recorded honestly.

---

## Suggested implementation order

```text
CS18-A  complex ↔ CF2D Vec exact bridge
  ↓
CS18-B  normSq polarization ↔ q2 polarization
  ↓
CS18-C  normalized ray state R = A/B
  ↓
CS18-D  two-channel ThreeElement decomposition
  ↓
CS18-E  finite prime-power star / optional unit-kernel power bridge
  ↓
CS18-F  aggregate q2 ledger
  ↓
CS18-G  collision applicability audit
```

Keep CS17 frozen.

---

## Green criteria

CS18 is **Green-B** if it establishes, without synthetic sign assumptions:

1. an exact local complex-to-CF2D coordinate bridge;
2. `Complex.normSq = Vec.q2` under that bridge;
3. complex multiplication corresponds to `Vec.star`;
4. CS17 plus/minus densities are exact normalized q2 masses;
5. the complex polarization admits the two-channel ThreeElement interpretation;
6. the finite prime-power power law is connected to repeated `star` if practical;
7. the aggregate ordering frontier is restated without strengthening it;
8. collision applicability is audited with all same-object obligations explicit;
9. any missing provider is left as a named gap.

No infinite exchange, no endpoint sign theorem, no RH conclusion, and no synthetic collision package are authorized.

If the existing CF2D library yields an actual new source-derived ordering or collision obstruction, stop and document the exact theorem chain before propagating it into the prime-side sign mechanism.
