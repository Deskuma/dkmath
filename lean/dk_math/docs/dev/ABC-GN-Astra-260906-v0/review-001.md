# review-001 — ABC–GN Astra campaign pause review

## Status

This review records the strategic interpretation of the Astra-001 production
run that landed at:

```text
branch:
  wip/ABC-GN-astra-260906-v0

HEAD:
  ac8c678b79f99924b771e9f5774ccaa7f2fd447a

commit:
  impl: 001 — orientation foundation + autonomous frontier attack
```

The full ABC test surface rebuilt successfully:

```text
Build completed successfully (8803 jobs).
```

The new theorems reported by the focused audit depend only on the standard Lean
/ Mathlib trust boundary:

```text
propext
Classical.choice
Quot.sound
```

No new ABC proof in this campaign depends on `abc_main_axiom` or `sorryAx`.

This file is intentionally named `review-001.md` rather than
`report-001.md`: the Astra run exhausted its available execution budget before
it could write its own final report, while the implementation and verification
artifacts had already landed successfully.

---

## 1. Overall assessment

The Astra-001 run changed the research map materially.

The main gain was not merely a stronger local upper bound. It established that
the previous large-profile summation target itself is structurally too loose.

The decisive change is:

```text
OLD frontier:
  deep GN-Wieferich / repeated valuation
  -> large profile
  -> bound GNExcessLargeBoundaryProfileSum
  -> ABC

NEW frontier:
  local depths are independently realizable
  -> formal profile space contains many unrealizable combinations
  -> the canonical raw large-profile sum overcounts ghost profiles
  -> realizability / joint-height constraints must be built into the object
  -> only then should one return to global counting or ABC-quality coupling
```

This is a genuine strategy-level advance.

---

## 2. Productionized cubic orientation foundation

For

```text
F = GN 3 a b
G = GN 3 b a
```

the two exact Bézout-type identities were formalized:

```text
(3*b - 9*a) * F + (3*a + 5*b) * G = 14*b^3

(3*a - 9*b) * G + (3*b + 5*a) * F = 14*a^3
```

Under `Nat.Coprime a b`, this yields:

```text
gcd (GN 3 a b) (GN 3 b a) ∣ 14.
```

Consequences formalized in the production API include:

- no prime square divides both cubic orientations,
- the non-exceptional GN-Wieferich prime sets of the two orientations are
  disjoint,
- the actual non-exceptional repeated parts of the two orientations are
  coprime.

An important semantic distinction is now fixed:

```text
ordinary prime support may overlap at 7,
but repeated support cannot overlap.
```

The numerical regression

```text
a = 605
b = 370688
c = 371293
```

confirms:

```text
GN 3 a b
  = 7 * 37^2 * 1777 * 24247

GN 3 b a
  = 7^3 * 9721 * 41413

repeated moduli:
  37^2 = 1369
  7^3  = 343

gcd of the two GN values:
  7
```

Thus both orientations can contain repeated prime powers while the repeated
prime supports remain separated.

The smaller example

```text
a = 11
b = 40
c = 51

GN 3 11 40 = 79^2
GN 3 40 11 = 7^2 * 67
```

permanently rules out the stronger but false heuristic that one orientation
should always be squarefree or Wieferich-free.

---

## 3. The cubic 3/8 target estimate survives

The actual current target-weight definitions support the cubic-specific
estimate at `t = 3/8`.

The production theorem is:

```text
GNExcess_cubic_target_boundaryWeight_le_repeatedPart_three_eighths
```

Conceptually:

```text
rootAddressCharge
  * exp ((3/8) * activeProfileMass)
<=
  (GNNonExceptionalRepeatedPart 3 a b : ℝ)^(3/8).
```

For every active non-exceptional cubic prime:

```text
q % 3 = 1
  -> q >= 7
  -> 2^8 <= q^3.
```

This improves the previous general odd-prime target-level `3/4` diagnosis.

However, this theorem remains a one-target-profile theorem. It is not a bound
for the full large-profile sum.

---

## 4. Local depth conflict is not the obstruction

A particularly important negative result is that the two orientations can be
forced to arbitrary exact local depths independently.

The production theory proves arithmetic progressions on which, for arbitrary
positive depths `k,l`:

```text
v_7  (GN 3 a 1) = k
v_13 (GN 3 1 a) = l
```

exactly, and both equalities persist along an infinite arithmetic progression.

Relevant declarations include:

```text
exists_GN_three_pair_exact_depth_progression
exists_GN_three_seven_thirteen_exact_depth_progression
exists_large_GN_three_seven_thirteen_exact_depth
```

Therefore the strategy

```text
"one orientation becoming very deep forces the other to become shallow"
```

is dead.

Finite Hensel uniqueness is compatible with arbitrarily deep paired local
behavior and must not be interpreted as a global sparsity theorem.

---

## 5. Coprime repeated parts can both become arbitrarily large

The new ABC-side theorem

```text
exists_arbitrarily_large_coprime_cubic_repeated_parts
```

shows that the two cubic repeated parts can remain coprime while both exceed an
arbitrarily prescribed fixed bound.

Hence orientation coprimality is not a mechanism that prevents both sides from
becoming large.

Its correct interpretation is:

> deep repeated debt in the two orientations must be paid using different
> prime resources.

That fact may matter once the original ABC radical / height budget is coupled
back in, but local coprimality alone does not close the problem.

---

## 6. The canonical large-profile sum overcounts unrealizable profiles

This is the most important strategic result of the run.

The existing profile space bounds each prime depth separately. That allows
formal combinations in which every local prime-power depth satisfies its own
individual bound while the product modulus is too large for any cubic GN value
in the interval.

The Astra run formalized an explicit two-prime family based on `7` and `13`.

For these profiles:

- each local depth individually fits the current profile-space bound,
- the joint modulus is too large,
- the corresponding exact profile event is empty.

The production theorem

```text
GNExcessTwoPrimeProfile_event_eq_empty
```

makes the overcount exact.

Representative values:

```text
X = 13

local powers:
  49
  169

joint modulus:
  8281

cubic height upper bound:
  588

event:
  empty
```

This is not an edge effect. It creates an infinite family of ghost profiles.

---

## 7. The old linear large-profile target is false

The overcount is strong enough to prove:

```text
not_exists_GNExcess_cubic_largeBoundary_linear_bound
```

At `t = 3/8`, there is no constant `C` such that the present canonical raw
sum satisfies a uniform estimate

```text
GNExcessLargeBoundaryProfileSum ...
  <= C * (X + 1)
```

for all relevant `X`.

This is a theorem about the current summation object. It is not a
counterexample to ABC.

The reason is that the sum continues to charge positive weight for profiles
whose realization event is empty.

The numeric lower bounds already exhibit geometric divergence after
normalization:

```text
m = 0:       2 / 7
m = 1:      52 / 7
m = 2:    1352 / 7
m = 4:  913952 / 7
```

Thus no improvement of the single-profile exponent alone can repair the old
raw summation route.

---

## 8. The missing invariant is realizability / joint height

The Astra run also proved the necessary height restriction for any realized
cubic profile:

```text
GNExcess_cubic_realized_modulus_le_height
```

Conceptually:

```text
realized profile e in interval [0,X]
  ->
profile modulus M(e) <= 3 * (X + 1)^2.
```

If

```text
M(e) = product q^(e_q + 1),
```

then realizability forces the logarithmic joint-height constraint

```text
sum (e_q + 1) * log q
  <= log 3 + 2 * log (X + 1).
```

The current canonical profile space is essentially rectangular in the separate
depth coordinates.

Actual realized profiles live inside a joint weighted-height region.

A useful mental model is:

```text
current formal space:
  large rectangular depth box

realized cubic profiles:
  weighted simplex / height-constrained subset
```

The previous large-profile sum diverges because it sums over much of the box,
including points outside the realizable region.

---

## 9. Interpretation of the 3/8 theorem after the height result

The `3/8` theorem remains valuable.

For a realized target profile:

```text
weight <= M^(3/8)
```

and realizability gives:

```text
M <= 3 * (X + 1)^2.
```

Therefore the target-level scale becomes

```text
weight
  <= 3^(3/8) * (X + 1)^(3/4).
```

So an individual realized large profile is sublinear in the interval scale.

The remaining difficulty is no longer an excessively heavy individual profile.

It is:

> how many realized profiles exist, how their realization fibers overlap, and
> how their total contribution couples to the original ABC triple.

This is a much sharper frontier.

---

## 10. Revised research map

The earlier picture was approximately:

```text
deep valuation
  -> GN-Wieferich
  -> large profile
  -> bound all large profiles
  -> ABC
```

After Astra-001 the better map is:

```text
local q-adic depths
  are freely and independently realizable
             |
             v
huge formal profile space
             |
             +---- unrealizable ghost profiles
             |        |
             |        +--> make the old raw sum superlinear
             |
             +---- realized profiles
                      |
                      v
              joint height conservation
              M <= 3 * (X + 1)^2
                      |
                      v
              actual cubic realizability
                      |
                      v
        radical / quality coupling or descent
```

The research object has therefore changed from

```text
depth
```

to

```text
globally realizable configurations of depth
```

This is the main mathematical conclusion of this review.

---

## 11. Likely next implementation phase

This branch is paused after this review.

The next active phase should use ordinary Codex / Luna capacity to materialize
the Astra discoveries rather than immediately spend another high-cost Astra
invocation.

Candidate engineering tasks include:

1. consolidate and document the production orientation API,
2. introduce a clean notion of height-admissible profile,
3. introduce or expose realized-profile predicates / finite sets,
4. prove the bridge `realized -> height-admissible`,
5. define a realizability-aware replacement for the old canonical
   large-boundary sum,
6. develop exact finite counting / fiber APIs around the new object,
7. reconnect only after that to `abcEpsilon`, quality, joint pressure, or
   descent.

The immediate implementation phase should not attempt to prove ABC.

It should first replace the now-refuted overcounting object by a mathematically
honest one.

Once the realizability-aware framework exposes a genuinely new unknown
mathematical obstruction, that will be the appropriate point to consider
another Astra invocation.

---

## 12. Campaign pause status

```text
ABC-GN Astra Campaign 260906 v0

status:
  PAUSED

reason:
  first two Astra reconnaissance / attack runs completed;
  new strategy-level information obtained;
  next work is primarily implementation and API consolidation.

resume mode:
  Codex Luna / ordinary implementation workflow

next Astra use:
  only when a new mathematical discovery or major branch-selection problem
  appears.
```

No `instruction-002.md` is created at this pause point.
