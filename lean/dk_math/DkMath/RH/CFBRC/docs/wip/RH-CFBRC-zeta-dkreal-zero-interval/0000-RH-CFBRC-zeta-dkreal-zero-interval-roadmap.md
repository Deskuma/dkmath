# RH-CFBRC Zeta DkReal Zero Interval Roadmap

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Base: `develop` at `5749f61000bb630580de056344e7fd80a00938de`

Date: 2026-08-19

## 0. Reset

This branch is a fresh research route after closing and merging the former CFZP branch.

The former CFZP numbering is retired here. New work starts from `ZDI-001`.

`ZDI` means **Zeta / DkReal / Interval**.

Historical CFZP modules remain available as audited material, including failed routes and valid finite identities, but their forward numbering is not continued.

## 1. Formal target

The final target is exactly Mathlib's `RiemannHypothesis`:

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
    s.re = 1 / 2
```

The already formalized CFBRC critical-line theorem is not to be re-proved by a new analytic route:

```lean
offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

for positive degree `d`.

The remaining research problem is the standard-zeta zero-preserving step, preferably through finite algebraic certificates and nested rational intervals.

## 2. Separation of problems

Two mathematical questions must not be mixed.

1. **Critical-line geometry**: the CFBRC zero locus selects `σ = 1 / 2`. This is already Lean-proved.
2. **Prime-derived zero pattern**: explain why every standard nontrivial Riemann-zeta zero is forced into that zero locus.

The second question may contain substantially more arithmetic structure than is needed for the final RH theorem. Such extra structure is useful as a source of finite certificates, but it must not be confused with a second proof of the critical line.

## 3. Lean-first research discipline

### 3.1 A compiled `def` is not a semantic proof

A Lean `def` creates an object or predicate. Compilation proves only that the definition is well-typed. It does not prove that the definition matches the intended external mathematical object or that its hypotheses are realizable.

Every load-bearing definition introduced on this route must therefore be accompanied by appropriate **meaning-guarantee theorems**.

For each important `def`, audit all applicable items below before downstream use:

- **characterization**: reduce the definition to already fixed primitive data by an equality or `iff` theorem;
- **realizability / consistency**: prove that the intended hypotheses can actually hold, or prove and name the obstruction if they cannot;
- **source provenance**: show that the quantity is derived from an earlier exact source rather than inserted because the desired theorem needs it;
- **frontier audit**: check whether the new proposition is already equivalent to `RiemannHypothesis`;
- **axiom audit**: inspect the final dependency chain with `#print axioms`; declarations depending on `sorry` are not accepted as closed facts.

### 3.2 No theorem-progress credit without realizability

A theorem of the form `P → Q` is not counted as research progress toward `Q` until the route has audited whether `P` is realizable under the actual parent structures and invariants.

### 3.3 RH-equivalent propositions are frontiers, not providers

If Lean proves `P ↔ RiemannHypothesis`, then `P` must be labeled an RH-equivalent frontier. It must not later be imported as an independent auxiliary lemma in a purported proof of RH.

### 3.4 External mathematical tradition is not a definition source

Historical papers, standard analytic conventions, and model training knowledge may suggest experiments, but they must not determine load-bearing definitions without an internal Lean derivation from fixed source objects.

The unknown problem has no authorized answer to copy.

### 3.5 Simplicity is allowed

The age or difficulty of RH does not imply that the final Lean argument must be long or analytically complicated. Prefer the smallest exact structure that closes the formal target.

## 4. Preferred DkReal interval route

For a standard nontrivial zeta zero `s`, seek finite prime-derived certificates producing rational radii `q n : ℚ` with the following structure:

- `0 ≤ q n`;
- the associated rational intervals are nested;
- the interval widths tend to zero;
- every stage contains `s.re` after coercion to `ℝ`;
- every stage contains `(1 : ℝ) / 2`.

A canonical target shape is

`I_n = [1/2 - q_n, 1/2 + q_n]`.

The load-bearing finite statement is therefore a bound of the form

`|s.re - 1/2| ≤ q_n`.

Once both `s.re` and `1/2` belong to every shrinking nested interval, `DkMath.Analysis.DkReal` uniqueness machinery should force

`s.re = 1/2`.

This route deliberately avoids any need to solve the imaginary zero ordinate algebraically.

## 5. CFBRC-compatible finite certificate

Degree two is a preferred audit target because the existing CFBRC algebra exposes the transverse square directly.

A useful finite certificate would control the centered coordinate `X = s.re - 1/2`, for example by proving a stagewise bound on `X^2` from finite prime data and then converting it to a rational interval bound.

Do not postulate an exact CFBRC zero merely to reach the existing zero-locus theorem. Derive approximation bounds first if that is what the finite arithmetic naturally provides.

## 6. Existing facts to preserve

The new route should reuse, not re-prove, the already fixed dependency spine around:

- `Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis`;
- `NontrivialRiemannZetaZero`;
- `centeredSigma`;
- `offCriticalCFBRC`;
- `cfbrcR_eq_zero_iff_x_eq_zero`;
- `offCriticalCFBRC_eq_zero_iff_re_eq_half`;
- `ZeroToCFBRCBridge`;
- `riemannHypothesis_of_standardZeta_map_zero`;
- `standardZeta_map_zero_iff_riemannHypothesis`;
- `DkMath.Analysis.DkReal` nested rational interval and semantic uniqueness results.

Every one of these must nevertheless be dependency-audited before being marked as part of the trusted final spine.

## 7. Historical route policy

Former CFZP work is retained as a fact ledger, not as a forward proof chain.

Each reused declaration must be classified individually as one of:

- exact unconditional fact;
- conditional but realizable fact;
- conditional with unproved antecedent;
- impossible under its current parent type;
- RH-equivalent frontier;
- declaration depending on `sorry` or another unresolved frontier.

No result is inherited merely because it appeared later in an old numbered chain.

## 8. Immediate sequence

### ZDI-001 — RH definition dependency audit

Trace `RiemannHypothesis` backward through the exact DkMath bridge. Audit every load-bearing `def`, theorem, hypothesis, and axiom dependency. Identify the smallest unresolved statement without introducing a new analytic route.

### ZDI-002 — DkReal common shrinking interval uniqueness interface

Expose the smallest reusable theorem saying that two real values contained in every interval of one shrinking nested rational interval representation are equal. Prefer deriving it from existing `DkReal.Semantic` results rather than rebuilding completeness.

### ZDI-003 — finite prime-certificate source audit

Return to the exact finite prime-side facts, especially pre-growth-route material, and search only for an unconditional finite bound that can constrain the centered real coordinate of a standard nontrivial zeta zero.

No asymptotic provider or new strip parameter is to be introduced before this audit identifies its exact source provenance.

## 9. Stop conditions

Stop a route immediately and record an obstruction when any of the following occurs:

- a required hypothesis contradicts a field of its parent structure;
- a purported provider is RH-equivalent;
- a new definition encodes the desired conclusion without source provenance;
- a proof step requires a theorem with unresolved `sorry` dependency;
- successive numbered modules only repackage the same unresolved proposition.

A stopped route is a successful audit result, not a reason to manufacture another assumption.

## 10. Completion criterion

This research branch closes only when there is an axiom-audited Lean term of Mathlib's exact `RiemannHypothesis`, or when the currently explored finite-certificate route is formally obstructed and the obstruction is recorded precisely.
