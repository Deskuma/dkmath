# Mathematical Contract

## DkMath — Cosmic Formula Inversion

This document fixes the mathematical meaning of the hackathon project before repository audit, Lean implementation, visualization, or submission work begins.

It is the authoritative boundary between:

- formally required results;
- visual interpretation;
- later research phases;
- explicitly excluded claims.

Codex must not strengthen, weaken, or reinterpret this contract without a recorded project decision.

---

## 1. Purpose of This Contract

The project begins with a finite arithmetic construction and follows it through three connected layers:

```text
finite prime escape
→ Cosmic Formula completion
→ bounded inverse projection
```

The first two layers define the minimum viable formal result.

The inverse-projection and DkReal layers are stronger milestones and may be reduced or postponed if they expose a genuine obstruction.

The contract separates the layers so that failure to complete a later phase does not invalidate the verified finite theorem.

---

## 2. Mathematical Domains

The project uses several domains.

```text
Natural numbers:
  finite prime products
  divisibility
  gcd
  factorization
  concrete demo values

Integers:
  subtraction-sensitive formulations where Nat truncation is undesirable

Rational numbers:
  exact normalized projection
  finite interval bounds
  computable demo values

Real numbers:
  bounded interval interpretation
  continuity or limiting statements when required

DkReal:
  nested rational interval representation
  reconstruction or uniqueness of a macro-scale candidate
```

The finite-prime theorem should be proved in the weakest practical domain, preferably `ℕ`.

Projection statements should begin over `ℚ` whenever possible.

Real or DkReal machinery must not be introduced merely for presentation if a rational theorem already closes the formal obligation.

---

## 3. Core Finite Data

Let `S` be a finite set of natural numbers.

The intended primary representation is:

```lean
S : Finset ℕ
```

Assume every member of `S` is prime:

$$
\forall p\in S,\ \operatorname{Prime}(p)
$$

Define the product of the finite prime universe:

$$
P:=\prod_{p\in S}p
$$

Choose an offset:

$$
u\in\mathbb N
$$

with:

$$
0<u
$$

and:

$$
\gcd(P,u)=1
$$

The completed boundary value is:

$$
B:=P+u
$$

For prime-divisor existence, assume:

$$
1<B
$$

The names `P`, `u`, and `B` should remain stable across the formal proof, documentation, visualization, and final demo.

---

## 4. Finite Prime Escape Theorem

### 4.1. Main Statement

Let `q` be prime.

If:

$$
q\mid P+u
$$

then:

$$
q\notin S
$$

provided:

$$
\gcd(P,u)=1
$$

and:

$$
P=\prod_{p\in S}p
$$

with every member of `S` prime.

The intended theorem meaning is:

> A prime divisor of the completed boundary `P + u` cannot be one of the primes used to construct `P`.

---

## 5. Proof Kernel of Finite Prime Escape

The proof must use only standard arithmetic facts.

Assume for contradiction:

$$
q\in S
$$

Then, because `q` is one of the factors of `P`:

$$
q\mid P
$$

Since also:

$$
q\mid P+u
$$

it follows that:

$$
q\mid(P+u)-P
$$

hence:

$$
q\mid u
$$

Therefore:

$$
q\mid\gcd(P,u)
$$

But:

$$
\gcd(P,u)=1
$$

so a prime `q` cannot divide the gcd.

This contradiction proves:

$$
q\notin S
$$

The Lean implementation may use an equivalent gcd, subtraction, congruence, or divisibility argument.

The mathematical meaning must remain this one.

---

## 6. Strong and Weak Theorem Surfaces

The project should distinguish several theorem strengths.

### 6.1. Divisor Exclusion

The weakest useful form does not require `q` to be prime.

```lean
q ∈ S
→ q ∣ P
→ q ∣ P + u
→ q ∣ u
```

This is a reusable local lemma.

### 6.2. Prime-Member Exclusion

```lean
Nat.Prime q
→ q ∣ P + u
→ q ∉ S
```

under the finite-prime and coprimality assumptions.

This is the central general theorem.

### 6.3. Existence of a Fresh Prime Factor

If:

$$
1<P+u
$$

then a prime divisor of `P + u` exists.

Combining prime-divisor existence with prime-member exclusion yields:

$$
\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

This is the preferred public theorem for the first demonstration.

### 6.4. All Prime Divisors Are Fresh

A stronger universal statement is also valid:

$$
\forall q,\ \operatorname{Prime}(q)\land q\mid P+u\Longrightarrow q\notin S
$$

This theorem is useful because the concrete example has two fresh factors, `13` and `17`.

### 6.5. No Claim of Uniqueness

The theorem does not claim that there is exactly one fresh prime factor.

The boundary may contain:

- one prime factor;
- multiple distinct prime factors;
- repeated powers of a fresh prime.

---

## 7. Preferred Lean Theorem Shapes

Exact names may change after the repository audit.

The intended theorem surface is approximately:

```lean
theorem prime_mem_dvd_product
    {S : Finset ℕ} {q : ℕ}
    (hqS : q ∈ S) :
    q ∣ ∏ p ∈ S, p
```

```lean
theorem not_mem_of_prime_dvd_product_add_coprime
    {S : Finset ℕ} {u q : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hu : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

```lean
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hu : Nat.Coprime (∏ p ∈ S, p) u)
    (hgt : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, Nat.Prime q ∧ q ∣ (∏ p ∈ S, p) + u ∧ q ∉ S
```

If existing DkMath theorems already provide these statements, the hackathon layer should expose thin wrappers rather than reprove them independently.

---

## 8. Fresh Prime Terminology

The preferred project term is:

```text
fresh prime factor
```

Meaning:

> A prime divisor of `P + u` that is not a member of the original finite prime set `S`.

A possible internal predicate is:

```lean
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

This predicate should only be introduced if no equivalent existing DkMath predicate already exists.

### 8.1. Primitive Prime Divisor Is Different

The project must not casually replace `fresh prime factor` with `primitive prime divisor`.

A primitive prime divisor is normally relative to a sequence or indexed family and requires non-divisibility at specified earlier stages.

The finite prime escape theorem only compares a divisor of `P + u` with the finite set used to build `P`.

Therefore:

```text
fresh:
  relative to the original finite set S

primitive:
  relative to an ordered sequence or earlier stages
```

The first hackathon theorem is about freshness, not sequence-relative primitiveness.

---

## 9. Cosmic Formula Completion

Define:

$$
\mathrm{Big}(P,u):=(P+u)^2
$$

$$
\mathrm{Gap}(u):=u^2
$$

$$
\mathrm{Body}(P,u):=P(P+2u)
$$

The core identity is:

$$
P(P+2u)+u^2=(P+u)^2
$$

Equivalently:

$$
\mathrm{Body}(P,u)+\mathrm{Gap}(u)=\mathrm{Big}(P,u)
$$

This identity follows by ring normalization:

$$
P^2+2Pu+u^2=P^2+2Pu+u^2
$$

The Lean proof should reuse an existing Cosmic Formula theorem if possible.

If no exact theorem exists, a thin wrapper proved by `ring` or `ring_nf` is acceptable.

---

## 10. Interpretation of the Cosmic Formula

The formal theorem is an algebraic identity.

The project visualizes it as a square-completion process.

```text
Body:
  a rectangle with side lengths P and P + 2u

Gap:
  a square with side length u

Big:
  a completed square with side length P + u
```

The area relation is exact:

$$
P(P+2u)+u^2=(P+u)^2
$$

The visualization may rearrange the Body into a gnomon around the Gap or use an equivalent square-completion layout.

The visual arrangement must preserve total area.

---

## 11. Arithmetic and Geometry Must Remain Distinct

The project connects two facts:

```text
Arithmetic:
  prime factors of P + u lie outside S

Geometry:
  P(P + 2u) + u² completes the square (P + u)²
```

The geometry does not prove the prime-divisor theorem by itself.

The prime-divisor theorem does not establish a Euclidean area theorem by itself.

The formal bridge is that both use the same boundary value:

$$
P+u
$$

The project narrative may say:

> The completed geometric boundary carries an arithmetic value whose prime factors escape the original finite prime universe.

It must not say:

> The missing square geometrically creates prime numbers.

The former is a verified structural connection.

The latter would overstate the theorem.

---

## 12. Finite Prime Universe

The phrase:

```text
finite prime universe
```

is project terminology.

It refers to the finite arithmetic environment determined by:

- a finite prime set `S`;
- its product `P`;
- divisibility by members of `S`;
- residue information modulo `P`;
- quantities constructed from `P`.

It does not replace standard mathematical objects such as:

- a ring;
- a field;
- a residue class ring;
- a localization;
- a formal arithmetic universe.

When a standard object is intended, the standard name must be used.

---

## 13. Special Case `u = 1`

The classical finite-prime escape construction appears when:

$$
u=1
$$

Then:

$$
\gcd(P,1)=1
$$

automatically, and every prime divisor of:

$$
P+1
$$

lies outside `S`.

The Cosmic Formula becomes:

$$
P(P+2)+1=(P+1)^2
$$

The hackathon project uses general `u` because the general offset:

- exposes the role of coprimality;
- gives a visible nontrivial Gap `u²`;
- supports the concrete example `u = 11`;
- connects more directly to the broader DkMath program.

The general theorem should not be weakened to `u = 1` unless the repository audit exposes a severe implementation obstruction.

---

## 14. Empty Prime Set Boundary

If:

$$
S=\varnothing
$$

then:

$$
P=1
$$

under the standard empty-product convention.

The general theorem may remain valid, but this is not the intended demonstration.

The main public theorem may assume:

$$
S.\operatorname{Nonempty}
$$

if that improves meaning or avoids unhelpful edge cases.

However, a nonempty hypothesis must not be added merely because it feels natural.

Codex should determine whether it is mathematically or API-wise necessary.

---

## 15. Offset Conditions

The intended offset conditions are:

$$
0<u
$$

$$
\gcd(P,u)=1
$$

The positivity assumption supports:

- a nonzero visible Gap;
- monotonicity of the boundary;
- the intended geometric interpretation.

For the pure divisor-exclusion theorem, positivity may not be necessary.

The theorem surface may therefore separate:

```text
arithmetic theorem:
  Coprime P u is the essential condition

visual theorem:
  0 < u is required for the intended positive geometry
```

The report must identify which hypotheses are logically used and which belong only to the public demonstration.

---

## 16. Boundary Size Condition

Prime-divisor existence requires:

$$
1<P+u
$$

The exclusion theorem for an already supplied prime divisor does not require this condition.

Therefore the theorem layers should remain separate.

```text
given-divisor theorem:
  assumes q is prime and q divides P + u

existence theorem:
  additionally assumes 1 < P + u
```

The implementation must not add an unnecessary size hypothesis to every local lemma.

---

## 17. Concrete Demo Contract

The fixed demonstration data is:

```lean
def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}
```

```lean
def demoP : ℕ := 210
```

```lean
def demoU : ℕ := 11
```

```lean
def demoBoundary : ℕ := 221
```

The required numerical facts are:

$$
2\cdot3\cdot5\cdot7=210
$$

$$
\gcd(210,11)=1
$$

$$
210+11=221
$$

$$
221=13\cdot17
$$

$$
13\notin\{2,3,5,7\}
$$

$$
17\notin\{2,3,5,7\}
$$

$$
210\cdot232+11^2=221^2
$$

$$
48720+121=48841
$$

All numerical statements should be proved by Lean, preferably with `norm_num`, `decide`, or existing arithmetic lemmas.

---

## 18. Concrete Demo Theorem Surface

The final demo module should expose compact theorems similar to:

```lean
theorem demo_product :
    ∏ p ∈ demoPrimeSet, p = 210
```

```lean
theorem demo_coprime :
    Nat.Coprime 210 11
```

```lean
theorem demo_boundary :
    210 + 11 = 221
```

```lean
theorem demo_factorization :
    221 = 13 * 17
```

```lean
theorem demo_thirteen_fresh :
    FreshPrimeFactor demoPrimeSet 221 13
```

```lean
theorem demo_seventeen_fresh :
    FreshPrimeFactor demoPrimeSet 221 17
```

```lean
theorem demo_cosmic_completion :
    210 * (210 + 2 * 11) + 11 ^ 2 = (210 + 11) ^ 2
```

A final end-to-end theorem may bundle the result:

```lean
theorem demo_complete :
    Nat.Coprime 210 11 ∧
    221 = 13 * 17 ∧
    13 ∉ demoPrimeSet ∧
    17 ∉ demoPrimeSet ∧
    210 * 232 + 11 ^ 2 = 221 ^ 2
```

The exact bundling should remain lightweight and readable.

---

## 19. No Novelty Claim for the Finite Escape Lemma

The underlying finite prime-factor argument is elementary and classical.

The project must not claim that the following is a new mathematical discovery:

$$
q\mid P+u\land\gcd(P,u)=1\Longrightarrow q\notin S
$$

The project contribution lies in:

- connecting the theorem to the existing DkMath library;
- exposing it through a formal public facade;
- integrating it with the Cosmic Formula;
- extending it toward inverse projection;
- demonstrating a controlled AI-to-Lean workflow;
- presenting the verified structure visually.

---

## 20. First Projection Candidate

The initial normalized boundary projection is:

$$
\pi(P,u):=\frac{P}{P+u}
$$

For:

$$
0<P
$$

and:

$$
0<u
$$

we have:

$$
0<\frac{P}{P+u}<1
$$

The complementary normalized Gap coordinate is:

$$
\gamma(P,u):=\frac{u}{P+u}
$$

Then:

$$
\pi(P,u)+\gamma(P,u)=1
$$

The signed inverse-projection coordinate may instead be:

$$
\Pi(P,u):=-\frac{P}{P+u}
$$

with:

$$
-1<\Pi(P,u)<0
$$

and:

$$
\Pi(P,u)+1=\frac{u}{P+u}
$$

The final projection definition must be chosen in `DECISIONS.md` after repository audit.

Codex must not implement competing projection conventions simultaneously.

---

## 21. Normalized Cosmic Formula

Dividing the square-completion identity by `(P + u)²` gives:

$$
\frac{P(P+2u)}{(P+u)^2}+\frac{u^2}{(P+u)^2}=1
$$

Define:

$$
\mathrm{NormalizedBody}(P,u):=\frac{P(P+2u)}{(P+u)^2}
$$

$$
\mathrm{NormalizedGap}(P,u):=\frac{u^2}{(P+u)^2}
$$

Then:

$$
\mathrm{NormalizedBody}(P,u)+\mathrm{NormalizedGap}(P,u)=1
$$

Since:

$$
\frac{u^2}{(P+u)^2}=\left(\frac{u}{P+u}\right)^2
$$

the normalized Gap is the square of the linear Gap coordinate.

This distinction must remain explicit.

```text
linear Gap coordinate:
  u / (P + u)

square Gap mass:
  u² / (P + u)²
```

They are related but not identical.

---

## 22. Inverse Formula

For the unsigned normalized coordinate:

$$
x=\frac{P}{P+u}
$$

with fixed positive `u`, solve for `P`:

$$
P=\frac{ux}{1-x}
$$

For the signed coordinate:

$$
x=-\frac{P}{P+u}
$$

solve:

$$
P=-\frac{ux}{1+x}
$$

These are exact rational or real identities on the appropriate domains.

The inverse-projection phase should prove:

- the forward map lands in the intended interval;
- the denominator is nonzero;
- the inverse formula reconstructs `P`;
- the forward map is injective for fixed positive `u`;
- the inverse is unique on the chosen domain.

---

## 23. Projection Domain Boundaries

For the unsigned projection:

$$
x=\frac{P}{P+u}
$$

the intended domain is:

$$
P\ge0
$$

$$
u>0
$$

and the image lies in:

$$
0\le x<1
$$

For the signed projection:

$$
x=-\frac{P}{P+u}
$$

the image lies in:

$$
-1<x\le0
$$

The endpoint corresponding to unbounded `P` is approached but not attained for finite `P`.

Therefore:

```text
finite P:
  interior point

P → ∞:
  limiting boundary
```

No theorem should claim that a finite natural number maps exactly to the infinite-limit endpoint.

---

## 24. DkReal Reconstruction Contract

The stronger reconstruction phase seeks to represent a projected value by nested rational intervals.

Let:

$$
I_n=[a_n,b_n]
$$

be rational intervals satisfying:

$$
I_{n+1}\subseteq I_n
$$

and:

$$
b_n-a_n\longrightarrow0
$$

The intended projected value lies in every interval.

After applying the inverse scaling map, obtain integer-scale intervals:

$$
J_n=f_u^{-1}(I_n)
$$

The reconstruction goal is to prove that eventually the interval contains at most one natural-number candidate.

A standard sufficient condition is:

$$
\operatorname{width}(J_n)<1
$$

Then two distinct integers cannot both lie in `J_n`.

The DkReal phase should connect this uniqueness principle to existing DkReal APIs rather than build a parallel interval theory.

---

## 25. Reconstruction Is a Stronger Milestone

The minimum viable project does not require the complete DkReal reconstruction theorem.

The milestone hierarchy is:

```text
Required:
  finite prime escape
  Cosmic Formula completion
  concrete Lean demo

Preferred:
  rational bounded projection
  exact inverse identity

Stretch:
  DkReal nested intervals
  unique macro-integer reconstruction
```

If DkReal reconstruction exposes a genuine missing theorem, Codex must stop and report the smallest missing bridge.

The finite verified demo remains complete without the stretch milestone.

---

## 26. Visual Contract

The visual layer may display:

- a finite collection of prime-labelled components;
- their fusion into `P`;
- the Body region;
- the missing Gap square;
- completion into a square;
- the boundary value `P + u`;
- factorization of the boundary;
- fresh factors highlighted outside the original set;
- the corresponding Lean theorem.

The visual layer must not display as verified fact:

- an infinite prime process not formally stated;
- a geometric creation mechanism for primes;
- a general inverse theorem before it is implemented;
- DkReal uniqueness before the bridge is proved;
- cryptographic strength;
- aperiodicity;
- a solution to an open problem.

---

## 27. Separation of Formal and Interpretive Vocabulary

The following are formal or directly formalizable:

```text
finite set
prime
product
divisibility
coprime
factor
square identity
rational projection
interval
injective map
inverse map
unique integer candidate
```

The following are interpretive DkMath vocabulary:

```text
finite prime universe
fresh channel
completed boundary
Body
Gap
Big
inverse projection
macro reconstruction
```

Interpretive vocabulary may appear in comments and documentation.

Lean theorem statements should prefer mathematically standard predicates unless an established DkMath abstraction already exists.

---

## 28. Dependency Contract

The intended dependency direction is:

```text
Mathlib
  ↓
existing DkMath arithmetic and Cosmic Formula modules
  ↓
DkMath.Hackathon.FinitePrimeEscape
  ↓
DkMath.Hackathon.CosmicCompletion
  ↓
DkMath.Hackathon.Demo
```

Projection and DkReal bridges may be added later, but must not create a reverse dependency from core DkMath modules into the hackathon facade.

The hackathon layer is a public demonstration surface.

It is not a new foundational layer.

---

## 29. Reuse Contract

Before introducing any new declaration, Codex must search for existing equivalents involving:

```text
Finset product of primes
prime membership and product divisibility
coprime products
prime divisor existence
fresh prime predicates
Euclid-style finite escape
Big / Body / Gap
Cosmic Formula square completion
normalized projection
DkReal nested intervals
interval width
floor / ceil uniqueness
integer candidate uniqueness
```

Every proposed new declaration must be classified as:

```text
reuse existing declaration directly
thin wrapper
specialized corollary
genuinely missing lemma
demo-only numerical theorem
```

A parallel abstraction is prohibited unless the audit establishes that no suitable existing structure exists.

---

## 30. Proof-Strength Contract

Codex must prove the theorem actually requested.

It must not silently substitute:

- a numerical example for a general theorem;
- an existence theorem for a universal theorem;
- a classical choice object for a computable witness when computability is required;
- a rational theorem for a natural-number divisibility theorem;
- a visual identity for a set-theoretic area decomposition;
- a nonempty result for uniqueness;
- an asymptotic statement for an exact finite theorem.

Conversely, Codex must not overgeneralize a small required theorem if doing so materially increases implementation cost.

---

## 31. Acceptable Classical Reasoning

Classical reasoning may be used when it simplifies finite existence proofs, provided:

- the theorem does not claim computable extraction;
- the use of classical choice is documented;
- a constructive witness is not required by the demo.

For the concrete example, explicit factors `13` and `17` should be used rather than classical extraction.

For the general fresh-prime theorem, existing prime-divisor existence APIs may use classical reasoning internally.

---

## 32. Verification Gates

A formal claim enters the public project surface only after:

```text
focused module build passes
hackathon aggregate build passes
relevant DkMath build passes
new file contains no sorry or admit
git diff --check passes
the theorem statement matches this contract
```

The user-provided checkpoint is treated as build-verified when the report states that the relevant gates passed.

Review effort should focus on theorem meaning, dependency direction, API quality, and the next mathematical obstruction.

---

## 33. Required Reports

Each implementation report must state:

```text
What was proved
Which declarations were added
Which existing APIs were reused
Which hypotheses were actually necessary
Which visual interpretations are now justified
Which stronger claims remain unproved
What genuine obstruction stopped further work
What the smallest next theorem is
```

A report must not use phrases such as:

```text
the inversion is complete
the universe has no holes
the fresh factor is unique
the visual geometry proves the arithmetic
```

unless exact formal theorems with those meanings have been implemented.

---

## 34. Minimum Viable Mathematical Completion

The first mathematical milestone is complete when Lean proves all of the following.

### General arithmetic theorem

$$
\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

under the finite-prime, coprimality, and boundary-size assumptions.

### General Cosmic Formula theorem

$$
P(P+2u)+u^2=(P+u)^2
$$

### Concrete factor theorem

$$
221=13\cdot17
$$

### Concrete freshness theorems

$$
13\notin\{2,3,5,7\}
$$

$$
17\notin\{2,3,5,7\}
$$

### Concrete completion theorem

$$
210\cdot232+11^2=221^2
$$

The demo must expose these through a compact import surface.

---

## 35. Strong Mathematical Completion

The stronger milestone is complete when the project additionally proves:

- a chosen normalized projection into a bounded interval;
- an exact inverse formula;
- injectivity for fixed positive `u`;
- a normalized Body/Gap conservation theorem;
- a DkReal or rational interval reconstruction theorem;
- uniqueness of the recovered integer candidate under width `< 1`.

Each item is independent enough to be stopped and reported separately.

---

## 36. Explicit Non-Claims

This contract does not assert:

- a new proof of the infinitude of primes;
- a novel Euclid theorem;
- a primitive prime divisor theorem;
- that every `P + u` is prime;
- that every `P + u` has multiple fresh prime factors;
- that fresh factors are unique;
- that square completion causes factorization;
- that the geometry explains the distribution of primes;
- that the inverse projection solves an open problem;
- that DkReal reconstructs every arithmetic object;
- that the project provides cryptographic security;
- that the project proves Collatz convergence;
- that the project proves any currently open conjecture.

---

## 37. Contract Change Procedure

Any mathematical change must be recorded before implementation.

A change record must include:

```text
Decision identifier
Old statement
New statement
Reason
Affected files
Affected visual scenes
Affected Lean theorems
Whether the change strengthens or weakens the project
```

Codex may propose a contract change.

Codex may not apply it without review.

---

## 38. Final Contract Summary

The first verified path is:

$$
P=\prod_{p\in S}p
$$

$$
\gcd(P,u)=1
$$

$$
1<P+u
$$

$$
\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

and:

$$
P(P+2u)+u^2=(P+u)^2
$$

The fixed demo is:

$$
S=\{2,3,5,7\}
$$

$$
P=210
$$

$$
u=11
$$

$$
P+u=221=13\cdot17
$$

$$
210\cdot232+11^2=221^2
$$

The formal theorem is finite prime escape.

The visual structure is Cosmic Formula completion.

The stronger research direction is bounded inverse projection and verified reconstruction.

All implementation, documentation, and visualization must preserve these distinctions.
