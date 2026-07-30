# FLT7-FUSION-004B Codex execution instructions

Date: 2026-07-30

Repository: `Deskuma/dkmath`  
Pull request: `#74`  
Base branch: `develop`  
Work branch: `wip/FLT7-fusion-004b-conjugate-fiber-260730`

Companion roadmap:

```text
lean/dk_math/DkMath/FLT/Seven/docs/
  FLT7-FUSION-004B-ULTRA-ROADMAP.md
```

Current handoff:

```text
lean/dk_math/DkMath/FLT/Seven/docs/
  FLT7-FUSION-004B-CONJUGATE-PRIME-FIBER.md
```

## 0. Execution selector

The operator must set exactly one mode before starting a run.

```text
EXECUTION_MODE = ULTRA
ACTIVE_PHASE   = U1
CURRENT_EVENT  = U1.5
STATUS         = COMPLETE
```

The operator explicitly activated ULTRA / U1. Events U1.1 through U1.5 are
complete and the expedition continues at U1.6.

Allowed values are:

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N1 | N2 | N3 | N4 | N5

EXECUTION_MODE = ULTRA
ACTIVE_PHASE   = U1
```

For the completed run, the selector was:

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N1
```

Do not enter ULTRA mode unless the operator explicitly changes the selector and
the launch conditions in the roadmap are satisfied.

## 1. Global operating rules

1. Treat the existing Lean packets and theorem statements as the source of
   truth.
2. Do not restart from the original Fermat equation.
3. Do not weaken the current real-cubic and degree-six orientation data into a
   new abstract model unless an equivalence preserving all existing facts is
   proved.
4. Do not add the desired result as a structure field, typeclass assumption,
   axiom, `sorry`, `admit`, or hidden hypothesis.
5. Preserve exact routing-cell provenance, canonical ratio addresses,
   `padicValNat` exponents, Galois phase, and quadratic orientation.
6. Reuse Mathlib and existing DkMath APIs before creating local substitutes.
7. Keep new modules narrow.  Avoid unrelated refactoring during the active
   mathematical checkpoint.
8. Every completed checkpoint must include:

   ```text
   Lean implementation
   focused build result
   facade build result when practical
   exact completion/boundary report
   checkpoint commit
   ```

9. If the predicted route fails, prove or document the exact failure and expose
   the next minimal obligation.  Do not continue by assumption.
10. The branch may contain historical reports.  Do not rewrite them to match the
    current head; create a new report for the new checkpoint.

## 2. Current Lean boundary

The active source module is centered on:

```text
DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair
```

For every canonical `CyclotomicLinearPrimeAddress`, the existing implementation
provides:

```text
p     = the real-cubic evaluation kernel
P     = a.evalKernel
Pbar  = a.conjugateEvalKernel
fiber = a.realPrimeFiberIdeal = Ideal.map ofReal p
```

with:

```text
P.IsMaximal
Pbar.IsMaximal
P != Pbar
P ⊔ Pbar = top
comap ofReal P = p
comap ofReal Pbar = p
card(Ring / P) = q
card(Ring / Pbar) = q
fiber <= P * Pbar
```

The exact exposed proposition is:

```text
ConjugatePrimeFiberProductEqualityObligation
```

and Lean already proves that it is equivalent to:

```text
P * Pbar <= fiber.
```

## 3. NORMAL mode protocol

NORMAL mode is bounded.  Complete only the selected `ACTIVE_PHASE` and stop at
its checkpoint boundary.

### NORMAL / N1 — exact conjugate-prime fibre

#### Primary target

Prove a public theorem equivalent to:

```lean
 theorem conjugatePrimeProduct_le_realPrimeFiberIdeal
    (a : CyclotomicLinearPrimeAddress p q) :
    a.evalKernel * a.conjugateEvalKernel ≤
      a.realPrimeFiberIdeal
```

and then a public equality theorem equivalent to:

```lean
 theorem realPrimeFiberIdeal_eq_conjugateProduct
    (a : CyclotomicLinearPrimeAddress p q) :
    a.realPrimeFiberIdeal =
      a.evalKernel * a.conjugateEvalKernel
```

Finally discharge the named obligation with a theorem such as:

```lean
 theorem conjugatePrimeFiberProductEqualityObligation_holds
    (a : CyclotomicLinearPrimeAddress p q) :
    a.ConjugatePrimeFiberProductEqualityObligation
```

Names may be adjusted to avoid namespace conflicts, but preserve this theorem
surface.

#### Investigation order

Inspect and attempt the following routes in this order.

##### Route N1-A — explicit split quadratic fibre

Use the explicit pair representation of
`SevenCyclotomicDegreeSixInt.Ring` and reduce the quadratic relation modulo the
common real prime.

The intended residue polynomial has the two distinct roots:

```text
ratio
ratio^-1
```

in `ZMod q`.

Try to identify the quotient by `realPrimeFiberIdeal` with the split quadratic
algebra over `ZMod q`, or directly prove that an element lying in both kernels
has real and imaginary coordinates in the common real kernel.

##### Route N1-B — combined evaluation map

Construct the ring homomorphism:

```text
x |-> (localEval x, conjugateEval x)
```

into:

```text
ZMod q × ZMod q.
```

Target facts:

```text
ker combinedEval = realPrimeFiberIdeal
ker first         = P
ker second        = Pbar
```

Then use `P ⊔ Pbar = top` and the product/intersection identity for comaximal
ideals.

##### Route N1-C — finite quotient cardinality

Use the proved inclusion:

```text
fiber <= P * Pbar
```

and prove equal finite quotient cardinality or equal finite index.

Because `P` and `Pbar` are comaximal and each quotient has cardinality `q`, the
product quotient should have cardinality `q^2`.  Independently show that the
quadratic fibre quotient has cardinality `q^2` from rank two over the real
residue field.

Use this route only with explicit finiteness and quotient equivalences; do not
rely on an informal index argument.

##### Route N1-D — componentwise membership

If quotient APIs are obstructive, prove the reverse containment directly in
coordinates.

For an element represented as:

```text
x = ofReal r + zeta * ofReal s
```

membership in both kernels gives two linear equations over `ZMod q`.  Their
difference uses the nonzero quantity:

```text
ratio - ratio^-1
```

or an equivalent distinct-root fact.  Deduce that both `r` and `s` lie in the
common real kernel, hence `x` lies in `Ideal.map ofReal p`.

#### N1 restrictions

- Do not prove that the quadratic carrier is the full ring of integers.
- Do not introduce PID or class-number machinery.
- Do not begin global load factorization in the degree-six ring.
- Do not begin primitive chart reconstruction.
- Do not refactor the completed 003F real-prime valuation modules.

#### N1 deliverables

1. theorem closing the reverse containment;
2. theorem closing exact fibre equality;
3. theorem discharging
   `ConjugatePrimeFiberProductEqualityObligation`;
4. public facade exposure;
5. report file, suggested name:

   ```text
   FLT7-FUSION-004B-CONJUGATE-PRIME-FIBER-REPORT.md
   ```

6. checkpoint commit, suggested message:

   ```text
   feat(FLT7): close exact conjugate-prime fibre
   ```

7. stop and report.  Do not automatically continue to N2.

### NORMAL / N2 — global oriented launchpad

Run N2 only after N1 is reviewed and the operator explicitly sets:

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N2
```

#### Primary target

Build the smallest stable interface connecting the completed real-cubic global
load factorization to degree-six oriented prime powers.

Target chain:

```text
real load principal ideal
  = product over q of realPrime(q)^padicValNat(q, cell)

map ofReal
  -> product over q of
       (orientedPrime(q) * conjugatePrime(q))^padicValNat(q, cell)
```

#### Expected components

- finite support reuse from the existing global load factorization;
- canonical `CyclotomicLinearPrimeAddress` for every supported prime;
- exact fibre equality from N1;
- `Ideal.map` compatibility with finite products and powers;
- pairwise comaximality or distinctness facts needed for later valuation
  ownership;
- one packet exposing the global oriented factorization without yet extracting
  element-level seventh powers.

Suggested provisional structure:

```lean
structure DegreeSixOrientedLoadFactorizationPacket ... where
  support : Finset ℕ
  realFactorization : ...
  orientedAddress : ...
  fibreEquality : ...
  mappedFactorization : ...
```

Do not force this exact structure if a theorem family is simpler.

#### N2 deliverables

- global mapped load factorization theorem or packet;
- exact statement of the next carrier-valuation frontier;
- public facade exposure;
- completion report;
- checkpoint commit;
- stop and report before ULTRA.

## 4. ULTRA mode protocol

ULTRA mode may begin only when the operator explicitly sets:

```text
EXECUTION_MODE = ULTRA
ACTIVE_PHASE   = U1
```

Before starting, read the completed N1 and N2 reports and verify that the launch
conditions in `FLT7-FUSION-004B-ULTRA-ROADMAP.md` hold.

### ULTRA mission

Explore continuously from the global oriented launchpad toward the strongest
sound result obtainable in the remaining budget:

```text
global oriented prime factorization
  -> exact oriented carrier valuations
  -> load times seventh-power ideal
  -> element-level extraction or exact obstruction
  -> primitive additive chart candidate
  -> strict decrease candidate or exact failure boundary
```

Do not ask for approval at routine intermediate choices.  Choose the strongest
sound route supported by Lean facts.

### Mandatory Ultra Events

Treat the following as checkpoint Events, not as a rigid promise that every
Event must succeed.

```text
U1.1 global oriented prime factorization
U1.2 oriented carrier valuation ownership
U1.3 seventh-power residual ideal extraction
U1.4 element-level oriented power or exact obstruction
U1.5 primitive additive chart candidate
U1.6 strict decrease candidate or exact failure boundary
```

After every completed Event:

1. make the directly affected modules build;
2. run the `DkMath.FLT.Seven` facade build when practical;
3. commit the completed Event immediately;
4. add a report containing:

   ```text
   proved facts
   theorem names
   mathematical interpretation
   exact remaining obligation
   claims explicitly not made
   next selected route
   ```

5. continue to the next Event while budget remains.

### Ultra adaptive branching rules

#### If the carrier ideal has the expected load-times-seventh-power form

Proceed to determine whether the seventh-power ideal is principal and whether
its generator can be chosen compatibly with conjugation and Galois rotation.

#### If principality is the only obstacle

Investigate, in increasing order of cost:

1. explicit coordinate construction of a generator;
2. reuse of existing real-cubic principality transported through the extension;
3. a local/global theorem special to the addressed ideals;
4. identification with the full seventh cyclotomic integer ring;
5. class number or PID machinery.

Do not start broad algebraic-number-theory development until cheaper special
routes are formally blocked.

#### If a unit-class obstruction appears

Define the exact unit quotient or residue invariant required by the oriented
factorization.  Prove the strongest criterion available.  Do not assume that a
unit is a seventh power merely because its norm or reduction is trivial.

#### If additive reconstruction fails

Formalize the missing additive compatibility as a named proposition or prove an
obstruction theorem.  Distinguish clearly between:

```text
multiplicative ideal factorization
and
actual additive Fermat-chart reconstruction.
```

#### If strict decrease fails

Expose the precise missing inequality or measure theorem.  Do not label a new
primitive chart a descent step without a strict well-founded decrease.

### Ultra prohibitions

- no hidden assumptions;
- no placeholder instances encoding the target;
- no theorem claiming FLT7 from an uninhabited provider;
- no broad cleanup while a mathematical Event is incomplete;
- no deletion or weakening of completed exact valuation/provenance theorems;
- no single giant uncommitted change spanning several completed Events.

### Ultra interruption protocol

If budget, context, or tooling stops the expedition:

1. return to the last building Event commit;
2. preserve incomplete experiments in a clearly named work file only when they
   contain reusable information;
3. write an `ULTRA-HANDOFF` report with the exact goal state and failed routes;
4. do not claim completion of the interrupted Event;
5. leave the branch ready for a NORMAL recovery checkpoint.

## 5. NORMAL recovery mode

After Ultra, the operator will select one of:

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N3
```

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N4
```

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N5
```

### N3 — stabilization

- repair elaboration and import failures;
- deduplicate accidental local helpers;
- preserve the strongest theorem statements;
- build the affected dependency cone and facade.

### N4 — publication

- expose stable packets and theorems through `DkMath.FLT.Seven`;
- finish reports and roadmap updates;
- separate completed checkpoint from the next active frontier.

### N5 — landing or split

- close the smallest remaining bridge left by Ultra; or
- create the next focused branch/PR if the new frontier is mathematically
  distinct.

## 6. Final reporting format

At the end of every run, report exactly:

```text
Execution mode:
Active phase:
Starting commit:
Ending commit:

Completed Lean facts:
- ...

New or changed modules:
- ...

Build verification:
- ...

Exact remaining obligation:
- ...

Outcome:
A | B | C | D

Next recommended execution mode and phase:
- ...
```

Do not summarize an unproved prediction as a Lean result.
