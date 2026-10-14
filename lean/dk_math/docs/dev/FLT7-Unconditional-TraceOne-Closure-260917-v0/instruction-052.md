# FLT7TC-005R46 — Saturation audit and closure-route selection

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This is a reconnaissance checkpoint.

Do **not** add a new production contradiction theorem unless the audit finds
an immediate theorem already justified by the current checked surface.

Authoritative current endpoints:

- `report-044.md` — C>1 common-prime Kummer branch.
- `report-050.md` — C=1 projective-root closure.
- `report-051.md` — C=1 finite-Hensel amplification.
- `PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`
- `SevenRealCubicThetaSeventhPowerDepth.lean`
- `PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean`
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean`
- `SevenRealCubicUnitClass.lean`

The current C=1 endpoint is

```text
W = rho * t^(7^9)
Phi(W) = 0
norm W = 1
projectiveLog W = (1,1)
```

with the exact paired quotient provenance retained.

The current C>1 endpoint is: for every supplied prime `q | C`, the complete
split/oriented-prime machinery yields

```text
beta^3 = 2*beta^2 + beta - 1
z != 0
z^7 = beta*(1+beta)
q % 7 = 1 or 6.
```

A single-prime Kummer contradiction is known to fail: the checked R38 scratch
contains both a nonresidue example at q=29 and a residue example at q=379.

The goal of R46 is to decide which next route has an honest closure prospect.

## Part A — prove the finite-Hensel budget is saturated

Audit the exact depth accounting behind R45.

Starting only from

```text
theta^32 | directOrbitGap p
theta^32 | Z^7 - p.rho^6
```

and the neutral theorem

```text
theta^(3*m) | x -> 7^m | x,
```

record precisely:

1. the largest usable multiple of three below 32 is 30;
2. theta^30 gives scalar depth 10;
3. the rotation-gap constant coordinate is `-7*C`, so recovering the source
   nilpotent coordinates loses one factor seven and gives depth 9;
4. the quotient seventh-power comparison therefore gives depth 9 for `Z^7`;
5. one seventh-root depth drop gives depth 8 for `Z`;
6. scalar cancellation transfers depth 8 to `v⁻¹`;
7. recursive unit extraction gives `v = t^(7^8)`;
8. the outer R41 seventh power gives `W = rho*t^(7^9)`.

Explain why **the existing theta^32 provenance alone does not justify depth 9
for v⁻¹ or exponent 7^10 for W**.

This can be a report proof rather than a Lean theorem.  If a tiny arithmetic
lemma helps the audit, scratch-only is enough.

## Part B — confirm that the old successor routes remain frozen

Re-check R25 and R27 against the R45 endpoint.

Record explicitly that:

- ordinary homogeneous restart fails because the relevant coefficient ratio
  has fixed nontrivial theta residue, independently of the high-power
  correction;
- the square restart remains blocked because `7^9` is odd and the current
  factorization does not force coefficient zero to be a square;
- the mixed-sign theorem does not become a sign contradiction merely because
  the remaining power is `7^9`.

Do not reopen those implementations unless a genuinely new implication is
found.

## Part C — derive the exact trace-plane binary cubic surface

Work from the current checked trace plane

```text
3*A - 10*B + 35*C = 0
```

for a theta-coordinate element

```text
W = A + B*theta + C*theta^2.
```

Prove in scratch, and promote only if clean and useful, the complete integer
parameterization:

```text
A = 5*(r+s)
B = 5*r - 2*s
C = r - s
```

for some integers r,s.

The converse must also be checked.

Then substitute into the actual `SevenRealCubicInt.norm` formula and
kernel-check the exact binary cubic identity.  Determine the correct sign
without guessing.  The expected polynomial, up to the sign fixed by Lean, is

```text
r^3 - 4*r^2*s - 11*r*s^2 + 43*s^3.
```

Record the exact equation corresponding to

```text
norm W = 1.
```

Also calibrate the known unit

```text
rho = -alpha^3
```

on this parameterization.  The expected pair is

```text
(r,s) = (-3,-1).
```

Kernel-check the pair and the binary-cubic value.

## Part D — translate the projective class onto the binary cubic surface

Using only checked definitions of

```text
thetaConstModSeven
thetaLinearModSeven
thetaSquareModSeven
unitNilpotentX
unitNilpotentY
projectiveLog
```

derive the strongest simple congruence on r,s forced by

```text
projectiveLog W = (1,1).
```

A previously observed candidate is

```text
r = 3*s mod 7.
```

Do not assume it.  Kernel-check the actual congruence.

Check that the calibrated rho pair satisfies the resulting congruence.

If additional independent congruences follow at modulus 7 or 49, record them.

## Part E — audit whether the Thue route is actually formalizable

Search the current repository and the Mathlib API available in this project for
tools that can prove **completeness** of solutions to this specific binary
cubic equation.

Distinguish carefully:

- evaluating a proposed solution;
- finite brute-force search under an assumed bound;
- proving a bound;
- proving a complete Thue solution classification.

Do not treat a finite Python/Sage/PARI experiment as a proof.

If useful, a scratch computation may list small solutions as heuristic
evidence, but the report must label it non-authoritative unless Lean proves
completeness.

The audit must answer:

1. Is there already a Mathlib theorem reducing this exact cubic to a finite
   certified search?
2. Is there a usable generic Thue theorem with effective bounds?
3. Would proving completeness require substantial new Diophantine
   approximation / Baker / regulator machinery?
4. Does the extra congruence from Part D materially simplify the proof?

## Part F — audit the global unit-lattice route

The current repository proves:

- unit rank two;
- the mod-seven unit-class quotient has cardinal 49;
- the projective-log map modulo seventh powers is bijective.

It does **not** currently prove that

```text
alphaUnit, alphaAddOneUnit
```

are a fundamental Z-basis of the full free unit group.

Confirm this exact boundary.

Audit what would be required to prove a theorem of the form

```text
forall u : SevenRealCubicIntˣ,
  exists eps : {+1,-1}, exists a b : Int,
    u = eps * alphaUnit^a * alphaAddOneUnit^b.
```

Do not infer this from mod-seven surjectivity.

Determine whether current Mathlib Dirichlet-unit APIs can give an abstract
basis only, or whether the explicit alpha / (1+alpha) basis can be certified
without a regulator/index computation.

Then answer whether such an exact Z^2 decomposition, **even if available**,
would by itself make

```text
Phi(rho * t^(7^9)) = 0
```

finite/easy, or merely turn it into a rank-two exponential Diophantine
equation.

## Part G — test the exact calibration endpoint

Audit whether current provenance excludes the special possibility

```text
W = rho.
```

Facts already checked for rho include:

```text
norm rho = 1
projectiveLog rho = (1,1)
Phi(rho) = 0.
```

Check every additional C=1 theorem from R39–R45 and determine whether any one
of them rules out `W = rho`.

Do not confuse “the theorem does not prove W=rho” with “W=rho is impossible.”

If no current theorem excludes the calibration value, state that clearly.
This is important: any local/unit-lattice route whose only conclusion is
`W = rho` would still need a second provenance clash.

## Part H — re-audit the C>1 branch as a global, not single-prime, problem

For `q | C`, inventory exactly what is available simultaneously for **all**
prime divisors of C:

- q divides R,S,a;
- q is different from 7;
- q splits completely in the real cubic;
- exact 1-to-2 prime-ideal allocation;
- q mod 7 is ±1;
- the oriented residue beta satisfies the cubic;
- beta(1+beta) is a seventh power.

Then investigate whether the current data can be combined across all q | C.

Search specifically for possible existing infrastructure for:

1. seventh-power residue symbols;
2. product formulas / reciprocity;
3. norm residue symbols;
4. global Kummer extensions attached to
   `alphaUnit * alphaAddOneUnit`;
5. a parity/product relation over the three primes above q;
6. a relation between the q-local condition and the exponent
   `a.factorization q`.

Do not invent a reciprocity law.  Name exact available APIs/theorems, or state
that the infrastructure is absent.

## Part I — inspect the q ≡ -1 mod 7 branch separately

R38 notes that on `q % 7 = 6` the seventh-power map on the residue field is
an automorphism, so the current Kummer condition is automatically soluble.

Confirm whether the **14th-power** origin of the condition, the 1-to-2 prime
allocation, or the two rotated nonzero roots adds any restriction that was
lost when reducing to the seventh-power beta equation.

If no extra restriction survives, state that q ≡ -1 is genuinely invisible to
the current Kummer test.

## Part J — compare closure prospects

The report must end with a ranked technical assessment of the following
routes, but do not call any route a proof unless it is one:

### Route T — trace-plane / binary cubic

Use
`Phi(W)=0`, `norm W=1`, projective congruence, and
`W=rho*t^(7^9)`.

### Route U — explicit global unit lattice

Prove an explicit fundamental-unit basis and reduce to an exponential
Diophantine equation.

### Route K — global common-prime Kummer/reciprocity

Return to `C>1` and combine the local conditions over all common primes.

### Route S — successor/descent

Revisit the smaller twisted state only if R45 supplies a genuinely new bridge.

For each route record:

- exact new theorem needed;
- whether current Mathlib/DkMath infrastructure supports it;
- expected implementation scale: small / medium / major new theory;
- whether the endpoint would actually contradict provenance or merely sharpen
  the normal form.

The purpose is to select R47 honestly.

## Hard stops

- No FLT7 contradiction claim from `W = rho*t^(7^9)` alone.
- No arbitrary/infinite Hensel continuation beyond theta^32.
- No claim that alpha and 1+alpha are fundamental units without proof.
- No finite-search result presented as a complete Thue solution without a
  certified bound/completeness theorem.
- No invented reciprocity law.
- No historical terminal contradiction imported as a shortcut.
- No production `sorry`, `sorryAx`, `admit`, `unsafe`, or project
  `axiom`.

## Deliverables

Primary deliverable:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-052.md
```

Update `ROADMAP.md` with a concise R46 saturation/route-selection entry.

Scratch Lean files are allowed for:

- trace-plane parameterization;
- norm binary cubic identity;
- projective congruence;
- calibration rho.

Do not add a production module unless one of those neutral facts is clearly
reusable and fully proved.

## Outcomes

- Outcome A — the audit finds an already-supported independent clash that
  closes either C=1 or C>1.
- Outcome B — one route has a concrete next theorem with existing
  infrastructure and a credible contradiction endpoint; recommend it for R47.
- Outcome C — the trace-plane/Thue route is structurally precise but requires
  major new completeness machinery.
- Outcome D — the C>1 global Kummer route is the best frontier but requires
  new reciprocity/Kummer infrastructure.
- Outcome E — all current routes require major new theory; record the exact
  saturated boundary and stop rather than manufacturing progress.

## Validation

For any scratch Lean added:

```text
lake env lean <scratch-file>
git diff --check
```

If any neutral production theorem is promoted, add the normal focused API and
axiom audits.

Run forbidden-source/import scans on every decisive Lean file.
