# FLT7 Astra-001 findings freeze and generalization split

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative research source:
- astra-report-001.md
- astra-001/OrbitChecks.lean
- astra-001/orbit_experiments.py

This note freezes the interpretation of Astra-001 before productionization.

## 1. What Astra-001 actually established

Kernel-checked scratch facts include:

- the order-three action of rotateEquiv on the projective unit log;
- all three real-cubic orbit edges and their unit classes;
- pairwise coprimality of the orbit roots;
- common-prime localization for the root gap and homogeneous seventh quotient;
- exact theta depth 3 for the homogeneous quotient;
- theta^32 divisibility of the first root gap;
- norm identities needed by the height argument;
- the two real inequalities used in the smaller-norm calculation.

Mathematical deductions, not yet fully productionized, include:

- exact root-gap theta depth 32 + 42*k for A = 7^k*a;
- theta-stripped coprime factor extraction;
- associated seventh-power roots of the two stripped factors;
- the exact extracted unit classes;
- the strict positive norm reduction

      0 < abs(Norm(g)) < a <= A.

This is NOT yet a complete descent because no successor primitive arithmetic
state has been constructed from g.

## 2. Routes now considered exhausted or rejected

The following are not to be reopened without new input:

- the R16 mod-49 endpoint gate: it is equivalent to the existing sixth-root
  condition for units;
- contradiction from a single nonzero orbit unit class;
- contradiction from the sum/product of the three edge unit classes;
- trace-zero plus the predicted gap-core class;
- higher theta precision alone;
- inference of element coprimality from rational norm coprimality.

The three orbit unit classes are compatible, not contradictory.

## 3. Current FLT7 frontier

The current productive route is:

    direct cyclotomic exact seventh power
      -> relative norm to the real cubic field
      -> Galois orbit edge
      -> exact theta stripping
      -> coprime seventh-power extraction
      -> strictly smaller positive integer norm.

The precise conceptual gap after productionizing the smaller norm is:

    extracted smaller real-cubic root
      -> successor primitive arithmetic state.

A future descent claim must construct the successor state and prove a strict
well-founded decrease. The smaller norm alone is not a descent theorem.

## 4. Generalization ownership audit

### 4.1 Already generic; do not duplicate

The repository already owns reusable power extraction under:

- DkMath.Lib.NumberTheory.PowerFactor
- DkMath.Lib.NumberTheory.IdealPowerFactor
- DkMath.Lib.NumberTheory.PrincipalIdealPower

In particular, coprime product -> associated p-th power and principal ideal
power -> element/unit*p-th-power are already neutral kernels.

Astra-001 consumers should reuse these rather than create FLT7 copies.

### 4.2 Immediate new Lib candidate: homogeneous power quotient support

Astra-001 used the p=7 identity embodied by

    gap_dvd_seventhQuotient_sub_seven_mul_pow_six.

The reusable content is exponent-independent.

For a homogeneous quotient

    H_n(x,y) = sum_{i=0}^{n-1} x^(n-1-i) y^i,

the generic congruence is

    H_n(x,y) ≡ n*y^(n-1) mod (x-y).

Consequently, if a prime element divides both x-y and H_n(x,y), and does not
divide y, then it must divide the scalar n.

This is a genuine reusable common-prime localization kernel and belongs under
DkMath.Lib.NumberTheory, subject to choosing the weakest clean algebraic
hypotheses.

This is the highest-priority generalization extracted from Astra-001.

### 4.3 Generalization candidate after stabilization: homogeneous quotient lower bound

Astra-001 used, for p=7 and nonnegative reals,

    H_7(s,t) >= 7*(s*t)^3.

The mathematical pattern is the odd-prime/odd-exponent AM-GM inequality

    H_p(s,t) >= p*(s*t)^((p-1)/2).

This is potentially reusable in FLT/ABC height arguments, but a fully generic
Lean proof may cost more than its immediate benefit. Do not block FLT7
productionization on this abstraction.

First keep the p=7 inequality in the FLT7 production module. Promote a generic
version only after the direct smaller-norm theorem is stable.

### 4.4 Keep p=7-specific for now

Do NOT promote yet:

- the projectiveLog rotation matrix [[4,0],[1,2]];
- the edge classes (0,5), (0,3), (0,6);
- theta depth 3 for the seventh quotient;
- root-gap depth 32+42*k;
- thetaSevenUnit / orbitUnit01 formulas;
- the p=7 height constants 35,42,64;
- the successor-state reconstruction problem.

These depend materially on the real cubic subfield of Q(zeta_7), the chosen
ramified axis, or p=7-specific arithmetic.

They may later motivate a general Galois-orbit obstruction interface, but the
current repository does not yet justify that abstraction.

## 5. Implementation split

### Track F — FLT7 productionization

Productionize Astra-001's direct orbit split and strict smaller norm without
claiming descent.

Target:
- exact theta depths;
- stripped cores;
- current-provenance coprimality;
- associated seventh-power extraction with units;
- total positivity / norm compatibility;
- strict smaller positive norm.

Terminal statement should expose the smaller norm together with all witnesses
needed by a future successor constructor.

### Track G — neutral common-prime kernel

Separately extract the homogeneous quotient congruence/common-prime theorem to
DkMath.Lib.NumberTheory and calibrate it back against the p=7 theorem.

Do not move p=7 field-specific orbit code into Lib.

## 6. Research interpretation

The reusable principle visible so far is not yet a full "FLT prime exponent
descent" theorem.

What is supported is a smaller kernel:

    same-gauge difference
      + homogeneous power quotient
      + primitive/nondivisibility input
      -> common-prime support collapses to the exponent prime.

This is a precise algebraic form of the "gauge intersection" intuition:
after two factors share a common root-gap gauge, their common prime support is
forced onto the exponent/ramified axis.

The later CM phase kill and Galois orbit norm reduction are promising layers
of a broader principle, but should remain research-level until another prime
or another problem reuses the same interface.
