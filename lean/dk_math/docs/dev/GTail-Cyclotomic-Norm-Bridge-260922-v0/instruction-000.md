# GCNB-003 / instruction-000 — Extract the generic cyclotomic field Norm = GN bridge

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- DkMath/CFBRC/CyclotomicNorm.lean
- DkMath/Lib/Cosmic/GTailCyclotomic.lean
- DkMath/NumberTheory/CyclotomicQRProduct.lean
- DkMath/FLT/Kummer/CyclotomicPrincipalization.lean

## 1. Mission

The current branch has already proved the representation chain

~~~text
GTail p 1 x u
  = GTailCyclotomicShell p x u
  = GN p x u
  = cyclotomicRootProduct
~~~

for prime p, together with

~~~text
x * cyclotomicRootProduct
  = (x+u)^p - u^p
~~~

and a first complex identity using Complex.normSq.

The next task is **not** another Complex.normSq theorem.

The next task is to expose a genuine cyclotomic **field / ring-of-integers
Norm** theorem in the generic layer.

The target mathematical statement is the familiar prime cyclotomic norm:

~~~text
Norm((x+u) - u*zeta_p) = GN p x u
~~~

with the exact codomain and casts dictated by the chosen Lean carrier.

## 2. Important existing theorem: do not re-prove blindly

DkMath already contains a no-sorry specialized theorem in:

~~~text
DkMath/FLT/Kummer/CyclotomicPrincipalization.lean
~~~

named:

~~~text
chosenCyclotomicLinearFactor_norm_eq_gn_direct
~~~

Its visible signature begins with:

~~~lean
theorem chosenCyclotomicLinearFactor_norm_eq_gn_direct
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p z y : Nat} [Fact p.Prime] [IsCyclotomicExtension {p} Rat K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta p)
    ...
~~~

and it proves the integer algebraic norm of the chosen cyclotomic linear factor
equals the Nat GN value cast to Int.

Related existing helpers include at least:

~~~text
chosenCyclotomicLinearFactor_norm_eq_gn_ratCast_direct
cyclotomicEval_div_natCast_mul_pow_eq_gn
ratCast_eval_cyclotomic_eq_cyclotomicEval
Algebra.coe_norm_int
Algebra.norm_algebraMap
~~~

The exact current signatures must be audited before implementation.

### Core instruction

**Extract the reusable mathematical kernel from the FLT/Kummer-specific file
into the neutral GTail / cyclotomic / CFBRC layer.**

Do not make DkMath.CFBRC import DkMath.FLT.Kummer.

If the proof currently depends only on neutral cyclotomic and norm APIs, move
or reproduce the minimal proof in a dependency-neutral module and make the
FLT/Kummer theorem a later consumer where feasible.

If moving existing code would create a large refactor, add the neutral theorem
first and leave Kummer unchanged; prove compatibility in a test module.

## 3. Preferred carrier

First audit whether the cleanest theorem should live over:

~~~text
A. a generic K with
   [Field K] [NumberField K] [CharZero K]
   [IsCyclotomicExtension {p} Rat K]

or

B. the canonical CyclotomicField p Rat.
~~~

Prefer A if the existing proof already supports it without substantial
additional machinery.

The chosen primitive root should be explicit:

~~~text
zeta : K
hzeta : IsPrimitiveRoot zeta p
~~~

For the integral theorem, use its ring-of-integers image
hzeta.toInteger or the exact existing Mathlib/DkMath equivalent.

Do not introduce a custom cyclotomic field implementation.

## 4. Primary theorem target

Try to expose a neutral theorem with the conceptual shape:

~~~text
Algebra.norm Int (cyclotomic linear factor in O_K)
  = GN p x u
~~~

where the right side is embedded into Int.

A reasonable first API may use natural coordinates if that matches the
existing no-sorry Kummer proof most directly:

~~~lean
def cyclotomicLinearFactorInRingOfIntegers
    ...
    (x u : Nat) : O K := ...

theorem cyclotomicLinearFactor_norm_eq_GN_nat
    ...
    (x u : Nat)
    [necessary explicit hypotheses only] :
    Algebra.norm Int
      (cyclotomicLinearFactorInRingOfIntegers hzeta x u)
      =
      ((DkMath.CosmicFormulaBinom.GN p x u : Nat) : Int) := by
  ...
~~~

Here x is the gap coordinate and u is the base coordinate, so the linear
factor is mathematically

~~~text
(x + u) - zeta * u.
~~~

Names are suggestions; choose names consistent with the local namespace.

## 5. Stronger target if it is genuinely cheap

If the pinned Mathlib API makes it straightforward, also expose the field norm
version over Rat:

~~~text
Algebra.norm Rat ((x+u) - zeta*u)
  = cast(GN p x u)
~~~

and derive the integral theorem via Algebra.coe_norm_int.

Do not force this if the integral theorem is already the natural primary API.

## 6. Remove accidental positivity assumptions where justified

The existing Kummer theorem appears specialized to endpoint coordinates
z > y and y != 0 because its proof route uses:

~~~text
z - y
z / y
cyclotomic evaluation at a quotient
~~~

The new branch already removed an analogous accidental x != 0 assumption from
GTail = shell by proving the polynomial identity directly.

Audit whether the field norm theorem can similarly be stated directly in gap
coordinates x,u without:

~~~text
u != 0
x != 0
x+u > u
Nat subtraction
~~~

Prefer a direct homogeneous/cyclotomic proof if it is short and stable.

However:

**Do not manufacture stronger generality.**

If the available norm theorem fundamentally requires a nonzero base in the
current API, keep that assumption, document it, and return Outcome B with the
exact boundary.

## 7. Required connection to the current branch API

The new theorem must connect to the existing production surface in
DkMath.CFBRC.CyclotomicNorm.

At minimum, prove or test the compatibility chain:

~~~text
field/integer Norm of one chosen primitive linear factor
  = GN p x u
  = cyclotomicRootProduct zeta x u
  = GTailCyclotomicShell p x u.
~~~

Do not confuse the following objects:

~~~text
Complex.normSq
Algebra.norm Rat
Algebra.norm Int
cyclotomicRootProduct
TraceOne norm
~~~

They may be related, but each relation must be a checked theorem.

## 8. General-d warning

This checkpoint is prime-p only.

Do not state

~~~text
GTail d 1 x u = Phi_d(x+u,u)
~~~

for composite d.

For composite d the shell is the product over the nontrivial cyclotomic
divisors. Leave that to DkMath.CFBRC.CyclotomicProduct.

## 9. Dependency placement

Preferred placement order:

1. extend DkMath/CFBRC/CyclotomicNorm.lean if all imports remain neutral; or
2. create a neutral reusable module under DkMath/Lib/NumberTheory or
   DkMath/NumberTheory and have CFBRC.CyclotomicNorm import it.

Do **not** solve the task by importing:

~~~text
DkMath.FLT.Kummer.CyclotomicPrincipalization
~~~

into CFBRC or Lib.

Avoid a dependency cycle.

## 10. Tests and audits

Add focused tests under DkMathTest.

Required regressions:

~~~text
p = 3
p = 5
p = 7
~~~

The regression need only elaborate/check the generic norm theorem; it must not
invoke the final FLT3/FLT5 contradiction theorems.

Add #print axioms for every new public theorem.

Expected axiom surface should stay within the ordinary kernel/classical
foundations already used by the imported Mathlib theory. No sorryAx.

Also preserve the existing boundary regression:

~~~text
GTail d 1 0 u = GTailCyclotomicShell d 0 u.
~~~

## 11. Validation

Run at least:

~~~text
lake build DkMath.CFBRC.CyclotomicNorm
lake build <new focused DkMathTest target>
lake build DkMath.CFBRC
lake build DkMath
git diff --check
~~~

Scan changed production/test files for:

~~~text
sorry
admit
sorryAx
unsafe
axiom
~~~

Do not treat occurrences in comments/docstrings as proof failures; report the
actual scan method.

## 12. Deliverable report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-000.md
~~~

Classify the result as one of:

### Outcome A — generic field Norm bridge extracted

A dependency-neutral theorem now proves the cyclotomic field/integer norm
equals GN and is connected to cyclotomicRootProduct / shell.

### Outcome B — theorem extracted with explicit extra hypotheses

The neutral theorem is real, but the current pinned API still requires a
specific nonzero/positivity/carrier hypothesis. Record the exact hypothesis and
why it remains.

### Outcome C — existing Kummer theorem cannot yet be neutralized cleanly

No unsafe production theorem is added. Record the exact dependency/API blocker,
the smallest theorem already available, and the next bounded implementation
target.

## 13. Stop rules

Stop rather than overclaim if any of the following occurs:

- only Complex.normSq is available;
- the proof requires importing the FLT Kummer stack into a neutral module;
- field norm equality is inferred only from equal absolute values;
- equality of norms is used to infer equality of algebraic elements;
- a primitive-root product identity is silently treated as an ideal identity;
- a principal ideal p-th power is inferred from a norm p-th power;
- the proof needs a new class-group, PID, or unit theorem;
- a p=7-specific fact is required for the generic theorem.

This checkpoint is complete once the genuine Norm = GN bridge is either
extracted cleanly or its precise neutralization boundary is kernel-checked and
documented.
