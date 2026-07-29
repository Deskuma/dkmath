# M1-001 Report: Theorem and API Reconnaissance

Date: 2026-07-25  
Outcome: **B — fixed exponent five is immediate; odd-prime generalization needs one bridge layer**

## 1. Decision

The campaign will proceed in this order:

```text
M1-002  exponent-five local divisibility / no-lift theorem
M1-003  exponent-five exceptional excess = 0
M1-004  GN-to-geometric-sum bridge and odd-prime generalization
M1-005  odd-prime exceptional excess = 0 and zero budget
```

The general odd-prime theorem remains credible and has a strong Mathlib endpoint, but it should not block the exact exponent-five victory.

## 2. Existing DkMath findings

### 2.1. GN owner and explicit sum

`GN` is the `r = 1` specialization of canonical `GTail` and is exposed in:

```text
DkMath/CosmicFormula/CosmicFormulaBinom.lean
```

Relevant declarations:

```lean
DkMath.CosmicFormulaBinom.GN
DkMath.CosmicFormulaBinom.GN_eq_sum
DkMath.CosmicFormulaBinom.cosmic_id_csr'
DkMath.CosmicFormulaBinom.add_pow_gap_factor
```

The explicit sum is:

$$GN_d(x,u)=\sum_{k<d}\binom d{k+1}x^ku^{d-1-k}$$

Therefore `d = 5` can be expanded locally without importing the FLT5 tower.

### 2.2. ABC power-difference split

Existing:

```lean
Triple.powerDiff_eq_boundary_mul_GN
Triple.padic_powerDiff_eq_boundary_add_GN
```

The exact factorization is already available:

$$T.c^n-T.b^n=T.a\,GN_n(T.a,T.b)$$

No new ABC lift definition is required.

### 2.3. Exceptional support definition

Existing:

```lean
GNExceptionalValuationExcess
```

It is exactly a filtered sum over:

```text
q ∈ factorization.support (GN n a b)
q ∣ n
```

For `n = 5`, every such support prime is `q = 5`.

### 2.4. Factorization and padicValNat bridge

Mathlib defines:

```lean
Nat.factorization n p :=
  if p.Prime then padicValNat p n else 0
```

and exposes:

```lean
Nat.factorization_def
```

Thus, for prime `p`, a theorem

```lean
padicValNat p m = 1
```

rewrites directly to:

```lean
m.factorization p = 1
```

No new foundational equality theorem is required.

Useful existing DkMath wrappers:

```lean
padicValNat_eq_zero_iff
Vp_ge_one_iff
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
```

## 3. Exponent-five route

The `GN_eq_sum` specialization gives:

$$GN_5(a,b)=a^4+5a^3b+10a^2b^2+10ab^3+5b^4$$

This yields two local congruences.

### Modulo five

$$GN_5(a,b)\equiv a^4\pmod5$$

Therefore:

$$5\mid GN_5(a,b)\Longrightarrow5\mid a$$

### Modulo twenty-five

If `5 ∣ a`, the first four terms are divisible by `25`, hence:

$$GN_5(a,b)\equiv5b^4\pmod{25}$$

If `Coprime a b`, then `5 ∤ b`, so:

$$25\nmid GN_5(a,b)$$

Combined with `5 ∣ GN₅`, this gives:

$$v_5(GN_5(a,b))=1$$

This route is finite, elementary, and independent of FLT5 final theorems.

## 4. General odd-prime route

Mathlib provides a highly relevant theorem in:

```text
Mathlib/NumberTheory/Multiplicity.lean
```

Core declaration:

```lean
emultiplicity_geom_sum₂_eq_one
```

Conceptually, for odd prime `p`, if

```text
p ∣ x - y
p ∤ x
```

then the geometric quotient

$$\sum_{i<p}x^iy^{p-1-i}$$

has exact `p`-multiplicity one.

The same file also exposes odd-prime LTE variants:

```lean
Int.emultiplicity_pow_sub_pow
Nat.emultiplicity_pow_sub_pow
```

For ABC coordinates choose:

```text
x = T.a + T.b = T.c
y = T.b
x - y = T.a
```

The remaining bridge obligations are:

```text
A. identify GN p T.a T.b with the geometric quotient
B. transfer emultiplicity = 1 to padicValNat / factorization = 1
C. manage Nat subtraction or use an Int cast cleanly
```

These are local and plausible, but not needed for the fixed-five checkpoint.

## 5. Selected implementation ownership

Initial module:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

The first checkpoint will contain exponent-five local facts only.

If the general `GN = geom_sum₂` theorem is useful beyond ABC, M1-004 may move that bridge into a neutral owner such as:

```text
DkMath/NumberTheory/GN/OddPrimeExceptional.lean
```

No production dependency from `DkMath.ABC` to `DkMath.FLT.Five` will be introduced.

## 6. M1-002 theorem surface

Recommended local theorem chain:

```lean
GN_five_eq_explicit
five_dvd_boundary_of_dvd_GN_five
not_twentyFive_dvd_GN_five_of_coprime
padicValNat_five_GN_five_eq_one_of_dvd
factorization_five_GN_five_eq_one_of_mem_support
```

M1-002 stops after the local multiplicity-one theorem and focused build.

M1-003 alone will unfold and close `GNExceptionalValuationExcess`.

## 7. Rejected routes

### Import FLT5 GN5 implementation into ABC

Rejected because it reverses the desired dependency direction.

```text
ABC -> FLT.Five
```

would make a general ABC arithmetic layer depend on a problem-specific proof tower.

### Start with full odd-prime LTE composition

Deferred, not rejected. The mathematical endpoint exists, but the bridge overhead is larger than the complete exponent-five proof.

### Prove general squarefreeness

Rejected. M1 only needs the unique exponent-exceptional channel to have multiplicity one. It says nothing about non-exceptional repeated primes.

## 8. Confidence assessment

```text
M1-002 fixed-five local kernel        high confidence
M1-003 fixed-five excess zero         high confidence
M1-004 odd-prime generalization       medium-high confidence
M1-005 general zero budget            high after M1-004
```

## 9. Next checkpoint

Proceed with:

```text
instruction-M1-002.md
```

The next implementation must remain small:

```text
one new module
fixed exponent five only
local divisibility / no-lift / valuation-one
focused build
report
```

Do not close the exceptional finite sum until M1-003.