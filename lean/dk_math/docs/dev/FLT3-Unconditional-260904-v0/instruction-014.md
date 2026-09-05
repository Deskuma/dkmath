# instruction-014 — Positive-Natural Normalization and Public FLT3 API

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-010 completed with Outcome A.

Checkpoint role: FLT3U-011.

## 1. Mission

PrimitiveCubicClosure.lean の kernel-checked primitive theorem

    FLT_d3_unconditional

を使い、任意の positive natural cubic solution

$$
a^3+b^3=c^3
$$

を gcd normalization により primitive solution へ縮約し、最終 endpoint

    fermatThree_no_positive_solution

を証明する。

同時に standalone public import surface

    DkMath.FLT.Three

を作る。

この checkpoint で FLT3-Unconditional roadmap の completion gate を閉じる。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/PrimitiveCubicClosure.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-013.md

normalization architecture 参考のみ:

    lean/dk_math/DkMath/FLT/Five/SignedGoldenClosure.lean

特に

    exists_counterexamplePack_of_positive_fermat5

の gcd normalization pattern は指数 3 へ特殊化してよい。

FLT5 module を production import しない。

## 3. Proposed implementation module

第一候補:

    DkMath/FLT/Three/PositiveCubicNormalization.lean

Direct import:

    import DkMath.FLT.Three.PrimitiveCubicClosure

のみを優先する。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. Primitive normalization theorem

Given

$$
a,b,c>0
$$

and

$$
a^3+b^3=c^3,
$$

define

$$
d=\gcd(a,b),
$$

$$
a'=a/d,\qquad
b'=b/d.
$$

Prove d > 0 from a > 0.

Use:

    Nat.gcd_pos_of_pos_left
    Nat.gcd_dvd_left
    Nat.gcd_dvd_right

or current equivalent APIs.

## 5. Show d divides c

Since

$$
d\mid a,\qquad d\mid b,
$$

we have

$$
d^3\mid a^3,\qquad
d^3\mid b^3.
$$

Using the Fermat equation:

$$
d^3\mid c^3.
$$

Then extract

$$
d\mid c.
$$

Preferred current API, matching the verified FLT5 normalization pattern:

    Nat.dvd_pow_iff_ceilRoot_dvd

with exponent 3.

Expected shape:

    have hd3c3 : d ^ 3 ∣ c ^ 3 := ...
    have hdc : d ∣ c := by
      have hroot :=
        (Nat.dvd_pow_iff_ceilRoot_dvd
          (a := d ^ 3) (b := c)
          (by decide : 3 ≠ 0)).mp hd3c3
      simpa using hroot

If current Mathlib simplifies this differently, use the actual API.

Do not use prime factorization manually.

## 6. Define normalized c

Set

$$
c'=c/d.
$$

Then recover exact multiplication identities:

$$
d a'=a,
$$

$$
d b'=b,
$$

$$
d c'=c.
$$

Use

    Nat.mul_div_cancel'

with the three divisibility proofs.

## 7. Positivity of normalized coordinates

Prove:

$$
a'>0,\qquad
b'>0,\qquad
c'>0.
$$

Use

    Nat.div_pos

with d > 0 and divisor bounds from divisibility.

Do not use subtraction or integer coercions here.

## 8. Coprimality

Mandatory:

$$
\gcd(a',b')=1.
$$

Use the verified current theorem:

    Nat.coprime_div_gcd_div_gcd

with d = gcd a b and d > 0.

Candidate:

    have hcop : Nat.Coprime a' b' := by
      exact Nat.coprime_div_gcd_div_gcd hdPos

Avoid reproving Bezout/gcd normalization manually.

## 9. Normalized cubic equation

Prove exactly:

$$
a'^3+b'^3=c'^3.
$$

Recommended scaled cancellation route:

$$
d^3(a'^3+b'^3)=d^3 c'^3.
$$

Derive this by rewriting with

$$
da'=a,\quad db'=b,\quad dc'=c
$$

and original equation.

Then cancel the positive factor d^3 using

    Nat.mul_left_cancel

or current exact theorem.

Lean sketch:

    have hscaled :
        d ^ 3 * (a' ^ 3 + b' ^ 3) =
          d ^ 3 * c' ^ 3 := by
      calc
        d ^ 3 * (a' ^ 3 + b' ^ 3)
            = (d * a') ^ 3 + (d * b') ^ 3 := by ring
        _ = a ^ 3 + b ^ 3 := by rw [haEq, hbEq]
        _ = c ^ 3 := hEq
        _ = (d * c') ^ 3 := by rw [hcEq]
        _ = d ^ 3 * c' ^ 3 := by ring

    have hEq' : a' ^ 3 + b' ^ 3 = c' ^ 3 := by
      exact Nat.mul_left_cancel (pow_pos hdPos 3) hscaled

Adjust theorem signature if Nat.mul_left_cancel does not take the positivity proof in the current version; follow the working FLT5 source.

## 10. Primitive normalization package theorem

Expose a reusable theorem:

    theorem exists_primitiveCubicPack_of_positive_solution
        {a b c : ℕ}
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
        (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
        ∃ a' b' c' : ℕ,
          PrimitiveCubicPack a' b' c'

This is the preferred public normalization boundary.

Construct the pack with:

- normalized positivity
- normalized coprimality
- normalized cubic equation

No relation back to original coordinates is required after this theorem, unless easy wrappers are useful for audit.

## 11. Final theorem

Mandatory final public theorem:

    theorem fermatThree_no_positive_solution
        (a b c : ℕ)
        (ha : 0 < a)
        (hb : 0 < b)
        (hc : 0 < c) :
        a ^ 3 + b ^ 3 ≠ c ^ 3 := by
      intro hEq
      rcases exists_primitiveCubicPack_of_positive_solution
          ha hb hc hEq with ⟨a', b', c', p⟩
      exact primitiveCubicPack_false p

Equivalent proof via FLT_d3_unconditional is also acceptable:

    exact FLT_d3_unconditional p.hx p.hy p.hz p.coprime_xy p.equation

But primitiveCubicPack_false is the thinner endpoint once the pack exists.

## 12. Optional theorem with implicit coordinates

If project style prefers:

    theorem fermatThree_no_positive_solution'
        {a b c : ℕ}
        (ha ...) ... :
        ...

do not add both forms unless one is genuinely needed.

The required canonical public name is:

    fermatThree_no_positive_solution

## 13. Standalone public aggregator

Create:

    DkMath/FLT/Three.lean

with:

    import DkMath.FLT.Three.PositiveCubicNormalization

and a short module docstring stating:

- this is the standalone DkMath exponent-three public surface;
- the endpoint is fermatThree_no_positive_solution;
- the proof route is GN3 / signed 3-adic routing / Eisenstein Euclidean arithmetic / unit sectors / strict descent;
- it does not use a completed FLT3 theorem as a proof step.

Do not import DkMath.FLT.Main into this aggregator.

This standalone aggregator is the mandatory public import path for the independent proof.

## 14. Top-level DkMath.FLT aggregator

Do NOT modify

    DkMath/FLT.lean

in this checkpoint unless there is a compelling repository convention requiring it.

Reason:

    DkMath.FLT

currently imports legacy

    DkMath.FLT.Main

and therefore lives in an environment where broad Mathlib FLT3 imports may already be present.

The independence-clean public surface for this project is

    DkMath.FLT.Three

until a separate legacy Main cleanup is intentionally scheduled.

Record this choice in report-014.md.

## 15. Completed-Mathlib-FLT3 import artifact caveat

Existing DkMath.Basic has broad

    import Mathlib

so generated transitive import artifacts may list

    Mathlib.NumberTheory.FLT.Three.

Do not misclassify this as theorem dependency if:

- production source does not import/use the completed theorem;
- #print axioms contains no completed FLT3 theorem;
- source search shows no reference to the completed FLT3 theorem name.

Report both facts transparently:

1. broad import artifact presence may remain;
2. proof dependency remains independent.

Do not refactor DkMath.Basic in this checkpoint.

## 16. Final dependency audit

Audit the final endpoint and standalone aggregator for absence of references to:

- DkMath.FLT.Main.FLT_d3_by_padicValNat
- hS0_not_sq
- NoSqOnS0
- DkMath.FLT.Basic
- DkMath.FLT.GEisensteinBridge
- DkMath.FLT.Five.*
- DkMath.FLT.Seven.*
- Mathlib completed FLT3 theorem names

Direct imports should remain within the independent Three tower plus generic Mathlib dependencies already inherited.

## 17. Axiom audit

Run #print axioms on at least:

    DkMath.FLT.Three.exists_primitiveCubicPack_of_positive_solution
    DkMath.FLT.Three.fermatThree_no_positive_solution

Expected acceptable inherited foundations:

    propext
    Classical.choice
    Quot.sound

Required:

- no sorryAx
- no project-specific axiom
- no completed FLT3 theorem dependency

## 18. Focused builds

Required:

    lake build DkMath.FLT.Three.PositiveCubicNormalization
    lake build DkMath.FLT.Three

If a test/import smoke module is useful, add it under DkMathTest rather than production.

## 19. Optional final theorem test

A tiny test may verify:

    #check DkMath.FLT.Three.FLT_d3_unconditional
    #check DkMath.FLT.Three.fermatThree_no_positive_solution

after importing only:

    DkMath.FLT.Three

This is recommended but not mandatory.

## 20. Required report

Create:

    report-014.md

Record:

1. gcd normalization d = gcd a b
2. proof d | c
3. normalized positive coordinates
4. normalized coprimality theorem used
5. normalized cubic equation
6. exists_primitiveCubicPack_of_positive_solution
7. fermatThree_no_positive_solution signature
8. standalone DkMath.FLT.Three aggregator
9. decision not to modify legacy top-level DkMath.FLT
10. direct imports
11. focused build results
12. axiom audit
13. completed-FLT3 source/dependency audit
14. broad DkMath.Basic import-artifact caveat
15. completion-gate checklist
16. Outcome A / B / C

## 21. Completion gate

FLT3U-011 is complete only if all hold:

1. kernel-checked primitive theorem FLT_d3_unconditional
2. kernel-checked full positive-natural theorem fermatThree_no_positive_solution
3. no hS0_not_sq assumption
4. no NoSqOnS0 assumption/provider
5. no completed FLT3 theorem used as a proof step
6. no project-specific axiom / sorry in the new tower
7. standalone public import path DkMath.FLT.Three
8. focused builds green
9. final endpoint axiom audit clean

At that point mark the entire FLT3-Unconditional roadmap completed — Outcome A.

Do not claim repository-wide removal of legacy conditional FLT3 code; this project proves a new independent endpoint alongside it.
