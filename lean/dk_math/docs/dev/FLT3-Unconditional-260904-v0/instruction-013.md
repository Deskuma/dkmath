# instruction-013 — Well-Founded Closure of Primitive FLT3

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-009B completed with Outcome A.

Checkpoint role: FLT3U-010.

## 1. Mission

PrimitiveCubicDescent.lean の

    exists_smaller_primitiveCubicPack

を product measure に対する strong induction へ接続し、すべての

    PrimitiveCubicPack a b c

を矛盾化する。

その結果として、DkMath.FLT.Three namespace 内に

    FLT_d3_unconditional

を production theorem として実装する。

この theorem は primitive positive hypotheses のみを取り、

    hS0_not_sq
    NoSqOnS0
    completed Mathlib FLT3 theorem

を一切要求してはならない。

Positive-natural arbitrary triple の gcd normalization は U011 に残す。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/PrimitiveCubicDescent.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-012.md

closure architecture 参考のみ:

    lean/dk_math/DkMath/FLT/Five/SignedGoldenZeroSectorDescent.lean

特に

    goldenZeroSectorDescentPacket_false

の strong-induction shape は参考にしてよい。

FLT5 module を production import しない。

## 3. Proposed module

第一候補:

    DkMath/FLT/Three/PrimitiveCubicClosure.lean

Direct import:

    import DkMath.FLT.Three.PrimitiveCubicDescent

のみを優先する。

禁止:

    DkMath.FLT.Main
    DkMath.FLT.Basic
    DkMath.FLT.Core
    DkMath.FLT.GEisensteinBridge
    DkMath.FLT.Five.*
    DkMath.FLT.Seven.*
    Mathlib.NumberTheory.FLT.Three

## 4. Core contradiction theorem

First prove:

    theorem primitiveCubicPack_false
        {a b c : ℕ}
        (p : PrimitiveCubicPack a b c) :
        False

Use strong induction on

$$
m=abc.
$$

Recommended shape:

    have noAt :
      ∀ n : ℕ,
        ∀ {a b c : ℕ},
          PrimitiveCubicPack a b c →
          a * b * c = n →
          False := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro a b c p hp
          obtain ⟨x, y, z, next, hlt⟩ :=
            exists_smaller_primitiveCubicPack p
          exact ih (x * y * z)
            (by simpa [hp] using hlt)
            next
            rfl

Exact binder order may be adjusted to Lean elaboration.

The proof must recurse only on the smaller product measure.

Do not recurse structurally on packet construction.

## 5. Alternative closure through strict descent packet

It is also acceptable to use

    primitiveCubicStrictDescent p

directly rather than the existential wrapper.

Then the recursion step is:

$$
\operatorname{measure}(next)<\operatorname{measure}(source).
$$

However, prefer the closure-facing theorem already created in U009B unless direct use makes the proof materially shorter.

## 6. Measure theorem wrapper

If helpful, expose:

    theorem primitiveCubicMeasure_eq
        {x y z : ℕ}
        (p : PrimitiveCubicPack x y z) :
        primitiveCubicMeasure p = x * y * z := rfl

and/or:

    theorem exists_smaller_primitiveCubicMeasure
        {a b c : ℕ}
        (p : PrimitiveCubicPack a b c) :
        ∃ x y z (q : PrimitiveCubicPack x y z),
          primitiveCubicMeasure q <
            primitiveCubicMeasure p

This is optional.

Do not add abstraction merely for style.

## 7. Primitive unconditional theorem

Mandatory public theorem:

    theorem FLT_d3_unconditional
        {a b c : ℕ}
        (ha : 0 < a)
        (hb : 0 < b)
        (hc : 0 < c)
        (hab : Nat.Coprime a b) :
        a ^ 3 + b ^ 3 ≠ c ^ 3 := by
      intro hEq
      exact primitiveCubicPack_false
        (primitiveCubicPack_of_hypotheses
          ha hb hc hab hEq)

Equivalent formatting is acceptable.

This is the main acceptance gate for U010.

## 8. Naming boundary

This theorem is "unconditional" relative to the prior DkMath primitive FLT3 theorem because it removes the extra hypothesis

    hS0_not_sq

and every NoSqOnS0 provider.

It still assumes

    Nat.Coprime a b

because arbitrary positive triple normalization belongs to U011.

Do not overstate it as the final full positive-natural endpoint yet.

## 9. Independence audit

Explicitly verify that FLT_d3_unconditional does not depend on:

- DkMath.FLT.Main.FLT_d3_by_padicValNat
- DkMath.FLT.Basic
- Mathlib.NumberTheory.FLT.Three
- any theorem named FermatLastTheoremThree or equivalent completed endpoint
- NoSqOnS0
- hS0_not_sq
- GEisensteinBridge provisional descent

Use source search / #print axioms / dependency inspection as practical.

The new module's direct imports alone are not sufficient evidence; report the transitive forbidden-path audit.

## 10. Axiom audit

Run #print axioms on at least:

    primitiveCubicPack_false
    FLT_d3_unconditional

Expected acceptable foundations:

    propext
    Classical.choice
    Quot.sound

depending on inherited existential choices.

Required:

- no sorryAx
- no project-specific axiom
- no external completed FLT3 theorem axiom/dependency

## 11. Optional theorem aliases

If useful for downstream U011, add:

    theorem primitive_positive_cubic_no_solution ...

as a thin alias around FLT_d3_unconditional.

But avoid redundant theorem proliferation.

## 12. Do not touch DkMath.FLT.Main yet

U010 should remain a self-contained

    DkMath.FLT.Three.*

tower endpoint.

Do not replace or rewrite the existing conditional theorem in Main.

Public aggregator / migration belongs to U011.

## 13. Non-goals

Do not implement in this checkpoint:

- gcd normalization of arbitrary positive a,b,c
- division by common gcd
- final fermatThree_no_positive_solution
- public DkMath.FLT.Three aggregator unless trivial and explicitly useful
- DkMath.FLT.Main cleanup
- deprecation of old conditional FLT3 theorem
- NoSqOnS0 deletion
- repository-wide import migration

## 14. Required report

Create:

    report-013.md

Record:

1. exact strong-induction theorem shape
2. recursion measure
3. source of strict decrease
4. primitiveCubicPack_false
5. FLT_d3_unconditional signature
6. confirmation hS0_not_sq is absent
7. confirmation NoSqOnS0 is absent
8. direct imports
9. transitive forbidden-completed-FLT3 audit
10. focused build result
11. #print axioms results
12. exact remaining U011 normalization task
13. Outcome A / B / C

## 15. Verification

Focused build:

    lake build DkMath.FLT.Three.PrimitiveCubicClosure

Major theorem audit:

    #print axioms DkMath.FLT.Three.primitiveCubicPack_false
    #print axioms DkMath.FLT.Three.FLT_d3_unconditional

Required:

- no new sorry
- no project-specific axiom
- no completed FLT3 shortcut
- no FLT5 / FLT7 production import
- no GEisenstein provisional descent dependency

## 16. Completion condition

FLT3U-010 is complete when the repository contains a kernel-checked theorem

$$
\forall a,b,c>0,\quad
\gcd(a,b)=1
\Longrightarrow
a^3+b^3\ne c^3
$$

implemented independently of completed FLT3 endpoints and without hS0_not_sq.

At that point the primitive FLT3 proof is complete.

Stop there.

FLT3U-011 will normalize an arbitrary positive hypothetical solution by its gcd and expose the final public theorem

    fermatThree_no_positive_solution.
