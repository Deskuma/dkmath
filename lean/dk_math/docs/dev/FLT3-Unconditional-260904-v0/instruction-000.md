# instruction-000 — FLT3 Unconditional Workspace Reconnaissance

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Base: develop @ 99ff6fcefed5bb1775e0a685cee9025fd7fdcc69

## 1. Mission

実装を始める前に、現在の workspace に存在する FLT3 / GNPC / Eisenstein / primitive-prime / valuation 資産を read-only で調査し、次 checkpoint の exact theorem surface を確定せよ。

この checkpoint では Lean source を新規実装・修正しない。

作成するのは

    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-000.md

のみ。

## 2. Read first

必須:

    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/README.md
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/ROADMAP.md
    lean/dk_math/DkMath/FLT/README.md
    lean/dk_math/DkMath/FLT/Main.lean
    lean/dk_math/DkMath/FLT/PhaseLift.lean
    lean/dk_math/DkMath/FLT/GEisensteinBridge.lean
    lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
    lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
    lean/dk_math/DkMath/NumberTheory/GNThreeQuadratic.lean
    lean/dk_math/DkMath/NumberTheory/GNThreePrimeArithmetic.lean
    lean/dk_math/DkMath/NumberTheory/GNThreeHenselLift.lean
    lean/dk_math/DkMath/NumberTheory/GNThreeHenselDepth.lean

必要なら summary / grep を使用してよい。

巨大 raw conversation log は探索対象にしない。

## 3. Questions to answer

report-000.md で以下に exact identifier と file path を付けて答えよ。

### Q1. Current conditional endpoint

FLT_d3_by_padicValNat の完全な型は何か。

hS0_not_sq が証明中のどこで一度だけ使われるか。

NoSqOnS0 adapter 群は本体か互換層か。

### Q2. Primitive prime witness

exists_prime_factor_cube_diff の exact return data は何か。

q prime, q | c^3-b^3, q ∤ c-b 以外の情報を既に持つか。

### Q3. Difference / GN / S0 bridge

次の各 identity の canonical theorem を特定せよ。

$$
c^3-b^3=(c-b)S_0(c,b)
$$

$$
S_0(c,b)=GN_3(c-b,b)
$$

$$
v_q(c^3-b^3)=v_q(GN_3(c-b,b))
$$

同じ主張の theorem が複数ある場合、production 向け最小依存を推奨せよ。

### Q4. Primitive coordinate coprimality

primitive FLT3 counterexample から

$$
\gcd(c,b)=1
$$

および

$$
\gcd(c-b,b)=1
$$

を得る既存 theorem を特定せよ。

不足なら最小補題 shape を提案せよ。

### Q5. Ramified prime 3

primitive q が 3 ではないことを current API だけでどこまで直接示せるか。

GNThreePrimeArithmetic の

    three_dvd_GN_three_iff_dvd_boundary
    not_nine_dvd_GN_three_of_coprime

等が FLT3 coordinates でどう使えるかを確認せよ。

### Q6. Non-ramified cubic shell

次を供給する exact theorem を特定せよ。

$$
3\mid q-1
$$

$$
q\nmid 2u+3x
$$

where

$$
u=c-b,\qquad x=b.
$$

### Q7. Finite Hensel depth

GNThreeHenselLift / GNThreeHenselDepth が実際に何を証明しているか。

特に arbitrary finite depth の unique next digit theorem と derivative stability を列挙せよ。

それらが deep lift の存在を否定していないことも明記せよ。

### Q8. Cube-side valuation

FLT3 equation と primitive q から

$$
3\le v_q(GN_3(c-b,b))
$$

を現行 theorem の合成だけで出せるか。

可能なら exact proof chain を列挙せよ。

さらに

$$
3\mid v_q(GN_3(c-b,b))
$$

という exact multiple-of-three statement が既存 API で容易か、追加補題が必要かを判定せよ。

### Q9. Eisenstein substrate

Mathlib および DkMath に、Eisenstein integer / Z[ω] / quadratic integer ring の production-ready type が存在するか調査せよ。

次を確認:

- ring structure
- conjugation
- norm
- units
- EuclideanDomain / PID / UFD
- ideal factorization
- ramifier above 3
- cube coordinate formula

既存の GEisensteinBridge が generic descent skeleton 以外に何を実装済みかも分離して書け。

### Q10. Forbidden shortcut audit

current DkMath のどこかが Mathlib の完成 FLT3 theorem を import / use しているか調査せよ。

新 DkMath.FLT.Three tower がそれを transitive に import しないための推奨 import boundary を示せ。

### Q11. FLT5 Essence reuse

FLT5 の completed descent から、コードを import せず証明戦略として再利用できる段階を列挙せよ。

特に

    primitive normalization
    ramifier stripping
    conjugate coprimality
    unit × power extraction
    unit sector classification
    strict descent

のうち FLT3 へ直接移植可能 / 非該当 / 要再証明を分類せよ。

## 4. Required report structure

report-000.md は次の順で書く。

1. Executive conclusion
2. Exact current FLT3 proof frontier
3. Reusable theorem inventory table
4. False / forbidden route inventory
5. GNPC-to-FLT3 connection
6. Eisenstein substrate inventory
7. Dependency audit
8. Minimal imports recommended for FLT3U-001
9. Proposed exact theorem / structure surface for FLT3U-001
10. Risks and stop conditions
11. Outcome

Outcome labels:

    Outcome A
      FLT3U-001 can proceed essentially as planned.

    Outcome B
      Route is sound but theorem surface/import boundary should be revised.

    Outcome C
      A missing mathematical bridge must be solved before FLT3U-001.

    Outcome D
      Current route contains a mathematical contradiction or forbidden dependency.

## 5. Restrictions

- no Lean source implementation
- no theorem renaming
- no refactor
- no public import update
- no use of completed external FLT3 theorem as evidence that the route works
- do not reinterpret GN3(17,1)=343 as a failure; it is a required regression proving universal no-lift is false

## 6. Verification

This is reconnaissance only.

Run lightweight source searches as needed.

A full lake build is not required unless the workspace itself appears inconsistent.

Commit only report-000.md with a concise reconnaissance commit message.
