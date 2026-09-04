# FLT3 Unconditional ROADMAP

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Base: develop @ 99ff6fcefed5bb1775e0a685cee9025fd7fdcc69

## 0. Summit

最終目標:

$$
\forall a,b,c\in\mathbb N_{>0},
\qquad
a^3+b^3\ne c^3.
$$

DkMath 内の証明として完結させ、既成 FLT3 theorem を import して閉じない。

## 1. Route overview

    positive counterexample
      ↓
    primitive normalization
      ↓
    c^3 - b^3 = a^3
      ↓
    primitive prime q
      ↓
    q-adic mass is transported to GN3 = S0
      ↓
    ┌──────────────────────────┬─────────────────────────────┐
    │ NoLift                   │ Lift                        │
    │ q² ∤ GN3                 │ q² ∣ GN3                    │
    │                          │                             │
    │ existing valuation       │ depth is compatible with   │
    │ 3 ≤ v_q ≤ 1             │ a perfect cube              │
    │ → False                  │                             │
    └──────────────────────────┴──────────────┬──────────────┘
                                              ↓
                                      Eisenstein arithmetic
                                              ↓
                                      ramifier ownership
                                              ↓
                                      conjugate coprimality
                                              ↓
                                      unit × cube extraction
                                              ↓
                                      finite unit sectors
                                              ↓
                                      strict smaller packet
                                              ↓
                                      well-founded descent
                                              ↓
                                            False

## 2. FLT3U-000 — Workspace reconnaissance

Status: active first task

Goal:

現行 develop の FLT3 / GNPC / Eisenstein / primitive-prime 資産を実コードから棚卸しし、再利用可能 theorem と不足 theorem を report-000.md に固定する。

No implementation.

Deliverable:

    report-000.md

Mandatory findings:

1. FLT_d3_by_padicValNat の exact external obligation
2. primitive q の existing witness type
3. S0 = GN3 bridge の canonical theorem
4. primitive valuation transport の canonical theorem
5. q = 3 exclusion に使える existing theorem
6. q ≡ 1 mod 3 constraint
7. derivative nondegeneracy theorem
8. arbitrary finite Hensel depth theorem
9. Eisenstein integer support in Mathlib / DkMath
10. existing descent skeleton and what remains abstract
11. dependency path to any already-completed FLT3 theorem
12. recommended minimal imports for FLT3U-001

## 3. FLT3U-001 — Primitive Cubic Lift Packet

Goal:

仮想 primitive FLT3 counterexample と既存 primitive prime witness を、GNPC が直接消費できる一つの packet / theorem surface へ接続する。

Primary output candidate:

    DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean

Required mathematical facts for the supplied primitive q:

$$
\gcd(c-b,b)=1,
$$

$$
q\mid GN_3(c-b,b),
$$

$$
q\ne3,
$$

$$
3\mid q-1,
$$

$$
q\nmid 2(c-b)+3b,
$$

and

$$
3\le v_q(GN_3(c-b,b)).
$$

Do not prove arbitrary-depth descent yet.

## 4. FLT3U-002 — NoLift / Lift exact split

Goal:

既存 conditional FLT3 route を NoLift consumer として保存し、残存 branch を high-lift packet に正確に変換する。

Desired shape:

    either q^2 ∤ GN3 and contradiction
    or q^2 ∣ GN3 and HighLiftCubicPacket

重要:

Lift branch は異常状態ではない。GN3(17,1)=7^3 が存在するため、branch 自体を否定してはいけない。

## 5. FLT3U-003 — Eisenstein arithmetic substrate

Goal:

strict descent に必要な最小 Eisenstein arithmetic を決める。

Reconnaissance 結果に応じて次のどちらかを選ぶ。

A. Mathlib / DkMath の既存 Eisenstein integer type を直接利用
B. FLT3 専用の局所的な二座標 model を作り、後で一般化

Required surface:

- conjugation
- norm
- multiplicativity
- ramifier above 3
- units
- divisibility / gcd or ideal coprimality
- cube coordinate formula

S0 / GN3 との norm bridge を production theorem にする。

## 6. FLT3U-004 — Exact ramified routing

Goal:

FLT3 equation の factorization において 3-adic ramifier がどの因子へ何回所属するかを exact に固定する。

No heuristic valuation statement.

Output:

ramifier stripping 後の element β と

$$
N(\beta)=B^3
$$

型の exact norm packet。

## 7. FLT3U-005 — Conjugate coprimality

Goal:

β と conjugate β が、許された ramified factor を除去した後に coprime であることを証明する。

ここが cube extraction の gate。

必要なら element gcd ではなく ideal language を使う。

## 8. FLT3U-006 — Cube extraction

Goal:

UFD / PID / ideal factorization により

$$
\beta=\varepsilon\gamma^3
$$

を得る。

既成 FLT3 theorem は使用禁止。

## 9. FLT3U-007 — Unit classes modulo cubes

Goal:

Eisenstein unit を cube equivalence で有限分類する。

Expected finite sectors:

$$
1,\omega,\omega^2
$$

相当。

実際の Mathlib representation に合わせて theorem surface を設計する。

## 10. FLT3U-008 — Sector arithmetic exclusion

Goal:

strict descent へ戻らない unit sectors を有限 arithmetic で排除する。

数値 residue / coordinate congruence で閉じられるところは abstract algebra を増やさない。

## 11. FLT3U-009 — Zero-sector strict descent reconstruction

Goal:

残る cube sector から、元と同型で測度が厳密に小さい primitive FLT3 packet を構成する。

候補となる cube coordinate identity を実コードで確認する。

Conceptual form:

$$
\gamma=(r,s)
\quad\Longrightarrow\quad
(\gamma^3)_2=3rs(r-s)
$$

pairwise coprime 化から各因子を cube へ分離し、新 counterexample を再構成する。

最重要 checkpoint。

## 12. FLT3U-010 — Well-founded closure

Goal:

strict descent packet を Nat-valued measure に接続し、無限降下を Lean の well-founded induction / strong induction で閉じる。

Primitive theorem をここで無条件化する。

Target:

    FLT_d3_unconditional

## 13. FLT3U-011 — Positive-natural normalization and public API

Goal:

任意の正の自然数解を primitive counterexample へ gcd normalization し、primitive theorem へ送る。

Final target:

    fermatThree_no_positive_solution

Public aggregator と axiom audit を追加する。

## 14. Stop conditions

各 checkpoint で以下なら停止して report に戻す。

- 必要 theorem が current source と異なる
- proposed universal statement に counterexample が見つかる
- import cycle が発生する
- strict decrease が証明できず単なる self-similarity に留まる
- Mathlib の完成 FLT3 theorem への依存が混入する

失敗は route failure と決めつけず、未証明境界を exact Prop として記録する。

## 15. Completion gate

完了宣言には最低限次を要求する。

1. primitive unconditional theorem
2. full positive-natural theorem
3. no hS0_not_sq / NoSqOnS0 assumption
4. no completed external FLT3 theorem dependency
5. no project-specific axiom / sorry
6. public import path
7. theorem dependency / axiom audit document
