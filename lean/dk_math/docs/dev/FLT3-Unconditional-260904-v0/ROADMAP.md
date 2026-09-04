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
    PrimitiveCubicLiftPacket
      ↓
    exact cubic depth v_q(GN3) = 3 * v_q(a)
      ↓
    q³ ∣ GN3
      ↓
    forced high-lift branch
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

Status: completed — Outcome A

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

Status: completed — Outcome A

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

## 4. FLT3U-002 — Exact Cubic Depth and Forced High-Lift

Status: completed — Outcome A

Goal:

FLT3U-001 の packet と FLT3 equation から valuation を exact に強化し、

$
v_q(GN_3(c-b,b))=3v_q(a)
$

および

$
q^3\mid GN_3(c-b,b)
$

を production theorem として固定する。

この結果、primitive FLT3 counterexample の本流は NoLift / Lift の一般場合分けではなく high-lift branch へ強制される。

旧 conditional route は NoLift fast contradiction として保存し、unconditional proof は forced high-lift から Eisenstein descent へ進む。

## 5. FLT3U-003 — Eisenstein Coordinate Substrate

Status: completed — Outcome A

Goal:

既存 TraceOneInt (-1) を FLT3 の production Eisenstein coordinate ring として採用し、座標規約を固定する。

この basis は

$
\tau^2-\tau+1=0
$

であり、

$
N(r+s\tau)=r^2+rs+s^2.
$

この checkpoint では conjugation / norm multiplicativity / basis unit identities / ramifier candidate

$
\lambda=1+\tau,\qquad N(\lambda)=3
$

/ cube coordinate identity

$
((r+s\tau)^3)_2=3rs(r+s)
$

/ S0 and GN3 norm bridge を production theorem として固定する。

UFD/PID、ramifier ownership、conjugate coprimality、complete unit classification、strict descent は後続 checkpoint に残す。

## 6. FLT3U-004 — Exact ramified routing

### FLT3U-004A — Signed Three-Adic Routing and Exact Power Split

Status: completed — Outcome A

primitive FLT3 counterexample を mod 9 で signed orientation へ正規化し、common packet を作る。

Target:

$
\operatorname{carrier}=9A^3,
$

$
\operatorname{residual}=3B^3,
$

$
\operatorname{distinguished}=3AB,
$

with

$
\gcd(A,B)=1,
\qquad
3\nmid B.
$

Signed Eisenstein coordinate alpha must satisfy

$
N(\alpha)=\operatorname{residual},
$

$
\alpha_{\rm snd}-\alpha_{\rm fst}=\operatorname{carrier}.
$

### FLT3U-004B — Eisenstein Ramifier Stripping

Status: completed — Outcome A

Using

$
\lambda=1+\tau,
\qquad
N(\lambda)=3,
$

construct beta with

$
\alpha=\lambda\beta,
$

$
N(\beta)=B^3,
$

and the exact second-coordinate equation expected from the signed convention, ideally

$
\beta_{\rm snd}=3A^3.
$

No UFD/PID or conjugate coprimality is required until U005.

Mandatory stripped normal form:

$
\alpha=\lambda\beta,
$

$
N(\beta)=B^3,
$

$
\beta_{\rm snd}=3A^3,
$

with the ramified norm load exhausted:

$
3\nmid N(\beta).
$

## 7. FLT3U-005 — Conjugate coprimality

Status: active next task

Goal:

β と conjugate β が、ramifier 除去後に common nonunit divisor を持たないことを証明する。

Current stripped identities:

$
N(\beta)=B^3,
$

$
\beta_{\rm snd}=3A^3.
$

Hence

$
N(\beta-\overline\beta)=27A^6.
$

Using

$
\gcd(A,B)=1,
\qquad
3\nmid B,
$

prove that every common divisor d of beta and conjugate beta has unit norm and therefore is a unit.

This checkpoint deliberately avoids assuming a UFD/PID structure.

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
(\gamma^3)_2=3rs(r+s)
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
