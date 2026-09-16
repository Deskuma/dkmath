# instruction-002 — Exact Cubic Depth and Forced High-Lift

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: FLT3U-001 completed with Outcome A.

## 1. Mission

PrimitiveCubicLiftPacket が与える valuation lower bound を、FLT3 equation の完全立方構造まで戻して exact に強化する。

この checkpoint の主目的は、仮想 primitive FLT3 counterexample から選ばれる primitive prime q が単なる Lift candidate ではなく、

$$
3 \mid v_q(GN_3(c-b,b))
$$

を満たす cubic-depth high-lift prime であることを production theorem として固定することである。

NoLift / Lift の一般場合分けを新たに構築することは目的ではない。

FLT3 counterexample の文脈では FLT3U-001 が既に

$$
3 \le v_q(GN_3(c-b,b))
$$

を与えており、本流は high-lift 側へ強制される。

## 2. Read first

必須:

    lean/dk_math/DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean
    lean/dk_math/docs/dev/FLT3-Unconditional-260904-v0/report-001.md
    lean/dk_math/DkMath/FLT/PhaseLift.lean
    lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean
    lean/dk_math/DkMath/Petal/PrimitiveBridge.lean

必要に応じて padicValNat の Mathlib API と current source を調査する。

完成済み FLT3 theorem は使用しない。

## 3. Exact valuation target

primitive FLT3 equation

$$
a^3+b^3=c^3
$$

から

$$
c^3-b^3=a^3
$$

を得る。

FLT3U-001 と同じ primitive valuation transport により

$$
v_q(GN_3(c-b,b))=v_q(c^3-b^3).
$$

従って

$$
v_q(GN_3(c-b,b))=v_q(a^3).
$$

padicValNat の canonical power theorem を用いて

$$
v_q(a^3)=3v_q(a)
$$

を得る。

最終的に、実際の current API / simp normal form に合わせて次の exact equality を production theorem として固定せよ。

    padicValNat q
        (DkMath.CosmicFormulaBinom.GN 3 (c - b) b)
      =
    3 * padicValNat q a

乗算順序は existing theorem の正規形に合わせてよい。

## 4. Ownership of the FLT equation

現行 PrimitiveCubicLiftPacket は FLT equation 自体を field として保持していない。

そのため exact valuation theorem の API は、次のどちらかの最小設計を選ぶ。

A. packet と hEq : a ^ 3 + b ^ 3 = c ^ 3 を受け取る theorem
B. exact cubic-depth 用の小さな companion packet / theorem result を新設する

既存 packet に equation を後付けして肥大化させる必要はない。

最小依存と将来の consumer の使いやすさを優先する。

## 5. Positive cubic depth

PrimitiveCubicLiftPacket の hq, hqGN, hdepth および exact valuation equality から、少なくとも次を得る。

$$
0 < v_q(a)
$$

および

$$
\exists k:\mathbb N,\quad 0<k \land v_q(GN_3(c-b,b))=3k.
$$

第一候補は

    k := padicValNat q a

とする。

可能なら exact equality から直接導き、既存 hdepth と整合することを確認する。

## 6. Forced high-lift theorem

exact cubic depth または既存 lower bound から

$$
q^3\mid GN_3(c-b,b)
$$

を production theorem として固定せよ。

候補 shape:

    theorem cube_dvd_GN_of_primitiveCubicLiftPacket
        (h : PrimitiveCubicLiftPacket a b c q) :
        q ^ 3 ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b := by
      ...

実際の theorem は hdepth だけで十分なら equation を再要求しないこと。

q^2 ∣ GN3 wrapper は後続で有用かつ短い場合のみ追加してよい。

## 7. Structural conclusion

この checkpoint の report では、以下を明記する。

    primitive FLT3 counterexample
      -> primitive q
      -> PrimitiveCubicLiftPacket
      -> valuation depth >= 3
      -> q^3 | GN3
      -> q^2 | GN3

従って、旧 hS0_not_sq conditional proof は

    NoLift を仮定すれば counterexample は即座に消える

という fast contradiction として保存される。

unconditional route の残りは high-lift branch の global arithmetic closure である。

## 8. Hensel connection audit

GNThreeHenselDepth との接続可能性を確認する。

この checkpoint では Hensel recursion を実装しない。

report では exact depth

$$
3k
$$

が既存 finite Hensel theorem のどの depth parameter / hypothesis に対応するかを記録する。

Hensel lift の存在や一意性そのものを contradiction として扱ってはならない。

deep simple-root branch は current GNPC API 上で実在可能である。

## 9. Proposed module

第一候補:

    DkMath/FLT/Three/CubicValuationDepth.lean

ただし exact valuation theorem が packet API と密接で小さい場合は PrimitiveCubicLiftPacket.lean への限定的追加も許可する。

module が valuation algebra を独立所有できるなら分離を優先する。

新 module から DkMath.FLT.Main を import しない。

## 10. Non-goals

この checkpoint では以下を実装しない。

- general NoLift / Lift case splitter
- Hensel recursion
- Eisenstein ring construction
- ramifier stripping
- conjugate coprimality
- unit extraction / unit sector classification
- strict descent
- well-founded closure
- final FLT3 theorem
- old NoSqOnS0 adapter modifications

universal q^2 ∤ GN3 theorem を作らない。

## 11. Verification

新 module を作った場合の focused build:

    lake build DkMath.FLT.Three.CubicValuationDepth

同 module に追加した場合はその module を build する。

主要 theorem について #print axioms を確認する。

確認事項:

- no new sorry
- no project-specific axiom
- no DkMath.FLT.Main dependency
- no completed external FLT3 theorem shortcut dependency

## 12. Deliverables

- Lean implementation
- report-002.md
- ROADMAP status update only if実装結果が route を変更する場合

report-002.md には最低限以下を記録する。

1. exact valuation theorem
2. positive multiplier k
3. q^3 ∣ GN3 theorem
4. whether q^2 ∣ GN3 wrapper was added
5. Hensel depth connection
6. actual imports
7. build result
8. Outcome A / B / C

## 13. Completion condition

FLT3U-002 は、仮想 primitive FLT3 counterexample の equation と PrimitiveCubicLiftPacket から

$$
\exists k>0,\qquad v_q(GN_3(c-b,b))=3k
$$

を取得でき、さらに packet だけから

$$
q^3\mid GN_3(c-b,b)
$$

を取得できる時点で完了とする。

そこで停止する。

Eisenstein descent は FLT3U-003 から開始する。
