# instruction-001 — Primitive Cubic Lift Packet

cid: 6a9aa2b0-937c-83e8-aa29-b3474c8acdf9

Branch: wip/flt3-unconditional-260904-v0

Prerequisite: instruction-000 completed and report-000.md reviewed.

## 1. Goal

現行 FLT3 conditional route と GNPC degree-three API の間に、最初の production bridge を作る。

この checkpoint では strict descent を始めない。

仮想 primitive FLT3 counterexample から得た primitive prime q を、GNPC が直接消費できる一つの局所 packet / theorem surface にまとめることだけを行う。

## 2. Proposed module

第一候補:

    DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean

report-000.md が import-cycle または既存所有者の理由で別配置を推奨した場合のみ、最小限修正してよい。

新 module から DkMath.FLT.Main を import しない。

Main は将来 consumer 側にする。

## 3. Mathematical coordinates

Assume positive primitive FLT3 data

$$
a^3+b^3=c^3,
\qquad
\gcd(a,b)=1.
$$

既存 route と同じ orientation で

$$
u:=c-b,
\qquad
x:=b
$$

と読む。

Then

$$
GN_3(u,x)=S_0(c,b).
$$

A supplied primitive prime q satisfies

$$
q\mid c^3-b^3,
\qquad
q\nmid c-b.
$$

## 4. Required theorem content

report-000 の exact identifiers を再利用して、同じ q に対し少なくとも次を一つの theorem または structure constructor から取り出せるようにせよ。

$$
\gcd(u,x)=1,
$$

$$
q\mid GN_3(u,x),
$$

$$
q\ne3,
$$

$$
3\mid q-1,
$$

$$
q\nmid 2u+3x,
$$

$$
3\le v_q(GN_3(u,x)).
$$

where u = c-b and x = b.

### Important

最後の lower bound は NoLift 仮定から出してはいけない。

完全立方

$$
c^3-b^3=a^3
$$

と primitive valuation transport から出すこと。

## 5. Preferred API design

過度に大きな counterexample structure は作らない。

第一候補は、既存 q witness を受け取る軽い packet。

Example shape, to be adjusted to actual current API:

    structure PrimitiveCubicLiftPacket
        (a b c q : ℕ) : Prop where
      hq : Nat.Prime q
      hqDiff : q ∣ c ^ 3 - b ^ 3
      hqBoundary : ¬ q ∣ c - b
      hcopCoordinates : Nat.Coprime (c - b) b
      hqGN : q ∣ DkMath.CosmicFormulaBinom.GN 3 (c - b) b
      hqThree : q ≠ 3
      hresidue : 3 ∣ q - 1
      hderivative : ¬ q ∣ 2 * (c - b) + 3 * b
      hdepth : 3 ≤ padicValNat q
        (DkMath.CosmicFormulaBinom.GN 3 (c - b) b)

ただし同じ情報を既存 structures の conjunction theorem で十分表現できるなら、新 structure を無理に追加しない。

report-000 の推奨を優先する。

## 6. Constructor theorem

primitive FLT3 equation と existing primitive q witness から packet を構築する theorem を実装せよ。

Candidate shape:

    theorem primitiveCubicLiftPacket_of_counterexample_prime
        {a b c q : ℕ}
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
        (hab : Nat.Coprime a b)
        (hEq : a ^ 3 + b ^ 3 = c ^ 3)
        (hq : Nat.Prime q)
        (hqDiff : q ∣ c ^ 3 - b ^ 3)
        (hqBoundary : ¬ q ∣ c - b) :
        PrimitiveCubicLiftPacket a b c q := by
      ...

Exact orientation and redundant positive assumptions may be simplified if current theorems allow it.

Do not introduce an axiom/provider for any packet field.

## 7. Optional exact cube-multiplicity lemma

If report-000 shows this closes naturally without expanding scope, add:

$$
3\mid v_q(GN_3(c-b,b)).
$$

This is stronger than hdepth and will be useful later.

But do not delay the checkpoint if padicValNat power API makes the exact divisibility lemma substantially larger.

Record it as FLT3U-002 input if deferred.

## 8. Non-goals

Do not implement:

- q^2 case split
- Hensel recursion
- Eisenstein integer ring
- ramifier stripping
- unit classification
- strict descent
- final FLT3 theorem
- modifications to old NoSqOnS0 adapters

Do not prove q^2 ∤ GN3.

Do not remove the GN3(17,1)=343 regression.

## 9. Imports

Use report-000 recommended minimal lower-level imports.

Avoid:

    import DkMath.FLT.Main

and any import whose purpose is only to obtain a finished FLT3 theorem.

The new module should be suitable for later import by Main without a cycle.

## 10. Verification

Required:

1. build the new module
2. build any touched aggregator if one is intentionally changed
3. confirm no new sorry
4. confirm no project-specific axiom
5. grep/import audit for completed FLT3 shortcut dependency

Do not require full DkMath build for this micro-checkpoint unless imports force it.

## 11. Deliverables

- new Lean module
- report-001.md
- ROADMAP status update only if checkpoint outcome changes the planned route

report-001.md must state:

1. exact theorem surface added
2. which existing theorems supplied each packet field
3. whether q ≠ 3 required a new lemma
4. whether exact 3 | valuation was included or deferred
5. actual import boundary
6. build result
7. Outcome A/B/C

## 12. Completion condition

FLT3U-001 is complete when a later theorem can take one packet and immediately invoke the GNPC non-ramified cubic API without re-deriving FLT3 coordinate facts.

Stop after this boundary.

Do not start FLT3U-002 in the same checkpoint.
