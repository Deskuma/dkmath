# TRM-018 実装報告 — FlowTransitionXor migration / label-only holonomy

## 実装範囲

DkMath/Tromino/FlowTransitionXor.lean を追加し、TRM-014の
transition-XOR / primitive-cycle obstruction層を
ClosedFlowNetwork上に独立実装した。

既存の TransitionXor APIは変更していない。characteristic-twoの
nsmul_state_eq_mod_two と nsmul_state_eq_zero_iff は既存定理を再利用し、
同じ定理を重複定義していない。

## flowTransitionXor

flowTransitionXor N p n は Finset.range n 上のiterate labelのsumである。
j = 0 のstarting port labelを一度数え、n steps分のlabelを加算する
TRM-014と同じconventionを採用した。

次を証明した。

- flowTransitionXor = n • starting label
- flowTransitionXor_add
- labelが非zeroであることによる XOR = 0 iff n % 2 = 0

このparity theoremはprimitive returnに限定せず、任意のnに対して成立する。

## return / primitive return / transport

FlowTransitionReturn、FlowPrimitiveTransitionReturn、
firstFlowTransitionReturn、FlowPrimitiveCycleCompatibleを追加した。

first returnのspecification、minimality、primitive性、primitive returnの
存在をNat.findで証明した。solver-facingなnoncomputable orbit objectは
導入していない。

flowTransportState は base + flowTransitionXor として定義し、zero-step、
concatenation、return-to-base iff XOR zero、primitive return-to-base iff
periodがevenを証明した。

## pure Flow fixture

監査にはBoundaryContactを使わないpure Flow fixtureを追加した。

- 2地域、各region A A、canonicalFlowPairing、region swap crossing
  - primitive period 2
  - XOR 0
  - transportはbaseへ帰還
- 3地域、各region A A、TRM-014と同じ6-port crossing pattern
  - 1回目、2回目はstartに戻らない
  - 3回目にreturn
  - primitive period 3
  - XOR = deltaA != 0
  - transportはbaseへ帰還しない

## contact-erasure calibration

ClosedBoundaryNetworkからClosedFlowNetworkへのerasureについて、次を
pointwiseまたは定義等式として証明した。

- flowTransitionXor = transitionXor
- flowTransportState = transportState
- FlowTransitionReturn と TransitionReturn の対応
- FlowPrimitiveTransitionReturn と PrimitiveTransitionReturn の対応
- FlowPrimitiveCycleCompatible と PrimitiveCycleCompatible の対応
- first return値の一致

したがってTRM-014のodd-cycle obstructionは、absoluteなinside/outside
値ではなく、erased labelとtransition certificateに依存する。

## 解釈境界

本checkpointが扱うのは、flow crossingとsame-label local pairingから
生成されるhomogeneous alternating transition orbit上のzero/nonzero
holonomyだけである。

これらのorbit上でzero holonomyが得られても、region graph上のglobal state
potential、一般pathのindependence、color recoveryが従うとは主張していない。
一般region-path integrationとそのcycle obstructionは後続checkpointに残す。

## Audit / validation

DkMathTest/Tromino/FlowTransitionXorAxiomAudit.lean に、repeated-label、
parity、2地域／3地域のprimitive cycle、transport、primitive compatibility、
erasure後のXOR・transport・return対応、#print axiomsを収録した。

次のbuildは成功した。

    lake build DkMath.Tromino.FlowTransition
    lake build DkMath.Tromino.TransitionXor
    lake build DkMath.Tromino.FlowTransitionXor
    lake build DkMathTest.Tromino.FlowTransitionXorAxiomAudit

production側に sorry、admit、unsafe、新規axiom、noncomputable宣言は
追加していない。axiom auditで報告された依存は既存の有限集合・順序同型・
商に由来する [propext, Classical.choice, Quot.sound] である。

## 次の境界

次の候補は、FlowTransitionXorから一般region-path potentialへ進む
checkpointである。ただし、path independence、global color recovery、
open residual paths、ghost completion、planarity、BoundaryIR、
optimization、Four-Color theoremは本checkpointでは実装していない。
