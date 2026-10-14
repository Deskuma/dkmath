# TRM-017 実装報告 — FlowTransition migration / label-only closed network

## 表現

DkMath/Tromino/FlowTransition.lean を追加した。

FlowNetwork は有限region数と各regionの FlowSignature を保持し、
FlowNetworkPort は region index とそのregion内の Fin port indexからなる
Sigma型とした。FlowCrossing は全portの involutive crossing、region変更、
label保存を保持する。ClosedFlowNetwork は crossing、各regionの
FlowPairing、全pairingのperfect条件を保持する。

crossingは常にregionを変更するTRM-013と同じfirst-kernel scopeに留め、
self-adjacent region edgeを導入していない。

## crossing / local mate

flowCrossPort と flowLocalMatePort を定義し、次を証明した。

- crossingのinvolutive性、region変更、非自己性、label保存
- local mateのinvolutive性、region保存、perfect性からの非自己性、label保存
- crossingとlocal mateの各portでの相違

## transition kernel

flowTransitionNeighbors と FlowTransitionAdj を追加した。
各portの二つのneighborが異なることからneighbor cardが2であることを
証明し、adjacencyの対称性、非反射性、degree-two theoremを提供した。
Mathlib SimpleGraphへの依存は追加していない。

## transition permutation / periodicity

TRM-013と同じ convention

    flowTransitionStep p := flowLocalMatePort (flowCrossPort p)

および逆写像を定義した。left/right inverse、injective、surjective、
flowTransitionEquiv、iterateによるlabel保存、有限permutation orderに基づく
正周期を証明した。XOR accumulationはこのcheckpointでは定義していない。

## Boundary erasure adapter

次のadapterを追加した。

- BoundaryNetwork.toFlowNetwork
- BoundaryCrossing.toFlowCrossing
- ClosedBoundaryNetwork.toClosedFlowNetwork

erasure後もcrossingとpairingのmateを同じ関数として保持し、perfect条件を
FlowPairingのresidual equalityへ移した。

contact-based closed networkについて、次のpointwise calibrationを証明した。

- flowCrossPort = crossPort
- flowLocalMatePort = localMatePort
- flowTransitionStep = transitionStep
- erased transition label = boundaryDelta label
- positive periodicityの同一statement

したがってTRM-013のclosed transition dynamicsは、
絶対的なinside/outside値ではなく、erased nonzero labelと
crossing/pairing certificateを通じて因子化する。

## Audit / validation

DkMathTest/Tromino/FlowTransitionAxiomAudit.lean に以下を収録した。

- 二地域、各region A A のpure FlowNetwork fixture
- total port count 4
- crossing/local mateのinvolutive性と非自己性
- crossing/local mateの相違
- neighbor card 2、adjacency symmetry、irreflexivity
- label preservationとpositive periodic orbit
- contact-based二地域networkのerasure後crossing/local mate/step一致
- erased transition labelと周期性の一致
- 主要定理の #print axioms

focused buildと回帰buildは次の通り成功した。

    lake build DkMath.Tromino.FlowPairing
    lake build DkMath.Tromino.TransitionGraph
    lake build DkMath.Tromino.FlowTransition
    lake build DkMathTest.Tromino.FlowTransitionAxiomAudit
    lake build DkMath.Tromino.TransitionXor

production側に sorry、admit、unsafe、新規axiom、noncomputable宣言は
追加していない。axiom auditの報告は既存の有限集合・順序同型・商に由来する
[propext, Classical.choice, Quot.sound] である。

## 次のcheckpointへの境界

次はFlowTransition上のlabel-only XOR / holonomy migrationを候補とする。
TransitionXor本体の移行、color recovery、open residual paths、ghost completion、
planarity、BoundaryIR、optimization、Four-Color theoremは本checkpointでは
実装していない。
