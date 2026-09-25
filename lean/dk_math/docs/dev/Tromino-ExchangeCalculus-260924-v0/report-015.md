# TRM-016 実装報告 — FlowPairing migration / label-only residual normal form

## 実装範囲

DkMath/Tromino/FlowPairing.lean を追加し、TRM-015 の
FlowSignature 上に pairing/residual 層を構築した。

FlowPairing F は、有限portの mate、involutive、同一labelを保持する。
固定点を flowResidualPorts、非固定点を flowPairedPorts として定義し、
membership、非残余mateの非自明性、同一label、involutive性を公開した。

## canonical construction

既存の BoundaryPairing にある adjacentMate、fiberPairing、
fiberPairing_involutive を再利用した。flowPortsWithLabel の有限fiberを
Fin index順に並べ、隣接rankを交換し、奇数fiberの最終rankを固定点とする
canonicalFlowMate / canonicalFlowPairing を追加した。

production側に Classical.choice を選択する pairing宣言や noncomputable 宣言は
追加していない。

## residual normal form

任意の F と label delta について、canonical pairingのlabel別残余集合の
cardinalityが

    flowLabelCount F delta % 2

に等しいことを証明した。さらに全残余数を A/B/C の三つのparityの和として
表現し、保存flowについて次を得た。

- all-even: residual set は空
- all-odd: residual card は3
- all-odd: A/B/C 各labelの residual card は1
- conserved decomposition: empty または card 3

非保存診断として A A B C は B/C を各1つ残し、A A は異なる
Fin index同士をpairすることを監査fixtureで確認した。

## BoundaryPairing erasure adapter

BoundaryPairing.toFlowPairing を追加し、mate、残余集合、paired集合の
compatibilityを証明した。

また、canonicalBoundaryPairing S と
canonicalFlowPairing S.toFlowSignature の canonical mate がpointwiseで
一致し、canonical residual setも一致することを証明した。これにより、
TRM-012のcanonical pairing/residual層が
BoundarySignature.toFlowSignature によるlabel erasureを通じて因子化する。

この実装では既存の BoundaryPairing.lean を書き換えず、ordered-pairing
helper再利用のため FlowPairing.lean からimportしている。

## Audit / validation

DkMathTest/Tromino/FlowPairingAxiomAudit.lean に以下を収録した。

- empty, even, odd, invalid, duplicate の独立 FlowSignature fixture
- odd caseのA/B/C各1残余
- duplicate Aの二つのdistinct Fin indexの相互pair
- contact-based signatureとerasure後のcanonical mate pointwise equality
- canonical residual set equality
- 任意の非残余flow portのtransition-readiness
- 主要定理の #print axioms

focused build:

    lake build DkMath.Tromino.FlowPairing
    lake build DkMathTest.Tromino.FlowPairingAxiomAudit

はいずれも成功した。回帰対象の BoundaryPairing、TransitionGraph、
TransitionXor を含むbuildも成功した。axiom auditは既存の有限集合・商・
古典的順序同型に由来する [propext, Classical.choice, Quot.sound] のみを
報告し、sorry、admit、unsafe、新規axiom、production側の noncomputable は
追加していない。

## 停止境界

TransitionGraph / TransitionXor のmigration、FlowNetwork、color recovery、
open path、ghost completion、planarity、BoundaryIR、optimization、
Four-Color theoremは実装していない。
