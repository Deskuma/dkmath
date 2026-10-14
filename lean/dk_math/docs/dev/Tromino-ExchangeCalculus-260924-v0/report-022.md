# TRM-023 実装報告 — finite face-orbit partition

## Orbit representation

\`DkMath/Tromino/FaceOrbit.lean\` を追加した。

\`totalPortCount N\` は \`Fintype.card (FlowNetworkPort N)\` を返す computable
observer として定義した。publicなorbit carrierは、より直接にprimitive return
を使う次の有限imageで構成した。

\`\`\`text
faceOrbit R C p =
  (Finset.range (firstFaceReturn R C p)).image
    (fun n => (faceStep R C)^[n] p)
\`\`\`

したがってcarrierは \`FlowNetworkPort\` のままであり、parallel-edge/port
multiplicityを失わない。

## Period and cardinality

\`faceOrbit_contains\`、\`faceOrbit_mem_iterate\`、および
\`faceOrbit_mem_iff_iterate\` を追加した。任意のiterateは、primitive periodを
modulusとする \`Function.IsPeriodicPt.iterate_mod_apply\` によりrange imageへ
戻る。

\`faceOrbit_iterate_distinct\` は、range内の2つのiterateが一致したとき、
\`faceEquiv\` のinjectivityで小さいiterateをcancelし、primitive minimalityに
反するpositive returnを得ることで指数の一致を証明する。これから

\`\`\`text
(faceOrbit R C p).card = firstFaceReturn R C p
\`\`\`

を導出した。

## Orbit relation and partition

\`faceOrbit_eq_of_mem\` は、orbit内の点を起点にしても同じFinsetになることを示す。
逆向きmembershipは、\`firstFaceReturn - n\` iterateとreturn equalityから構成した。

\`SameFaceOrbit\` と \`faceOrbitSetoid\` を追加し、反射・対称・推移をkernel-checkした。
さらに、任意の2 portについてorbitが等しいかdisjointであることを
\`faceOrbit_eq_or_disjoint\` として定理化した。 \`faceOrbit_coverage\` は各portが
自分のorbitに属することを返す。\`firstFaceReturn_eq_of_mem\` により、同一orbit
内でface lengthが不変である。

quotientのFintypeやface-count cardinalityはまだ導入していない。

## Audit fixtures

\`DkMathTest/Tromino/FaceOrbitAxiomAudit.lean\` を追加した。

TRM-022の2 regions × 3 ports fixtureでは、次を確認した。

- total port countは6
- \`p23\` の first returnは6
- orbit cardinalityは6
- 6個の各portがorbitに属する
- 任意iterateのmembership
- 6未満のpositive returnがない
- orbit内の別portから同じFinsetを得る
- orbit内でfirst returnが不変

追加の2 regions × 4 ports fixtureでは、identity rotationとregion-swapping
crossingによりindexごとの2-cycleを構成し、異なる2 orbitの非等値とdisjointnessを
確認した。

## Boundary

ここでのface orbitは、TRM-022で固定した有限combinatorial permutation

\`\`\`text
phi = rho ∘ alpha
\`\`\`

のorbitである。planar embeddingのtopological faceではない。

本checkpointでは、Euler characteristic、face quotient/cardinality、genus zero、
planarity、Jordan curve、noncrossing pairing、任意のplanar-map extraction、
ghost completion、BoundaryIR、optimization、Four-Color theoremは実装・主張していない。

## Validation

次のbuildは成功した。

    lake build DkMath.Tromino.FaceOrbit
    lake build DkMathTest.Tromino.FaceOrbitAxiomAudit
    lake build DkMathTest.Tromino.RotationSystemAxiomAudit
    lake build DkMathTest.Tromino.GraphColoringBridgeAxiomAudit

監査の \`#print axioms\` では、新規orbit定理が既存の有限性・周期性証明に由来する
\`propext\`、\`Quot.sound\`、\`Classical.choice\`の範囲であることを確認した。
新規production codeと監査fixtureに \`sorry\`、\`admit\`、\`unsafe\`、\`axiom\`、
\`noncomputable\` は追加していない。
