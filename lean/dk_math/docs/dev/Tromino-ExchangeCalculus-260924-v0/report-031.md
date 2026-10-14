# TRM-032 report — Kirchhoff V4 flow kernel / tension separation

実装対象は `instruction-031.md` の TRM-032 契約に限定した。既存の
`V4FlowAssignment`（nowhere-zero と crossing 同値）に、各 region の incident
port labels の和が `0` になる Kirchhoff 条件を追加した。

## 実装した production API

`DkMath/Tromino/PortKirchhoffFlow.lean` に次を追加した。

- `vertexKirchhoffSum A r`
- `IsKirchhoffV4Flow A` と `HasKirchhoffV4Flow M`
- `assignmentFlowSignature A r`
- Kirchhoff sum と `FlowSignature.flowSum` の一致
- `FlowConserved` との iff、および `flowConserved_iff_parity` による parity characterization
- assignment の crossing/rotation ではなく、各 vertex の incident labels だけに依存する局所定義

ここで crossing の `cross_sameLabel` は characteristic 2 による reversal の整合性であり、
Kirchhoff の局所保存則そのものではない。また `IsZeroHolonomyV4Tension` は closed
region walk の XOR が zero になる tension/coboundary 条件であり、両者は同じ述語ではない。

## kernel-checked fixture

`DkMathTest/Tromino/PortKirchhoffFlowAxiomAudit.lean` に、監査用の有限 fixture を追加した。

- 3 regions、各 arity 2、3 crossing edges、6 ports の triangle map
- face count `2`、Euler characteristic `2`、combinatorial genus `0`、sphere characteristic
- triangle の全ポートを `deltaA` とする assignment は Kirchhoff だが、cycle
  `t00 → t20 → t10 → t00` の XOR が `deltaA` なので zero holonomy tension ではない
- 既存 2×3 fixture の all-`deltaA` coloring assignment は zero-holonomy tension だが、
  degree 3 vertex の sum が `deltaA` となるため Kirchhoff ではない
- 2×3 fixture の `deltaA`/`deltaB`/`deltaC` balanced assignment は Kirchhoff
- triangle coloring `0, deltaA, deltaB` の edge labels は `deltaA`, `deltaC`, `deltaB`
  となる。これは coloring preview であり、flow と tension の双対性定理ではない

したがって、この checkpoint では少なくとも fixture 上で両方向の非含意を確認した。
同一 primal graph 上の「genus zero + Kirchhoff flow なら coloring」という命題は追加していない。

## 境界と未実装事項

`PortCrossing` は crossing の両端が異なる region であることを要求するため、bridge を
dual 側の loop として扱う一般的な dual-map API はこの checkpoint の対象外である。将来の
dual construction では bridge-free 仮定を明示するか、loop を許す crossing 構造を別途設計する
必要がある。

planar duality、bridge reduction、loop map、universal flow existence、topology realization、
Four Color theorem は実装していない。Mathlib にこの repository の port crossing/tension
構造へ直接適用できる nowhere-zero graph flow/tension API も本 checkpoint では導入していない。

## 検証

成功した build:

```text
lake build DkMath.Tromino.PortKirchhoffFlow \
  DkMathTest.Tromino.PortKirchhoffFlowAxiomAudit
Build completed successfully (1561 jobs).
```

既存回帰については、TRM-031 の production と audit、および combinatorial map の production
と audit を同じ toolchain で再ビルドする。
