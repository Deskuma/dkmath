# NOTE-032 — 特異核の節点水準と同じ商像

2026-10-27。開始 HEAD `0e49347a4`。ユーザーから前回フルビルド通過を受領した。
作業開始時にステージ済みの `STATUS-N032-05X24.md` は、ユーザー提供の現状分析として保持した。

## 模範解答との対応

[模範解答の特異核側](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean) の保存済みソース（blob `ab1aee61bdcfbe439dcf9693d5f1417cacc05b6b`）を照合した。特異核側の核の深さ `kernel_level`、中心の一致、`master_off`・`master_on` の付値評価、枝の判定を合わせて逆像を導く構成である。

今回はそのうち中心からの距離と補正項の評価を、DkMath の既存の実点・半核・`kernelXAt` に翻訳した。参照定理を未証明の前提として追加せず、証明した付値評価と明示的な残りの仮定を区別する。模範解答由来のコードを含む二つの所有ファイルには Apache-2.0、著作権、出典 blob、変更内容を記載し、既存の `RegularKummer/LICENSE` と `ANTHROPIC-NOTICE` を参照する。

## 節点距離による商座標

源の臨界中心を `C=(x₀,y₀)`、半核点 Q の節点距離を `X_Q=x(Q)-x₀`、源点 P の距離を `X=x(P)-x₀` とする。中心誤差 `ε=equationDefect(E,x₀,y₀)` と `β=b₂+12x₀` を保持して、Vélu の反転対の補正分子を

`β X_Q X + 6 X_Q² X − 2 X_Q³ − 4 ε`

と表す。実点 P が H の外なら、半核点の x と P の x は一致しないことも内部証明し、同じ `kernelXAt` の半核和を上記の分数に書き直した。曲線の分岐を便宜的に別の点群に置き換えていない。

付値体上の独立した一般補題として、点の距離が核水準と異なるとき各補正が小さく、ちょうど一つの核水準と一致するときその項が他の項を支配することを証明した。前提には、`v(β)=1`、核距離の付値が1未満、中心誤差の付値が核距離の二乗より小さいことが含まれる。

## 同じ標的の滑らかさへの接続

特異核側では、既存の源・標的の剰余モデル等式と節点の一意性を使い、任意に指定された源・標的の臨界中心の x 座標が合同することを証明した。標的の臨界中心の存在は入力である。

この合同と上記の付値評価を合わせ、源の特異な核外点について、中心誤差の深さを仮定した下で以下を得た。

- 商像が滑らかなら、源点の節点距離は同じ半核のある距離と同じ付値を持つ。
- 半核の異なる点の距離の付値が相異なるなら、商像が滑らかであることと、その半核水準のいずれかとの一致は同値である。
- 3点核では半核が一点のため、水準分離の仮定を除ける。

また、同じ H の Q を引いた源点が滑らかなら、元の点の商像が滑らかであることを証明した。この前向き方向は中心誤差の深さを要せず、核内の点も含む。

## 実例と検証

`y²+xy+7y=x³` の既存の実3点核を7上で使い、源と標的の臨界中心および中心誤差の深さを仮定して、特異な核外点の商像の滑らかさと半核水準の一致の同値を検査した。深さや中心の存在をこのスモークが新たに証明したわけではない。

- `./lean-build.sh DkMath.Lib.NumberTheory.WeierstrassVeluNodalValuation`
- `./lean-build.sh DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalLevels`
- `./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNodalLevels`
- `lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032NodalLevelsAxioms.lean`

19 宣言の公理監査は `propext`, `Classical.choice`, `Quot.sound` のみで、`sorryAx` を含まない。フルビルドと全テストはユーザー側の分担とする。

## 残る境界

目標の `φ(P) ∈ E'₀ ↔ ∃ Q ∈ H, P−Q ∈ E₀` は未証明。今回の水準一致だけでは、同じ節点の二つの枝のどちらに P があるか分からず、P−Q または P+Q が滑らかであることまでは導けない。模範解答の枝の二分と軌道比較の対応部分が必要である。

また、特異核点の中心距離の水準分離と `v(4ε)<v(X_Q)²` を一般の奇素数核から供給する工程、標的臨界中心の存在を同じ特異核側で内部供給する工程も残る。判別式深さ、q=p、剰余点の全体持上げ、Mazur Step Three に相当する大域入力と一般 hno は未完成である。
