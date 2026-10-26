# NOTE-032 特異核側の還元可換図式と同じ整数標的への点の輸送（2026-10-27）

## 到達点と境界

前章の「同じ付値環商標的で像が滑らか」という結論を、実際の還元点の等式へ進めた。
同じSource・直線L・有限核H・既存実点商準同型を維持し、特異核側の全零成分について
源から商への還元可換図式を証明した。O・有限整点・非整点を含む。

さらに、同じ既存整数化の幾何学的点同型で、滑らかな還元条件を双方向に輸送した。
Sourceでは既存の共通分母d=p^eとq≠pから単元性を供給し、**既存の整数点準同型そのもの**の
像を、同じ整数係数標的の付値環モデルの零成分へ運ぶ一括終点を実装した。
悪い奇素数と2を同じ入口で扱い、p≥5、Lの安定性、Disjoint、源の滑らかさを保持する。

滑らかな核側の全零成分輸送と還元写像、逆像の零成分判定、Δの正確な深さ、q=p、
スキームisogeny、標的有理捩れ排除、一般hnoは残る。
整数化の前後の滑らかさの同値と、源・商の剰余点の一致を区別している。
整数化すると剰余曲線も単元変数変換で変わるので、整数像の還元を元の剰余点と直接等置していない。

## 同じ商写像と還元の可換性

Mを源の整モデル、Uを同じ有限核の付値環標的とする。特異核側では前章により
Uの剰余モデルとMの剰余モデルが等しい。この等式による点の移送を明示して

```text
pointEquivOfModelEq(h_residue) (red_U(φ_H(P))) = red_M(P)
```

を証明した。左右の還元は`modelReduce`を使い、一般ファイバーと整モデルの等式輸送を含む。
全域関数の特異点分岐での既定値に依存した群準同型の主張ではなく、定理の定義域に
源の滑らかな還元条件を残す。

- 核内のP: 特異核の仮定と源の滑らかさからP=O。双方の還元はO。
- 核外で整なP: 既存の両座標合同から像の座標整性と剰余座標の一致を得る。
  源と像の非特異性を使い、便宜座標でなく実際の有限剰余点の等式を証明する。
- 非整なP: 前章の同じx付値の保存により、源も像も実際にOへ還元する。

Sourceの`residual_pointHom_reduction_square_at_bad_place`は同じLのDisjointを保持し、
悪い奇素数の臨界中心とp≥5での2進幾何を内部供給する。

## 単元変数変換と整数化

付値環A上の変数変換C=(u,r,s,t)ではu∈Aˣである。
両座標と逆座標の多項式公式から、座標対の整性が前後で同値となる。
整座標の剰余を取る操作も、同じCを剰余体へ写した変換と可換である。
既存の非特異性の変数変換同値を剰余体で使うと

```text
SmoothCoordinates (C • M) x y
  ↔ SmoothCoordinates M (vcX(C_K,x)) (vcY(C_K,x,y))
```

が従う。2・3の単元性、良還元、捩れ性、完備性は要求しない。
非整座標の枝を除いてから証明したものではない。

有理曲線Wの既存整数化ではC=(d⁻¹,0,0,0)である。
v(d)=1なら、このCはA上の単元変数変換へ持ち上がる。
同じ既存整数曲線をAへ写した`integerValuationModel`がC•Mに等しいことを、
一般ファイバーの係数の一致とA→Kの単射性から証明した。

既存`geometricPointEquiv`の有限点の座標を同定し、Oも含めて

```text
HasSmoothReduction integerValuationModel P_I
  ↔ HasSmoothReduction M (geometricPointEquiv W P_I)
```

を証明した。判別式の付値が一致するというだけの主張ではない。

Sourceの`residual_integer_pointHom_smooth_iff`は、既存整数化同型・係数降下の点同型の
二つの対応式を使い、同じ整数点準同型の像と同じ付値環商準同型の像の条件を結ぶ。
これは任意の実点Pとq≠pで成立し、Disjointは比較自体には要求しない。

`residual_integer_pointHom_smooth_at_bad_place_of_disjoint`では、この同値と前章の保存性を
合成する。整数像や整数モデルを新たに選ばず、前段の未完了だった点の輸送を接続した。

## 実例と仮定の境界

実3点核O,(0,0),(0,−7)を持つy²+xy+7y=x³を再利用し、7上の全ての滑らかな実点で
同じ剰余モデルへの還元可換図式を検証した。臨界中心は数値的なΔ・c₄から内部構成する。
前章で同じ曲線に構成したx=1の非零点とx=1/7の非整点も、この定理の対象である。

別の実例y²+y/2=x³では、共通分母d=2と既存整数モデルy²+4y=x³を実際に計算した。
7上では倍率2が単元である。同じ幾何学的整数化同型の滑らかさの同値を任意の実点で検査し、
非零点(0,0)から滑らかに還元する同じ整数モデル上の非零点を実際に構成した。

2上ではx=1/2が非整だが2²x=2は整になる例を証明した。
単元条件を外して無限遠近傍や整性の同値を主張できない境界を固定している。

## 所有者・検証・次の課題

新規本体は5所有者、15公開定理・2定義。

- `WeierstrassModelReduction`: 同じモデルでの還元と、有限剰余点の等式輸送。
- `EllipticFiniteKernelReductionSquare`: 特異核側の全零成分での実際の還元可換図式。
- `WeierstrassIntegralChangeReduction`: 付値環の単元変数変換による整性と滑らかさの同値。
- `WeierstrassIntegerReductionTransport`: 同じ整数化の持ち上げと、既存点同型での還元条件の同値。
- `FreyFiniteKernelReductionSquare`: 同じSourceの2を含む一括可換図式と、同じ既存整数像への輸送。

既存DkMathのモデル等式、非特異性の変数変換、整数化、前章の座標合同とOへの還元を組み合わせた。
外部解答コードの新たなコピーや外部証明モジュールのimportはない。新規所有者はMITである。
既存数学所有者は変更せず、入口のimportを追加した。

[Source37スモーク](evidence/Note032ReductionSquareSmoke.lean)、
[検証要約](evidence/validation-note032-reduction-square-integer.txt)、
[機械可読記録](evidence/note032-reduction-square-integer.json)に結果を記録する。
フルビルド・集約入口ビルド・lake testはユーザー側の分担を維持する。

次は滑らかな核側の節点比の冪写像と、核への衝突点の処理である。
特異核側で得た「剰余モデルが同じ」という等式は、その側には使わない。
Δ深さと逆像判定に必要な枝・levelの比較、q=pと一般hnoは別の残る課題である。

最終確認は次の対象だけを実行し、全て警告なしで通過した。

```text
./lean-build.sh DkMath.FLT.FreyFiniteKernelReductionSquare
./lean-build.sh DkMathTest.Lib.NumberTheory.FreyReductionTransport
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032ReductionSquareSmoke.lean
lake env lean tmp/note032-reduction-square/Axioms1.lean
lake env lean tmp/note032-reduction-square/Axioms2.lean
```

本体17公開宣言、対象テスト5定理・2定義、Source37の3定理の計27宣言を15・9・3に分散して公理監査した。
依存公理は`propext`、`Classical.choice`、`Quot.sound`だけだった。
Lib依存方向、docstring・昇格マーカー、モジュールマーカー、入口の静的登録、禁止構文、
既存数学所有者・NOTE・前段証拠の不変性、空白とリンクも確認した。
代数閉包の基底変換表記とmapの型の違い、未確定のモデル等式、整数castと付値環coercionは、
型付き等式と既存環写像の公式を明示して修正した。heartbeat上限を引き上げる処置は残していない。
