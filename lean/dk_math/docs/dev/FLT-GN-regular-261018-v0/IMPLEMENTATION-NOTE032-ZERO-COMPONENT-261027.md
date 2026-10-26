# NOTE-032 無限遠近傍と特異核側の全零成分輸送（2026-10-27）

## 今回の到達点

同じ源・有限核H・座標X_H,Y_H・実点商写像・付値環標的を維持した。
単元位数の奇数有限核について、非整なx座標の点は同じ商写像の後も非整となり、
xの付値は正確に保存される。実際の還元関数による像もOである。

非零核点が全て特異に還元する側では、源の**全零成分**を同じ付値環標的の零成分へ輸送した。
対象は捩れ点だけでなく任意の実点であり、O・非整座標の点・整な滑らかな点を全て含む。
この制限を実際の加法準同型に構成し、既存商準同型との一致と単射性も証明した。
Sourceでは同じLのDisjoint条件を保ち、悪い奇素数q≠pと2進場所へ接続した。

滑らかな核の側の全零成分輸送、一般の還元可換図式、整数化後の点への輸送、
逆像の零成分判定、Δ深さ、q=p、スキームisogeny、標的有理捩れ排除、一般hnoは未完了である。
付値環標的と整数標的を、点の還元について未証明のまま同一視していない。

## 無限遠近傍の付値計算

整な半核代表(a,b)に対し、xが非整ならv(x)>1なのでv(x−a)=v(x)。
同じ源のVélu補正は

```text
c_Q(x) = t_Q/(x−a_Q) + u_Q/(x−a_Q)^2
X_H(P) = x(P) + Σ_{Q∈halfKernel} c_Q(x(P))
```

となる。t_Qとu_Qは整だから各項の付値は1未満で、有限和も1未満である。
従ってv(X_H(P))=v(x(P))>1が従う。2や3を割る仮定、良還元、節点、完備性は要求しない。

一般点の関数体公式をそのまま有限点へ代入したことにはしない。
`kernelXAt_half`は既存の正規化座標和を実際の点の群法で半核へ分割し、
各点で分母非零を確認する。核座標の整性から、非整なx(P)と各a_Qが異なることを供給する。
核内点やOの便宜座標を有限点の評価へ流用しない。

## 特異核側での短い証明経路

Pが零成分に属し、非零Q∈Hが滑らかに還元しないとする。
もしP+Qが零成分に属すれば、零成分の引き算の閉性からQ=(P+Q)−Pも属し、矛盾する。
従ってP+QとQはともに同じ臨界中心へ還元する。

既存の正規化座標和を使うと

```text
X_H(P) − x(P) = Σ_{Q≠0} (x(P+Q)−x(Q))
Y_H(P) − y(P) = Σ_{Q≠0} (y(P+Q)−y(Q))
```

の各項が付値1未満となる。半核や巡回生成元を選び直さず、全核を添字にした有限和である。
2で和を割らずに、両座標の合同を得る。

整なPでは合同から像の座標整性を得て、前段の「特異核側では源と商の剰余モデルが等しい」
定理により非特異性を輸送する。非整なPは無限遠近傍保存で処理する。
Pが核に入る枝は既存写像のOへの像を使う。

`singularKernelZeroComponentHom`はモデル等式による移送と既存`oddKernelPointHom`を合成し、
上で証明した保存性で零成分へ制限した準同型である。
一般ファイバーへ戻すと同じ既存写像になることも証明した。
その核では滑らかなHの点が必要だが、特異核の仮定によりOしかないので単射となる。
これは剰余点群上の単射性や、零成分全体への全射性の証明ではない。

## Sourceと非空の実例

Sourceの公開終点では、単元位数p、奇数核、座標整性、特異核条件を内部供給する。
悪い奇素数では既存の臨界中心を、2ではp≥5の既存2進幾何を使う。
同じLと零成分p捩れの`Disjoint`は型に保持する。

検証では既存の実3点核O,(0,0),(0,−7)を持つy²+xy+7y=x³を再利用した。
7上で非零核点が特異となる既存定理を使い、数値的なΔ・c₄から臨界中心を内部構成して、
全ての滑らかな実点の像を検証した。
x=1ではy=√17−4の非零実点を構成し、剰余非特異性と像の滑らかさを確認した。
x=1/7でも代数閉包の平方根から実点を構成し、無限遠近傍の像が実際に存在することを確認した。
Source37のスモークだけに依存しない検証である。

## 所有者と模範証明

新規本体は4所有者、18公開定理と1定義である。

- `WeierstrassVeluFormal`: 任意の体・付値環・有限添字での補正和の評価。
- `EllipticFiniteKernelFormal`: 同じ実点の半核表示、付値保存、滑らかさと実際のOへの還元。
- `EllipticFiniteKernelZeroComponent`: 特異核側の座標合同、全零成分輸送、同じ写像の制限と単射性。
- `FreyFiniteKernelZeroComponent`: 同じSourceの任意住所での無限遠近傍保存と、悪い奇素数・2での特異核側輸送。

[模範証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean)
を取得して調査した。実際の取得内容は194234 bytes、Git blob
`ab1aee61bdcfbe439dcf9693d5f1417cacc05b6b`である。
模範証明の主命題は、商の零成分の逆像を源の零成分と核の和で判定する、より強い同値である。
節点の枝・深さ・衝突点の比較まで含む約3600行を今回の前向き輸送と同一視しない。

無限遠近傍の評価を任意体・有限添字へ翻訳した所有者にはApache-2.0、参照blob、変更内容、
既存の`RegularKummer/LICENSE`と`ANTHROPIC-NOTICE`を記載した。
残る所有者は既存DkMath APIを組み合わせた証明で、MITとした。
外部解答モジュールやP2Mコマンドのimportはない。既存数学所有者は変更していない。

## 検証と次の接続

[Source37スモーク](evidence/Note032ZeroComponentSmoke.lean)、
[検証要約](evidence/validation-note032-zero-component.txt)、
[機械可読記録](evidence/note032-zero-component.json)に検証範囲を記録する。
本体と対象テストのモジュールビルドを使い、フルビルド・集約入口ビルド・lake testは行わない。

次は、今回の両座標合同とOへの還元から特異核側の還元可換図式をまとめ、
p以外で単元となる整数化倍率に沿って同じ整数標的の点へ輸送する。
滑らかな核の側には節点比の冪写像の座標公式と、核への衝突点の処理が必要である。
Δの正確な深さと逆像判定のための枝・level比較は、その後も独立した課題として残す。

実行した検証は次の通りで、全て警告なしで通過した。

```text
./lean-build.sh DkMath.FLT.FreyFiniteKernelZeroComponent
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelZeroComponent
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032ZeroComponentSmoke.lean
lake env lean tmp/note032-zero-component/Axioms1.lean
lake env lean tmp/note032-zero-component/Axioms2.lean
```

本体19公開宣言、対象テスト6定理、Source37の3定理の計28宣言を、15・10・3に分散して公理監査した。
依存公理は`propext`、`Classical.choice`、`Quot.sound`だけだった。
ファイルマーカー、Libのdocstringと昇格マーカー、依存方向、入口への静的登録、禁止構文、
既存数学所有者・NOTE・前段証拠の不変性、参照blob・ライセンス、空白とリンクを確認した。
付値環の数値coercion、モデル等式と逆写像、テストの直接import・局所Fintype・剰余castを
明示して初期の型不一致を修正した。未証明の保存性providerは追加していない。
