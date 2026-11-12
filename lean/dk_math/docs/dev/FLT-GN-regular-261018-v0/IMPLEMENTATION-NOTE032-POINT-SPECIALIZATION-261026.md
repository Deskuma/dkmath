# NOTE-032 — 実点への特殊化と2捩れ三根判定

2026-10-26 JST。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `a212cc31359647f7b1ea36b09bf34d8a2d5d3b04`、作業ツリーはclean。
細かな枝番は追加せず、評価・有限座標・反転・三根判定・条件付き全点写像を一括実装した。
記述は従来の「完了・条件付き・未完了」に戻した。

**同じX_H,Y_Hの実点での有限値、実点座標和との一致、方程式・軌道不変性・反転公式、
元の反転固定点から標的2捩れ三次式の根への着地を証明した。**
同じ三つのx値の分離を入力すれば、同じ標的モデルのΔ≠0へ接続できる。
ただし分離そのものは未供給であり、標的楕円性やisogenyを無条件に完成したとはしない。

## 1. 今回の到達点

| 項目 | 状態 | 正確な内容 |
| --- | --- | --- |
| 全点の正則関数の評価 | 完了 | 各Pでv_P(f)≤1なら、fに合同な係数体元cが一意に存在 |
| 評価準同型 | 完了 | 実際の正則部分代数から係数体への全射AlgHom、和・積・定数・零点・平行移動と整合 |
| 同じX_H,Y_Hの実点特殊化 | 完了 | Hの外で有限値を構成し、実点の正規化座標和と一致 |
| 同じ標的方程式 | 完了 | 全てのP∉Hで、二つの有限値が同じkernelModelの方程式を満たす |
| 同じ核・反転との整合 | 完了 | H軌道で一定、xの反転不変性、yの−Y−a₁X−a₃公式 |
| 反転固定点の像 | 完了 | 特殊化xが同じ標的の2捩れ三次式の根となる。標的楕円性は不要 |
| 三根からのΔ判定 | 条件付きで完了 | 三つの実際の反転固定解のx値の分離を入力すればΔ≠0 |
| 全点関数 | 条件付きで完了 | 標的IsEllipticを入力し、H上はO、Hの外は同じ有限値の点へ送る |
| 全点関数の零ファイバー | 条件付きで完了 | 上記と同じ入力の下でφ(P)=O ↔ P∈H。H軌道で一定 |
| 標的楕円性の無条件供給 | 未完了 | 奇素数核について実際の三つのx値を分離する証明が残る |
| isogeny | 未完了 | 全点関数の加法性、代数曲線の正則写像としての接続、同変性などが残る |
| 標的零成分輸送・hno | 未完了 | 源のhratを標的へ流用しない |

全点関数の零ファイバーと `AddMonoidHom.ker` は区別した。
今回の `kernelPointMap` の型は関数であり、群準同型ではない。

## 2. 所有者と一般性

| 所有者 | 定理 / 定義 | 責務 |
| --- | ---: | --- |
| [EllipticPointEvaluation](../../../DkMath/Lib/NumberTheory/EllipticPointEvaluation.lean) | 17 / 3 | 全点での正則関数の有限評価と評価AlgHom |
| [WeierstrassTwoTorsionSeparation](../../../DkMath/Lib/NumberTheory/WeierstrassTwoTorsionSeparation.lean) | 3 / 0 | 反転固定解の根への着地、相異なる三根からΔ≠0 |
| [EllipticFiniteKernelSpecialization](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelSpecialization.lean) | 17 / 3 | 同じ有限核の実点座標・反転・根・条件付き全点関数 |
| [FreyFiniteKernelSpecialization](../../../DkMath/FLT/FreyFiniteKernelSpecialization.lean) | 5 / 3 | 同じSource・直線・実点核への接続 |

本体4所有者、42定理・9定義、659行。
Lib公開宣言に `[DkMath.Lib]` と日本語教科書docstringを付け、import直後にファイルマーカーを置いた。
Libから研究層への逆依存はない。

Kは体、kはその代数閉包、Eは同じK上の楕円曲線、Fは同じ幾何学的関数体。
評価そのものには標数0を要求しない。有限核の実点座標和・平行移動・反転公式も任意の標数を扱う。
同じkernelModelを使う方程式と全点関数では、前回と同じ標数0の条件を保持する。
一般の三根判定は任意の体上で2≠0を明示する。反転固定解が根となる恒等式にはその条件も不要。
Source側の非零2捩れ点の核外判定ではpが素数、p≠2を使用する。

## 3. 評価を、剰余体の未証明な同一視なしに作る

Pの付値をvとする。まず `transEquiv (-P) x` はPで極位数2を持つ。
これは既存の全点付値の平行移動輸送でOの一般x座標へ戻るためである。
この超越関数を用い、正則fについて二つの場合を扱った。

```text
v(f)<1 : c=0
v(f)=1 : 既存の最高項相殺定理で v(f−c)<1 となるc∈kを得る
```

非零定数の付値は1なので、異なる定数二つが同じ点で合同になることはない。
従ってcは一意である。この存在と一意性から `value E P f hf` を構成した。
入力hfはv_P(f)≤1の証明であり、極に有限値を割り当てる定義にはしていない。

同じ点で正則な元の部分代数 `regularAlgebra E P` を作り、
和・積・定数の局所合同から実際の `evalHom E P : regularAlgebra E P →ₐ[k] k` を構成した。
各定数関数がその定数へ戻るので全射である。
また有限値が0であることとv_P(f)<1の同値、一般x,yが実点のx,yへ戻ることも証明した。

一般のWeierstrass方程式をこの部分代数で読み、評価AlgHomを実際に適用することで、
正則な二関数の方程式を有限値へ特殊化できる。
この段階の結論はEquationであり、標的全体のNonsingularではない。

## 4. 同じ有限核の実点座標へ戻す

Hの外のPでは、全てのQ∈HについてP+Q≠Oである。
従って一般座標の有限評価を各平行移動項に適用し、和と補正定数を保持して

```text
kernelXAt(P) = Σ(Q∈H) xc(P+Q) − Σ(Q∈H) xc(Q)
kernelYAt(P) = Σ(Q∈H) yc(P+Q) − Σ(Q∈H) yc(Q)
```

を証明した。関数体の二関数と別のVélu座標を新しく選び直してはいない。
Oに便宜的な座標0を置くことは補正和のためであり、極の有限評価としては使わない。

Hの元を足す操作は添字の置換となるため、両値は同じH軌道で一定である。
Q↦−Qの置換から、実点での反転公式

```text
kernelXAt(−P) = kernelXAt(P)
kernelYAt(−P) = −kernelYAt(P) − a₁ kernelXAt(P) − a₃
```

も得た。a₃の復元には前回の `kernel_coordinate_correction` を再利用した。
有限和の全項を有限点の公式へ誤って代入せず、Oの一項の補正を維持している。

## 5. 模範解答から取り込んだ三根判定

模範解答の
[標的判別式の証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero.lean)
では、源の2捩れ三次式の相異なる三根を標的へ移し、三根が相異なることから標的Δ≠0を示していた。
Git blobは `f66586eb1bb501437c601e7af2bd9a79c0f77a48`。

DkMathではまず任意のモデルWの実際の方程式解について

```text
y = −y−a₁x−a₃
⇒ (W.twoTorsionPolynomial.toPoly).eval x = 0
```

を恒等式で証明した。非特異性を示す前なので、W.PointやE[2]を入力にせず、
Equationと反転固定条件で記述している。

相異なる三根の多重集合を実際のrootsへ包含し、三次の次数上界でrootsの全体と一致させる。
Cubicの根と判別式の定理、`twoTorsionPolynomial_discr` からW.Δ≠0を得る。
この三根の議論を再構成した所有者には、Anthropicの著作権・Apache-2.0・既存NOTICEへの参照を保持した。
外部のP2M/Definitions/Theoremsはimportしていない。

同じ有限核では、元のP∉Hが−P=Pを満たせば、上の実点反転公式によりその像が反転固定となる。
方程式は既に特殊化できるので、**根への着地は追加providerなしで内部供給できた。**
同じSourceでは、p倍で消えるpointSubgroupと2倍で消える非零点の共通所属を、
addOrderOfがpと2の双方を割ることから排除した。p≠2では「核の外」も内部供給できる。

## 6. 三根の分離が、なお必要な理由

[根分離の模範証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots.lean)
のGit blobは `7d20d1868f13706680f16addb3fdaaeb58be9c51`。
その核心は、異なる2捩れ点の半軌道からx値の集合を作り、
もし像が一致すれば同じ有理式のファイバーが分子の次数より多くの相異なる根を持つ、という計数である。
明示的Vélu有理式と奇巡回核の代表系を使っており、既存のDkMathの任意核の座標和へはそのまま代入できない。

前回の関数体次数2|H|は既に供給済みだが、これを実点の有限ファイバーの個数上界へ使うには、
分母を払った多項式の次数と、今回の評価値との整合を証明する必要がある。
今回の三根分離はこの証明を仮定へ隠すための完成扱いではなく、未供給の入力として明示した。

次に採るDkMathでの接続方針は次のまとまりである。

1. 反転不変なX_Hを、元のxの単純体k(x)内の有理関数として実現する。
2. 既存の関数体次数とRatFuncの分子分母次数公式から、分母を払ったファイバー多項式の次数を得る。
3. 今回の実点評価をその多項式の根へ接続し、奇数核の二つの2捩れ半軌道の計数で分離する。
4. 今回の三根判定へ接続して標的楕円性を供給する。その後、全点関数の加法性・正則写像との整合へ進む。

一般の商スキーム・因子・Pic0理論を一括移植する経路も調査した。
[全点群準同型の模範証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean)
は、場所の制限、ノルム公式、Pic0の押し出しを経由して加法性を得ている。
今回はその大きな基盤を移植せず、同じDkMath付値と有限和を使う実点特殊化を先に完成した。

## 7. 具体例・境界・指数37

[通常テスト所有者](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelSpecialization.lean) と
[独立した境界検査](evidence/Note032PointSpecializationBoundary.lean) は、マーカー以外で同じ本体を持つ。

- 前回と同じ実曲線y²=x³−x、Q=(1,0)、H={O,Q}、R=(−1,0)。
- 一般座標の評価は(−1,0)。源の群法でR+Q=(0,0)を計算する。
- 同じ実点座標和から、標的座標は(−2,0)となり、同じモデルの方程式と2捩れ三次式を満たす。
- Q上には極があるため、有限評価に必要な正則性の証明を供給できない。
- 元の曲線の三つの反転固定解(0,0),(1,0),(−1,0)で三根判定を検査する。
- 尖点y²=x³では三つの分離した反転固定解を供給できないことを検査する。
- 自明核では前回のモデル同一性から標的楕円性を実際に供給し、全点関数の零ファイバーを検査する。
- **偶数核の境界**: 異なる実点R,R+Qの特殊化x値がともに−2となる。
  従って三つの2捩れ像の分離を任意の有限核へ無条件には拡張できない。

[Source37の検査](evidence/Note032PointSpecializationSmoke.lean) では同じSource・L・Pについて、
方程式、根への着地、非零2捩れ点の核外判定、分離条件からのΔ≠0、
標的楕円性を入力した全点関数の正確な零ファイバーを検査した。
Source、直線、三つの分離した像、isogenyの存在を新たに主張しない。

## 8. 実施済み検証

- `lake build DkMath.FLT.FreyFiniteKernelSpecialization`: 成功、4088 jobs、警告0。
- 独立境界Lean: 11定理、成功、警告0。
- Source37のLean: 5定理、成功、警告0。
- 本体51宣言＋境界11宣言＋Source37の5宣言、計67宣言の公理監査。
  `propext / Classical.choice / Quot.sound` の範囲内。
- 禁止構成・外部証明import・Lib逆依存・教科書docstringと昇格マーカー・ファイルマーカー・
  入口登録・既存所有者と直前契約の保持・参照リンク・JSON・差分の空白を検査。

入口は `DkMath.Lib`、`DkMath.FLT`、`DkMathTest` に登録し、静的に確認した。
利用者との分担に従い、フル/ルートビルドと `lake test`、`DkMathTest` 全体ビルドは実行していない。
[検証記録](evidence/validation-note032-point-specialization.txt)、[構造化証拠](evidence/note032-point-specialization.json)。
