# NOTE-032 同じ有限核の局所整性・半核・分母の素数支持

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 到達点と未解決の境界

**同じ実点核Hの座標と、半核から作るVélu型多項式係数候補は、p以外の全素数住所で整である。既存の同じℚ係数標的の分母がp冪であるという無条件の定理は、まだ得ていない。**

既存標的は、同じ関数体のX_H,Y_Hが満たす方程式から構成されている。今回の多項式候補は、核点の座標から直接作る別の定義である。この二つを同一視せず、同じX_H,Y_Hが候補方程式を満たすという具体的仮定を置いた場合には、既存の一意性・ℚ降下・分母判定を使って、元の標的の共通分母がp冪であることまで証明した。

| 数学的内容 | 今回の判定 |
| --- | --- |
| 同じHの実座標がp以外の全付値環に入る | 証明済み。既存の捩れ点整性を再利用 |
| 奇数核Hの非零反転対から一代表を選ぶ半核 | 構成済み。巡回性不要 |
| 半核と反転半核の分割、2\|半核\|+1=\|H\| | 証明済み |
| 半核によるVélu型多項式係数候補 | 定義済み。2の逆数不要 |
| 候補係数のp以外での局所整性 | 証明済み。2進場所も含む |
| 有理局所整性と既約分母の非可除性 | 正確な同値を証明済み |
| 同じ既存共通分母のp冪性の判定 | 正確な同値を証明済み |
| 同じX_H,Y_Hによる候補の方程式 | **未証明** |
| この方程式から既存標的の局所整性・p冪分母 | 条件付きで証明済み |
| 整数化前後のΔ,c₄の付値保存 | 五係数がその場所で整なら証明済み |
| 源と商の還元比較、最小性、零成分輸送、hno | 未完了 |

## 1. 素数住所と既約分母

有理数r=num(r)/den(r)は既約なので、素数qがden(r)を割ればnum(r)を割らない。従って

```text
0 ≤ padicValRat q r  ↔  ¬ q ∣ den(r).
```

零も含む。q進位数の零に対する規約だけで結論せず、零の分母1も同じ判定に含める。
有限集合Sの外で整であることは、分母の全素因数がSに入ることと同値である。例外が素数p一つなら、同じ分母の素因数分解からden(r)=p^eを取り出す。

さらに、標数0の体Kの付値環Aがq上にあるとき、値群の正規化なしで

```text
(r : K) ∈ A  ↔  ¬ q ∣ den(r)
             ↔  0 ≤ padicValRat q r
```

を示した。全付値環への所属からの逆向きには、既存の `exists_liesOverPrime` で住所qを持つ付値環を実際に供給する。空の全称条件による証明にはしない。

前段の共通分母dは五係数の分母の積であるため、五係数の局所整性とq∤dは同値。従ってd=p^eも五係数のp以外での整性と同値になる。局所整性からv(d)=1を内部供給し、同じ整数化モデルのΔ,c₄の付値保存へ接続した。これは整数化前後の比較であり、源から商への還元比較ではない。

## 2. 同じHの整性と半核

一般のH⊆E(K̄)がn倍で消え、同じ源がA上の整モデルから来て、v(n)=1なら、既存の `torsion_coordinates_mem` によって全ての有限核点の両座標がAに入る。Oの便宜座標は0なので、全核について一つの定理にできる。

Sourceでは、同じ残余直線の点部分群Hの元がp倍で消えることを証明し、既存 `valuationModel` と `valuationModel_map` をそのまま使用した。q≠pならpはq上の付値単元となる。新しい整モデルの存在を入力に置き換えていない。

有限型Hを `Fin (card H)` へ番号付けし、Qと−Qの番号が小さい側を選ぶ。奇数性から非零Q≠−Qが従うので、半核と反転半核は互いに交わらず、O以外のH全体を尽くす。生成元の選択や巡回性は不要。位数9の非巡回E[3]で半核4点、Source37の一次元核で半核18点を確認した。

## 3. 分母なしのVélu型多項式候補

半核の各代表(x,y)について

```text
t(x)   = 6x² + b₂x + b₄
w(x,y) = (2y+a₁x+a₃)² + x t(x)
a₁',a₂',a₃' = a₁,a₂,a₃
a₄' = a₄ − 5Σt
a₆' = a₆ − b₂Σt − 7Σw
```

と置く。wは反転y↦−y−a₁x−a₃で不変。この構成には2や核の位数の逆数がなく、任意の可換環と有限添字集合で定義できる。

任意の環準同型との可換性と、任意の部分環内での係数の閉性を証明した。同じHの座標整性を適用すると、半核候補の係数も同じ付値環に入る。2進場所を例外にする必要はない。

候補の数値例として、y²+y=x³の代表(0,0)からy²+y=x³−7が得られること、先に標数2へ移して構成しても同じy²+y=x³+1となることを確認した。この例は係数算術の検査であり、候補と既存kernelModelの同一性を証明した例ではない。

## 4. 残る一つの関数体恒等式

既存標的の構成 `exists_velu_residual_polynomial` は、同じX_H,Y_Hから残余多項式の次数を落とす方法でa₂,a₄,a₆を得ている。明示的な核点和の係数公式は、既存の定理群にはまだない。

残る接続は、同じ関数体・同じSource・同じ直線についての次の命題である。

```lean
((S.residualHalfKernelPolynomialModel L hline).toAffine⁄
  (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).Equation
    (S.residualKernelX L hline) (S.residualKernelY L hline)
```

この命題を `he` とした
`residual_target_denominator_power_of_polynomial_equation` は実装済みである。
内部では以下を全て供給する。

1. `kernelModel_unique` による同じ候補と既存kernelModelの一致。
2. 同じ半核候補の局所整性。
3. 同じGalois安定核の既存ℚモデルへの係数降下。
4. 指定した素数上の付値環の存在と、有理局所整性への変換。
5. 元の同じ共通分母d=p^e。

従って次の数学的作業は上記の方程式の証明である。候補係数が局所整であることだけから、この方程式や既存モデルの係数の整性を推論することはできない。新しい存在providerに未証明結果を隠す構成もしていない。

## 5. 模範解答からの翻訳と所有者

模範解答 `anthropics/fermats-last-theorem` の `Definitions/Def_WeierstrassCurve_Velu.lean`（blob `35bd154a52a4e83267a2930da2438ece8cc64a54`）の多項式係数公式と、`S_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable`（blob `361e2b2a3f20b849206fe0142b58063452ace691`）の分母素数支持の議論を参照した。読み取ったファイルのblobを検証し、適応した二所有者にはApache-2.0・既存ライセンスとNOTICE・改変範囲を記した。外部の証明モジュールはimportしない。

模範解答は明示的Vélu標的に対して局所整性を適用する。一方、DkMathの現標的は関数体から暗黙的に得たものなので、この違いを閉じる恒等式が必要である。数式の係数構成と有理数の素数支持は中立的Lib所有者へ分離し、同じSourceへの接続だけをFLT側に置いた。

| 所有者 | 公開する内容 |
| --- | --- |
| `RationalPrimeDenominator` | 既約分母・有限例外素数・p冪判定 |
| `ValuationRationalPrimeSupport` | 延長付値環の所属と有理局所整性 |
| `WeierstrassDenominatorSupport` | 同じ共通分母と五係数、整数化前後の付値 |
| `EllipticFiniteKernelHalf` | 同じ奇数核の半核・分割・点数 |
| `WeierstrassVeluPolynomial` | 分母なし係数候補・環写像・部分環整性 |
| `EllipticFiniteKernelLocalIntegrality` | 同じH座標の整性・候補への輸送・方程式からの一意性 |
| `FreyFiniteKernelLocalIntegrality` | 同じSourceと残余核への特殊化、条件付きの既存分母制御 |

## 6. 検証

本体7所有者、公開35定理・8定義。対象テスト7定理・1定義、Source37 smoke 6定理。対象ビルド、公理監査、入口の静的登録、docstring・昇格マーカー・ファイルマーカー・依存方向を確認した。公理監査は57公開宣言を対象とした。

```sh
./lean-build.sh DkMath.FLT.FreyFiniteKernelLocalIntegrality
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032LocalIntegralSupportSmoke.lean
lake env lean tmp/note032-local-integral/Axioms.lean
```

対象範囲は警告なしで成功。既存数学所有者・NOTE-032・前段の報告と検証証跡を変更していない。フルビルドとlake testは依頼に従い実行していない。公開入口の登録は静的確認であり、入口全体のビルド成功を今回の検証とはしない。

検査中、有理分母の正規化を定義的等式として扱えなかった例、古典的等号判定の下で素因数集合の直接計算が停止した例は、明示的な既約分母等式と素数可除性の証明に置き換えた。標数2の数値計算は同じ環写像の等式を介して検証した。

[検証結果](evidence/validation-note032-local-integral-support.txt)・[宣言と公理監査](evidence/note032-local-integral-support.json)。
