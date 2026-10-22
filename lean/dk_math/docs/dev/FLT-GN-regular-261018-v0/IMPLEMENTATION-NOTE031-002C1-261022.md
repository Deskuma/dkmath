# NOTE-031 第5部: 一点の滑らかな還元から実際の慣性固定へ

日付: 2026-10-22（JST）。**031-002Cの最初の区切り、031-002C1を実装した。**
剰余曲線全体が特異でも、当該点が滑らかに還元するなら、prime-to-q torsion点は慣性に固定される。
前回の差点の極と座標整性の証明を一般化し、同じ実際のFrey残余点へ接続した。

特異点へ落ちる零成分外の点、零成分部分加群の構成、乗法的還元の全点固定は未完成である。
031-002全体、031-003〜005、hcases・hno、無条件既約性・一般FLTを閉じたという主張ではない。

## 1. 今回の切り分け

031-002Bはq∤abcの良還元を扱った。次のq∣abcでは剰余判別式が零となる。
しかし前章の証明で曲線全体の非特異性を使ったのは、一点での偏微分の非同時消滅だけだった。
そこで今回のC1は、この一点の条件で零成分側の点の固定を先に証明する。

公開した条件は、整座標の剰余点が非特異であることを文字通り表している。
零成分全体の加法閉性や部分加群としての同定はまだ証明していないので、
本体APIでは`HasSmoothReduction`という座標条件を使い、零成分部分加群の存在を仮定に隠していない。

## 2. 教科書API

本体に公開宣言12個（定義2個・定理10個）、回帰に8個を追加した。
全てに教科書docstringを付け、各新規Leanファイルのimport直後に指定の`#print "file: ..."`を置いた。

| 位置 | 追加内容 |
|---|---|
| `EllipticGoodReductionSeparation` | `SmoothCoordinates`、`HasSmoothReduction`、零点・有限点・非整座標・良還元の基本補題、一点の滑らかさによる偏微分・傾き・和の極 |
| `EllipticGoodReductionInertia` | `torsion_eq_of_coordinate_congruence_of_smooth` |
| `EllipticSmoothReductionInertia` | `fixed_of_inertia_of_smooth_reduction` |
| `FreySmoothReductionInertia` | `Source.residual_fixed_of_smooth_reduction` |

`SmoothCoordinates W x y`は、x,yが付値環Aに属すなら、その剰余座標がWの剰余曲線の非特異点となる条件である。
`HasSmoothReduction W P`は、Pを有限座標で表示できる各場合にこの条件を要求する。
無限遠点では自明であり、xが非整の点も含める。形式群側の非整座標の枝を定義から削っていない。
prime-to-q torsionへの適用では、既に証明済みの座標整性から有限点の座標が整となるので、
この条件を実際の剰余偏微分の非同時消滅として利用する。

この座標条件の定義は一般のV上の点を受け付けるが、**固定定理は必ずW.map A.subtype = Vを要求する**。
異なる曲線の滑らかさを流用する入口にはしていない。

Freyの公開定理は次の形である。

```text
[Fact p.Prime], S : Frey.Source p
hq : q.Prime, hqp : q ≠ p
A : ValuationSubring ℚ̄, hA : LiesOverPrime A q
σ ∈ inertiaSubgroupIn A ℚ
P : S.ResidualSpace
hs : HasSmoothReduction (S.valuationModel A) P.val
────────────────────────────────────────────────────────
S.residualRepresentation σ P = P
```

q≠2やq∤abcは必要ない。q∣abcでも、この点の条件hsがあれば適用できる。
モデル一致と指数の単元性は同じSourceの既存定理から供給する。
hsは還元した一点の方程式・偏微分の条件であり、慣性固定・単射性を仮定するproviderではない。
Sourceの整数・共通因子・向き付け・曲線・点は変更しない。

## 3. 証明の短縮

二点P,Qが同じ剰余座標を持ち、Pの還元が滑らかだとする。
P≠Qなら、Pと−Qを結ぶ接線または割線の傾きはAを外れる。
接線の分母に当たるY偏微分が剰余体で消えても、Pの滑らかさからX偏微分は単元となる。
割線の場合は二つの曲線方程式の差を因数分解し、同じ単元の分子を持つ表示へ移る。

従って差点のx座標の二次項が支配し、x(P−Q)もAを外れる。
しかしnP=nQ=0かつnがAの単元なら、実際の差点P−Qもn-torsionであり、031-002Aの座標整性に反する。
従ってP=Qである。ここで曲線全体の良還元は一度も必要ない。

慣性固定ではQ=σPと置く。慣性は剰余体を固定するので座標が合同になる。
滑らかさを知っているPを第一点に取り、必要な差の向きは非単元集合の負号閉性でそろえる。
σPの滑らかさの輸送や、零成分の加法性を先に証明する必要はなかった。
無限遠点は別の枝で直接固定される。

031-002Bの既存APIは、良還元からこの一点の条件を供給する特殊化として維持した。
証明の共通部分は一度だけ実装し、前回の依存監査も共通補題への経路に合わせて更新した。
還元写像の全点群上の加法準同型や形式群の帰納法は、今回も構成していない。

## 4. 回帰

前章と同じ曲線

\[
y^2+xy=x^3+4x^2+x,\quad \Delta=225,\quad c_4=241
\]

を使う。3上ではΔ=0、c₄≠0であり、剰余曲線は特異だが乗法的還元に対応する形を持つ。

- (0,0)は滑らかで、元の実際のE[2]の非零点である。
  任意の3上の付値環と任意の慣性元について、この同じ点が新定理で固定される。
- 前回の二点P=(−1/4,1/8)、Q=(−4,2)の共通の剰余座標(2,2)は曲線上の特異点である。
  Qの座標は任意の3上の付値環で`SmoothCoordinates`を満たさないことも証明した。
  単射性が破れた境界を今回の仮定から除外する。
- 同じSource 37のq=3、q∣abcで、c₄の付値が1であることと、滑らかに還元する同じ残余点の慣性固定を接続した。
  SourceやFermat反例の存在は主張しない。

この非零2-torsion点は有理点でもある。回帰は新しい局所定理を通る依存を監査するが、
この点の固定だけが非有理torsionの存在や乗法的還元での全点固定を示すわけではない。

## 5. 模範解答との対応

[零成分の模範解答](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean)
の`HasNonsingularReduction`と、その零点・有限点・非整座標・良還元の基本補題を参考にした。
前回抽出した接線・割線の補題を、一点の非特異性へ一般化した。
該当する既存モジュールにApache-2.0・著作権・変更内容・LICENSE/NOTICEの所在を保持した。
新しい固定証明はDkMathの座標整性と同じ実際の表現から再構成した。

[零成分外の固定の模範解答](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd.lean)
も依存を確認した。この部分はまだ移植していない。
その証明は、節点の臨界中心、中心からの深さ、同じ深さでの二つの枝、判別式付値のp可除性を組み合わせる。
今回の滑らかな点の固定を、その外側の枝へ無条件に延長することはできない。
取得済み読取専用キャッシュのblob SHAと利用範囲は[出典台帳](evidence/upstream-note031-002C1.json)に記録した。

## 6. 次の境界

次は031-002C2として、乗法的還元の特異点に対応する臨界中心を作り、
その座標の慣性固定、非特異な二次項、判別式の付値を同じ中心に結ぶ段階が適切である。
その後、零成分外のtorsion点の深さ・枝の比較と、p∣v_q(Δ)をつないで全点の固定へ進む。

C1は滑らかな還元を持つ点の固定までであり、零成分部分加群の構成・全点固定・C全体の完了ではない。
031-003の素数2、031-004の素数pでの統一した側の選択、031-005のhcases統合も未完成である。

## 7. 検証

新規12宣言・回帰8宣言の公理監査、主要8経路の型・opaque本体監査、公開入力3件の検査が成功した。
許容公理は`propext`・`Classical.choice`・`Quot.sound`だけである。
前章の良還元の監査も成功し、共通補題への一般化後も従来の経路が維持されている。

集中ビルドは3,188ジョブ、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`は11,723ジョブで成功した。
テスト入口の直接検査、通常ルート`import DkMath`のスモーク、マーカー照合、docstring・禁止構文・体裁検査、
`git diff --check`も成功した。新規コードに警告・sorryはない。
全体ビルドには既存の無関係な5件のsorry警告が再掲された。
コマンド・版・監査結果・残る境界は[検証記録](evidence/validation-note031-002C1.txt)に記録した。
