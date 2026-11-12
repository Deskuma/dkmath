# NOTE-032 同じ有限核の整数標的・変数変換・有理捩れ像

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 今回の到達点

**構成済みのℚ係数標的から、実際のℤ係数モデルを構成した。同じ点準同型を移し、核H・全射性・Galois同変性・非零有理p捩れ像を保持した。**

源のSource、残余直線L、実点核H、前回の既存ℚ係数標的Tと準同型φを維持する。整数標的はTの共通分母から定まり、変数変換による明示的な加法同型を通してφとの対応を証明した。整数モデル・点同型・核・同変性を外部providerにしていない。

これは整数係数化と点の輸送の一括実装である。最小モデル、元の源から商を取る前後の局所還元保持、零成分輸送、一般hnoは今回の結論に含めない。

## 1. 重み1,2,3,4,6による整数化

任意の有理係数Weierstrass曲線Wについて

```text
d = den(a₁) den(a₂) den(a₃) den(a₄) den(a₆)
```

と定める。分母は全て正なのでd≠0であり、各係数の分母はdを割る。

整数係数は存在定理で選ぶのではなく、重みwに対して

```text
weightedCoefficient(q,d,w) = d^(w−1) (d / den(q)) num(q) ∈ ℤ
```

と構成する。w≥1、den(q)∣dなら、この整数をℚへ戻した値はd^w qと等しい。

従って整数曲線Iの係数は

```text
(d a₁, d² a₂, d³ a₃, d⁴ a₄, d⁶ a₆)
```

である。C=(d⁻¹,0,0,0)を同じ有理変数変換とすると、公開等式は

```text
I.map ℤ→ℚ = C • W
```

となる。元の点を整数化モデルへ送る座標はx'=d²x、y'=d³yであり、戻す座標はx=d⁻²x'、y=d⁻³y'である。

同じ係数等式とMathlibの不変量の変換公式から、ℚ上で

```text
Δ(I) = d¹² Δ(W)
c₄(I) = d⁴ c₄(W)
c₆(I) = d⁶ c₆(W)
```

を証明した。Wが楕円曲線ならΔ(I)≠0であり、Iをℚへ戻した曲線は楕円曲線となる。**ℤ上でΔ(I)が単元であるとは主張していない。**

## 2. 一般の変数変換と点加法同型

`WeierstrassVariableChange`と`WeierstrassVariableChangeHom`は、一般の体上のC=(u,r,s,t)について実際の座標変換を扱う。

```text
x = u²x' + r
y = u³y' + u²sx' + t
```

曲線方程式の差はu⁶倍となり、偏微分の比較にu³・u⁴の重みが現れる。これにより、変換前後の非特異性を同値にし、Oを含む実点の往復写像を構成する。

加法性は、反対点となる場合とそれ以外を分ける。後者では弦と接線の傾きがu倍にsを加えた値へ変わり、和の二座標が同じ変換に従うことを計算する。これにより、点の同値を実際の加法同型へ昇格した。

この一般層は代数閉性・標数0・楕円性を必要としない。一般のWeierstrass曲線の非特異点群に対する定理である。

## 3. 有理点と幾何学的点の整合

`WeierstrassVariableChangeGalois`は、元の体の変数変換Cを代数閉包へ写して、同じ幾何学的点の加法同型を構成する。係数u,r,s,tは絶対Galois作用で固定されるため、実際の座標公式からGalois同変性を証明できる。

さらに、有理点の同型と幾何学的点の同型が基底変換と可換であることを、モデルの等式による輸送も含めて証明した。

`WeierstrassIntegralModelTransport`は、今回の同じ整数化モデルについて

```text
e_rat : I_ℚ(ℚ) ≃+ W(ℚ)
e_geom : I_ℚ(ℚ̄) ≃+ W(ℚ̄)
e_geom(baseChangePoint(Q)) = baseChangePoint(e_rat(Q))
```

を公開する。逆方向にも同じ可換性が成立する。したがって、元の非零有理n捩れ点Rをe_rat⁻¹(R)へ移すと、非零性・n倍零・元の同じRへ戻る等式を保持する。

**整数係数曲線上の有理点であり、任意の像点の座標が整数になるとは主張していない。**

## 4. 同じSource・同じ核・同じ既存標的への接続

`FreyFiniteKernelIntegralModel`では、既存の同じ標的

```text
T = S.residualDescendedKernelModel L hline hstable
```

に上の一般構成を適用し、実際のℤ係数曲線`residualIntegerKernelModel`を得る。整数化した同じ準同型は

```text
φ_int = e_geom⁻¹ ∘ φ
```

である。公開した内容は次の通り。

| API | 証明した内容 |
| --- | --- |
| `residual_integer_kernel_model_discriminant` | 同じΔのd¹²倍の公式 |
| `residual_integer_kernel_model_discriminant_ne_zero` | ℤモデルのΔ≠0 |
| `residual_integer_kernel_model_isElliptic` | ℚへ戻した整数標的の楕円性 |
| `residualIntegerKernelPointHom` | 同じ整数標的への実点加法準同型 |
| `residual_integer_kernel_pointHom_transport` | 元へ戻すと既存の同じ降下点関数の像 |
| `residual_integer_kernel_pointHom_ker` | 核は同じH |
| `residual_integer_kernel_pointHom_surjective` | 全射性 |
| `card_residual_integer_kernel_torsion_image` | 同じp捩れ像の位数p |
| `residual_integer_kernel_pointHom_equivariant` | 標準実点Galois同変性 |
| `exists_rational_torsion_on_integer_kernel` | Cofixedから同じ整数標的の非零有理p捩れ点 |

素数p、p≠2、Lの一次元性、必要なGalois安定性またはCofixed性という前提を保持した。最後の定理では元P∉L、p倍零、非零性、同じφ_int(P)との基底変換等式を全て残している。Cofixed直線そのものの存在を結論しているわけではない。

## 5. 局所比較について今回固定した範囲

任意の有理数体の乗法的付値vについて、v(d)=1なら

```text
v(Δ(I)) = v(Δ(W))
v(c₄(I)) = v(c₄(W))
```

となることを証明した。これは**同じ有理標的を整数係数化する前後**の比較である。元のSource曲線と有限核で割った標的との比較ではない。

dが非単元となる場所で、この等式を無条件に使用してはならない。また、この付値等式だけを最小性や零成分輸送と呼び替えない。

検証例W:y²=x³−x/16ではd=16となり、I:y²=x³−4096xとなる。判別式はΔ(W)=1/64、Δ(I)=4398046511104=2⁴²であり、2進加法的付値は−6から42へ変わる。これを実際にLeanで証明して境界検査とした。

## 模範証明の参照と、今回の整数化との違い

以下の固定blobを取得し、Git blobハッシュを照合した。

- [変数変換の点の同値](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/93376fed97aefdb39c2ff3173013fbb5c1288d12)
- [逆変換の加法性](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/1f15a16634107da49dcfd4ffe712cd5beeb61138)
- [基底変換後のGalois同変性](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/4542e0df895bf2fecf64a96a630035070ddc12b6)
- [安定核のVélu標的の整数化](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/361e2b2a3f20b849206fe0142b58063452ace691)

最初の二つはDkMathの所有名前空間へ移し、importを必要なMathlibだけに絞り、重複していた偏微分公式を再利用し、教科書コメントを加えた。Galois層は具体的な加法同型と基底変換等式として再構成した。これらの所有者にはApache-2.0の出典・blob・既存LICENSE/NOTICEへの参照を残している。外部のDefinitions/Theorems/P2Mライブラリはimportしない。

模範証明の整数化は、整数係数の源と位数pの核に対し、標的係数がp以外で整であることを先に証明する。その結果、p冪だけによる拡大を選べる。**今回の一般共通分母dをp冪だと同一視していない。**

今回は任意の有理モデルに確実に適用できる共通分母法を選び、整数標的の存在と点の輸送を閉じた。p以外の場所で核の座標が整となる定理から、同じ標的係数の分母の素因数を制御する部分は次の仕事として残る。

## 検証と所有者

本体6所有者、公開57定理（lemmaを含む）・20定義、911行。変数変換の所有者には別にprivate補助定理5個があり、公理依存は公開定理から推移的に監査している。

- `WeierstrassVariableChange`
- `WeierstrassVariableChangeHom`
- `WeierstrassVariableChangeGalois`
- `WeierstrassRationalIntegralModel`
- `WeierstrassIntegralModelTransport`
- `FreyFiniteKernelIntegralModel`

対象テストは10定理・3定義。実際の分母16、整数係数−4096、二つの判別式、(1/4,0)と(64,0)の同じ点の対応、非零2捩れ性、基底変換、単元場所での付値比較、2進での付値変化を確認した。さらに前段の同じ非巡回9点核のℚ係数標的の非零有理2捩れ像も、同じ整数化モデルへ移した。

Source37の5定理では、整数標的のΔ≠0、同じ核H、全射性、Galois同変性、Cofixedからの同じ整数標的の非零有理37捩れ点を確認した。

対象検証は、本体`DkMath.FLT.FreyFiniteKernelIntegralModel`、テスト`DkMathTest.Lib.NumberTheory.WeierstrassIntegralModel`のモジュールビルド、Source37の直接Lean検証、95公開宣言の公理監査である。禁止構文・Lib依存方向・教科書docstring・ファイルマーカー・昇格マーカー・入口登録・既存所有者保持・差分空白も検査する。

[evidence](evidence/note032-integral-model.json)と[検証記録](evidence/validation-note032-integral-model.txt)へ結果を記録する。フルビルド・全testは今回実行していない。

失敗と修正: 点群の加法は等号判定のインスタンスを持つため、モデル等式の点同型でその引数を明示した。Pointsと生の幾何学的点型の差には、型付き等式の合成を使った。2進位数の大きな整数例は定義の再帰展開を避け、2の冪に戻して既存の付値の冪公式で証明した。

## 残る数学的境界

完了したのは、実際の整数標的、元との変数変換、同じ実点準同型・核・同変性・全射性・有理捩れ像、および単元倍率の場所でのΔ,c₄の付値保存である。

未完了は、分母の素因数の制御、源から商への局所還元保持、最小モデル、零成分輸送、スキーム射としてのisogeny、標的の有理捩れ像に対する算術的排除、一般hnoである。元Sourceの有理捩れ排除を別の標的へ流用しない。

次は、既存の`EllipticTorsionValuationIntegrality`などを用いて、局所整モデルと同じ有限核の座標の整性から同じ標的係数の整性へ進み、今回の整数化の分母を制御することが候補となる。
