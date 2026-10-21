# NOTE-030 第3部: 2-torsion反射から両側の境界へ

日付: 2026-10-22（JST）。030-004に続き、**030-005を実装した**。
同じWeierstrassモデル上の実際の点T=(0,0)を構成し、反射x(P+T)=a₄/x(P)を証明した。
有理数の2進付値ではe↦γ−eとなり、既存の負付値排除・正の下界と組み合わせて上界γ−1を得た。
同じFrey Sourceと同じQの非自明な倍点から、整数軌道核の区間条件1≤e(k)≤γ−1を供給する。

本体3ファイルに公開定義・定理21個、回帰に12個を追加した。
全公開宣言に教科書docstring、全新規Leanファイルに指定の`#print "file: ..."`を付けた。
Lib・FLT・テストの通常入口にも接続した。030-006〜008、有理torsion排除・hratは未完成である。

## 1. 読む順序

| モジュール | 内容 |
|---|---|
| `DkMath.Lib.NumberTheory.WeierstrassXReflection` | Tの構成、2T=0、平行移動の群法、実際のx座標の反射、付値の反射 |
| `DkMath.Lib.NumberTheory.WeierstrassTorsionBounds` | 反射後の点の負・零付値を排除して上界を得る。非自明な倍点の両側の境界 |
| `DkMath.FLT.FreyRationalTorsionBounds` | 同じSourceの係数・γを供給する薄い特殊化 |
| `DkMathTest.FLT.FreyRationalTorsionBounds` | 実在する位数5の点、鋭い上界、移動後の位数の誤認防止、Source 37 |
| `DkMathTest.FLT.Note030BoundsDependencyAudit` | 全新規公開宣言の公理、主要経路の型・opaque本体・必須providerを検査 |

## 2. 幾何の核はa₁=1に依存しない

任意の体K上のモデルでa₃=a₆=0、a₄≠0とする。
T=(0,0)は非特異であり、無限遠点と異なる実際の点となる。
a₃=0から−T=T、従って2T=0が従う。

有限点P=(x,y)、x≠0に対し、Tへの割線の傾きはy/xである。
曲線方程式

\[
y^2+a_1xy=x^3+a_2x^2+a_4x
\]

をx²で割り、実際の`addX`公式へ代入すると

\[
x(P+T)=\left(\frac yx\right)^2+a_1\frac yx-a_2-x=\frac{a_4}{x}
\]

が得られる。`addX_origin`はこの体上の計算を証明し、
`add_twoTorsionPoint_x`が`Point.add_of_X_ne`を使って実際の点群の座標へ接続する。
a₁は任意であり、モデル変換や座標の取り替えは行っていない。

座標の式にはx≠0が必要だが、次の群法の等式は全てのPについて成立する。

\[
(P+T)+T=P,\qquad 2(P+T)=2P.
\]

一方、奇数nでnP=0ならn(P+T)=T≠0となる。
**P+Tを同じ奇数nのtorsionと見なしてはいけない。**
この事実を一般定理`odd_nsmul_add_twoTorsionPoint`として公開した。

## 3. 付値の反射から上界へ

有理数モデルでは、`Exact γ a₄`と`Exact e x(P)`から

\[
\operatorname{Exact}(\gamma-e)\,x(P+T)
\]

を得る。非零性も結論に保持するため、零の便宜的な付値で割り算を正当化しない。

上界の一般定理は次の仮定を取る。

```text
a₁=1, a₃=a₆=0
Lower 0 a₂, Exact γ a₄, 1≤γ
p.Prime, 5≤p, addOrderOf Q=p
Q=Point.some x y h
```

上界v₂(x)≤γ−1に反すると仮定し、R=Q+Tと置く。
反射によりv₂(x(R))=γ−v₂(x)≤0であり、2R=2Qである。
位数p≥5から2Q≠0を得るので、Rの接線公式の例外y=negYも除ける。

- **反射後の付値が負の場合**: 030-003の`double_x_valuation_drop`により倍点の付値はさらに2以上下がる。
  しかしこの倍点は元の2Qであり、有限軌道から得た非負下界に反する。
- **反射後の付値が0の場合**: x(R)の整性からy(R)の整性を得る。
  a₂が深さ1以上なら030-004の`not_unit_x_of_even_a₂`で矛盾する。
  a₂が単元なら`double_x_unit`でx(2R)も単元となるが、2R=2Qの正の下界に反する。

従って上界が成立する。R自体に位数pの下界を適用する箇所はない。
負付値の降下・単元倍点という局所計算を前章から独立に再利用できたことが、今回の短縮である。

## 4. 同じSourceから整数軌道の区間へ

公開入口`S.orbit_x_bounds`は次の型を持つ。

```text
S : Source p
hp : p.Prime, hp5 : 5≤p, hbe : Even S.b
Q : S.rationalCurve.toAffine.Point
hQp : p • Q = 0, hQ0 : Q ≠ 0
1≤k≤p−1
───────────────────────────────────────────────────────
1≤padicValRat 2 (k • Q).xc ∧
  padicValRat 2 (k • Q).xc ≤ S.twoAdicGamma−1
```

γは前章と同じ`p·v₂(S.b)−4`であり、係数の正確な付値と1≤γは既存のSource定理から供給する。
p倍零・非零から位数pを証明し、添字範囲からp∤kを証明する。
任意のp∤kを受け取る入口は`nsmul_x_bounds_of_prime_torsion`である。
同じa,b,c、互いに素という情報、正規化、同じ有理モデルと同じQを保持する。
裸のSourceにb偶数やp≥5を暗黙に付加しない。

## 5. 実際の点で確認した内容

前章のモデル(a₁,a₂,a₃,a₄,a₆)=(1,−24,0,160,0)と、位数5の点Q=(4,−20)を再利用した。
γ=v₂(160)=5を非零性とともに証明し、次を検査した。

1. T=(0,0)は非零で2倍零。二回の平行移動は元に戻り、2(Q+T)=2Qとなる。
2. x(Q+T)=40で、x(Q)の深さ2は反射によって5−2=3になる。
3. 5(Q+T)=T≠0であり、移動後の点は5倍零ではない。
4. 全ての5∤kについて、一般定理から1≤v₂(x(kQ))≤4を得る。
5. 2Q=(16,16)のx付値は4であり、上界γ−1は実際に達成される。上界を3へ強めることはできない。
6. T+T=O、O+T=Tを検査し、x=0の原点と無限遠点を反射の分母ガードから区別した。
7. Source 37について、同じ点Qと明示されたb偶数条件の下で1≤k≤36の上下界を型検査した。

一般モデルの有理5-torsionはFrey Source 5やFLTの反例ではない。
Source 37の定理も、そのようなSourceや非零有理37-torsionの存在を主張しない。

## 6. 翻訳元と検証

前段で取得した[Anthropicの原典](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean)
（blob `fe61fd5d4f94d55b5a9da38d1541903c84397df0`）の
`frey_ns00`、`frey_T0_T0`、`frey_addX_T0`、`frey_shallow_of_order`を参照した。
一般の体の幾何と、有理数の付値境界と、Sourceの係数供給へ分割して再構築した。
翻訳した一般モジュールにはApache-2.0の帰属、blob、既存LICENSE/NOTICEへのパスを保持した。

新規本体21個・回帰12個の公理検査と、主要7経路の型・opaque本体の走査は合格した。
許容公理は`propext`、`Classical.choice`、`Quot.sound`のみ。
反射の加法公式、2T=0、負付値降下、単元例外排除、元の2Qの下界、Sourceの係数評価への到達を確認した。
旧FLT終点・外部P2M/P2MW/FltRegular・Kummer終点・sorryAx・未接続のFoldedValuationOrbitは禁止した。
一般Libの主要経路がDkMath.FLTへ依存しないことも確認した。

focused build（3,159 jobs）、通常のルート・Lib・FLT・テスト入口のビルド（11,682 jobs）、
ルートsmoke、テスト入口の直接検査、マーカー照合、`git diff --check`は全て成功した。
新規コードに警告はない。全体ビルドで再掲された既存の別モジュールの`sorry`警告5件は、今回の証明経路とは区別する。

検証のコマンド・結果・依存グラフの記録は
[evidence/validation-note030-005.txt](evidence/validation-note030-005.txt)に置く。

## 7. 次の開始点と未完成境界

次は030-006である。まず同じ点でx+2yの正確な付値を証明し、
非零分母・座標同一性を保持して倍点恒等式と和差恒等式を付値へ翻訳する。
その後030-007でe,A,B,A₁を実際のQから定義し、既存の整数折り返し核へまとめて渡す。

今回完成したのは区間条件であり、倍点・和差の漸化式、整数核への全入力、有理p-torsion排除、
030-008のhrat供給はまだ完成していない。fixed/cofixed二択、cofixed排除、無条件既約性、一般FLTは別の境界である。
