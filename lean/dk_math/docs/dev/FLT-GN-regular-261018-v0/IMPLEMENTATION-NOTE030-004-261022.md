# NOTE-030 第2部: 付値0を排除して正の下界へ進む

日付: 2026-10-22（JST）。
前回の030-001〜003に続き、**030-004を実装した**。
同じ正規化Weierstrassモデル上で、素数p≥5の位数を持つ有限点のx付値が1以上であることを証明した。
Source版ではbの偶数性を明示し、同じ有理点Qの1≤k≤p−1の全倍点へ下界を供給する。

本体2ファイルに公開定理9個、回帰の定義・定理22個を追加した。
教科書docstringと指定の`#print "file: ..."`を付け、Lib・FLT・テストの通常入口へ接続した。
030-005〜008、有理p-torsion排除、hratの供給は未完成のままである。

## 1. 読む順序と公開入口

一般の数学は`DkMath.Lib.NumberTheory.WeierstrassPositiveValuation`、
Sourceへの特殊化は`DkMath.FLT.FreyRationalTorsionPositive`に置いた。
本体は前回の`RationalTwoAdicBounds`と`WeierstrassTorsionValuation`を再利用する。

| 一般定理 | 内容 |
|---|---|
| `not_unit_x_of_even_a₂` | a₂が深さ1以上の場合、整なyを持つ有限点のxは単元になれない |
| `double_x_unit` | a₂,xが単元、yが整なら、接線分母は非零、傾きは整、倍点のxも単元 |
| `triple_x_valuation_negative` | xと倍点のx₂が異なる単元なら、同じ座標公式による三倍点のx付値は−2以下 |
| `x_positive_of_prime_order` | 位数p≥5の有限点のx付値は1以上 |
| `nsmul_x_positive_of_prime_order` | p∤kの全倍点について、実際のPoint.xcの付値は1以上 |

前三つの局所補題は有限位数を仮定しない。
特に`double_x_unit`を、反射後の点P+Tがp-torsionであると仮定せず使える形に分離した。
ただし反射自体とその上界への応用は今回実装していない。

## 2. 非負から正へ: a₂の2進的な偶奇で分ける

係数条件は前回と同じ

```text
a₁=1, a₃=a₆=0, Lower 0 a₂, Lower 1 a₄
```

である。有限点Q=(x,y)の位数がp≥5とする。
030-003からx≠0とv₂(x)≥0を得るので、正でない場合は`Exact 0 x`となる。
また`y_integral_of_x_integral`がyの2進整性を供給する。

### a₂が深さ1以上の場合

曲線方程式は

\[
y^2+xy=x^3+a_2x^2+a_4x
\]

である。左辺をy(y+x)と見る。
yが単元なら二つの単元y,xの和は深さ1以上。yが単元でなければ、整性からy自身が深さ1以上となる。
いずれの場合も左辺は`Lower 1`を満たす。

右辺はx³が単元、残る二項は深さ1以上なので、和は`Exact 0`となる。
方程式により同じ有理数が深さ0と深さ1以上を同時に持つことになり矛盾する。
零の便宜的な付値を使わず、LowerとExactを通して打ち消しも扱っている。

### a₂が単元の場合

整なa₂が深さ1以上でなければ、a₂は`Exact 0`となる。
接線分母x+2yは単元xに深さ1以上の2yを加えたものなので単元であり、非零である。
接線の傾きℓは整となる。

倍点のx₂座標を

\[
x_2=-a_2+\bigl(\ell(\ell+1)-2x\bigr)
\]

と書く。整なℓではℓ(ℓ+1)が深さ1以上であり、2xも深さ1以上である。
従って単元−a₂が最低項となり、x₂も単元である。
ここまでが`double_x_unit`で、曲線方程式や有限位数自体はこの局所計算に不要である。

## 3. 同じx座標の例外は、位数の議論で除く

有限点Qと2Qのx座標が等しいなら、曲線上では2Q=Qまたは2Q=−Qとなる。
前者からQ=0、後者から3Q=0が従う。
位数p≥5では、いずれも不可能である。

この例外処理を省くと、後述の実在する3-torsion点を誤って排除してしまう。
`Point.X_eq_iff`に同じ曲線上の非特異性の証拠を渡し、単なる有理数の座標一致から群の等式を飛躍させない。

## 4. 異なる単元x座標から、負の三倍点へ

倍点のy₂も同じ`addY`で計算する。

\[
y_2-y=-x_2-\ell(x_2-x)-2y.
\]

x₂,xは異なる単元なので、x₂−xは非零かつ深さ1以上。
右辺では−x₂が単元、残りは深さ1以上なので、y₂−yは単元である。
従って割線の傾き

\[
\mu=\frac{y_2-y}{x_2-x}
\]

は負の付値m≤−1を持つ。
三倍点のx座標

\[
x_3=\mu^2+\mu-a_2-x_2-x
\]

ではμ²の付値2mが一意に低く、x₃≠0かつv₂(x₃)≤−2となる。
`triple_x_valuation_negative`はこの計算を独立に証明する。
有限点としての3Qとの同一視は、その後に`nonsingular_add`と実際の点群の加法公式で行う。

最後に030-003の`x_nonnegative_of_prime_order ... 3`が、同じ3Qの非負付値を与える。
これにより仮定したxの単元性が矛盾し、1≤v₂(x)が従う。

## 5. Sourceから整数軌道の下界へ

最終入口は`S.orbit_x_lower_bound`である。

```text
S : Source p
hp : p.Prime
hp5 : 5 ≤ p
hbe : Even S.b
Q : S.rationalCurve.toAffine.Point
hQp : p • Q = 0
hQ0 : Q ≠ 0
1 ≤ k ≤ p−1
─────────────────────────────────
1 ≤ padicValRat 2 (k • Q).xc
```

Sのa₂の整性とa₄の深さ1以上は、前回の係数定理から供給する。
Qの位数pはhp,hQp,hQ0から証明し、p∤kは添字範囲から証明する。
任意のp∤kを受け取るAPIとして`nsmul_x_positive_of_prime_torsion`も公開した。

裸のSourceにb偶数を暗黙に追加せず、元のa,b,c、原始性、正規化、同じ曲線、同じQを保持する。
k=0などpで割れる倍点は零点となるため、正の下界を全kへ拡張していない。

## 6. 実際の点で検査した境界

`DkMathTest.FLT.FreyRationalTorsionPositive`に次の回帰を置いた。

1. 前回のモデル(1,3,0,−2,0)の位数3の点Q=(1,1)は、依然としてx付値0を持つ。
   局所の倍点単元補題は適用できるが、2Q=−Qでx座標が同じになるので、割線補題の非零分母条件を満たさない。
2. モデル(1,1,0,−2,0)のU=(1,0)について、2U=(9,−33)、x(3U)=121/64を実際の点群の公式から確認した。
   局所補題で同じ3Uの付値が−2以下となることも確認した。Uの有限位数は仮定・主張していない。
3. モデル(1,−24,0,160,0)上にQ=(4,−20)、R=(16,16)を構成した。
   非特異性を証明し、2Q=R、2R=−Qから5Q=0、Q≠0から位数5を証明した。
   同じモデルの係数条件を供給し、全ての5∤kに正値定理を適用した。
4. k=0ではx付値が0であり、正の下界が偽になることを確認した。
5. Source 37について、同じ点Qと明示されたb偶数条件の下で1≤k≤36の下界を型検査した。

**一般モデル上の有理5-torsionの存在は、Frey Source 5やFLT5の反例を構成したものではない。**
Source 37の入口も、そのようなSourceや非零有理37-torsionの存在を主張しない。
具体例の候補探索に使った有理数計算は証明として採用せず、最終的な座標等式・位数・付値は全てLeanで証明した。

## 7. 原典・依存監査・検証

前段で取得した[原典のfrey_deep_of_order](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean)
（blob `fe61fd5d4f94d55b5a9da38d1541903c84397df0`）を参照した。
一つのFrey専用証明を、係数の偶奇・倍点単元・割線負付値の三つの局所補題と、一般の位数の議論へ分割した。
翻訳した一般モジュールにはApache-2.0の帰属、blob、既存LICENSE/NOTICEのパスを保持した。

`Note030PositiveDependencyAudit`は新規本体9個・回帰22個の公理を検査する。
主要7経路では型とopaque本体まで走査し、三つの局所補題、前章の有限軌道の非負下界、Sourceの係数定理、
実在する位数5の点の倍点計算への到達を確認する。
旧FLT終点、外部P2M/P2MW/FltRegular、Kummer終点、sorryAx、未接続のFoldedValuationOrbitを禁止する。
許容公理は`propext`、`Classical.choice`、`Quot.sound`だけである。

focused build（3,155 jobs）、通常ルート・テストを含むビルド（11,677 jobs）、
テスト入口、ルートsmoke、マーカー照合、`git diff --check`は全て成功した。
新規コードに警告はない。全体入口の既存の別モジュールにある`sorry`警告5件は今回の依存監査と区別する。
コマンドと結果は[evidence/validation-note030-004.txt](evidence/validation-note030-004.txt)に記録した。

## 8. 次の開始点

030-005ではT=(0,0)の2-torsionとx(P+T)=a₄/x(P)を証明し、反射v₂(x)↦γ−v₂(x)から上界γ−1へ進む。
P+T自体をp-torsionとはせず、2(P+T)=2Pへ戻す必要がある。
今回の`double_x_unit`は有限位数を仮定しないため、その局所計算にも再利用できる。

現在完成したのは整数核の**下界側**である。
上界、x+2yの正確な付値、倍点・和差の漸化式、整数核への一括供給、有理torsion排除とhratの無条件化は次段階に残る。
