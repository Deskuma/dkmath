# NOTE-030 第1部: 付値演算・係数・有限軌道の負付値排除

日付: 2026-10-22（JST）。
NOTE-030とINST-030を検討資料として現行コードと照合し、今回は**030-001〜003**を実装した。
8段階の途中で検証できる数学的な区切りを選び、030-004以降は次段階として残す。
新規の本体6ファイル、公開の名前付き定義・補題・定理71個、回帰28個を追加した。
日本語の教科書docstring、指定の`#print "file: ..."`、通常入口への接続を含む。

## 1. 8段階の現在位置

| 段階 | 今回の状態 | 到達点・残る内容 |
|---|---|---|
| 030-001 | 完成 | 有理2進の零を許す下界と正確な付値、和差・積・商・自然数冪・min、単元の法2での性質 |
| 030-002 | 完成 | 同じSourceのa₂の整性、b偶数と原始性からa奇数、a₄の正確な付値γ、p≥5ならγ≥1 |
| 030-003 | 完成 | 有限軌道の最小値原理、負付値の倍点降下、位数p>2の全倍点でx付値が非負、非自明な倍点のx非零性 |
| 030-004 | 未実装 | 付値0を排除し、1≤v₂(x(kQ))へ進む |
| 030-005 | 未実装 | 有理2-torsionによる反射と、v₂(x(kQ))≤γ−1 |
| 030-006 | 未実装 | x+2yの正確な付値、倍点・和差恒等式の付値化 |
| 030-007 | 未実装 | 同じS,Qからe,A,B,A₁を作り、NOTE-029の整数核へ供給して有理p-torsionを排除 |
| 030-008 | 未実装 | 上記の有理torsion排除をFreyStableLineのhratへ供給 |

今回の非負下界だけでは整数核の要求する**正の下界**を満たさない。
局所慣性からのfixed/cofixed二択、cofixed不存在、Frey表現の無条件既約性も別の未完成課題である。

## 2. 読み進める順序

| ファイル（接頭辞 `DkMath.`） | 教科書での役割 |
|---|---|
| `Lib.NumberTheory.RationalTwoAdicBounds` | 零を許す整性と、非零の正確な付値を分ける一般算術 |
| `FLT.FreyRationalTorsionValuation` | 既存の同じSourceから係数の付値を供給する |
| `Lib.Algebra.FiniteOrbitMinimum` | 負の値が下がり続けることを有限性が禁止する一般原理 |
| `Lib.NumberTheory.WeierstrassNegativeValuation` | 方程式・接線・倍点公式から、負のx付値の降下を証明する |
| `Lib.NumberTheory.WeierstrassTorsionValuation` | 一般原理と実際の点群・既存のPoint.xcを接続する |
| `FLT.FreyRationalTorsionIntegral` | 同じSourceの同じ有理点について、係数providerなしで最終下界を得る |

一般算術、有限群論、Weierstrass座標、Sourceへの特殊化を分離した。
Frey専用の仮定を一般補題へ隠していない。

## 3. 030-001: 零の便宜値を、数学的な付値と取り違えない

Mathlibの`padicValRat 2 0`は0である。このため、生の等式v₂(q)=0だけではqが単元とは言えない。
次の二つを定義した。

```lean
Lower n q := q = 0 ∨ n ≤ padicValRat 2 q
Exact n q := q ≠ 0 ∧ padicValRat 2 q = n
```

`Lower`は「零または深さn以上」、`Exact`は「非零でちょうど深さn」である。
零は任意の深さのLowerを満たすが、どの深さでもExactではない。

積の下界は加算でき、商では分母をExactにすることで非零性を確保する。
自然数冪も両方の形式で扱い、q=0,k=0の境界を残した。
`Exact.add_lower`と`Exact.sub_lower`は、低い付値の項と厳密に高い深さの項の和差を評価し、
非零性も同時に証明する。異なる正確な付値には`Exact.add_exact_of_ne`と`Exact.sub_exact_of_ne`を使える。
同じ付値では打ち消しがあり得るため、`Lower.add_min`・`Lower.sub_min`に留める。

さらに、既約分数の分子と分母の互いに素性から、2進単元qのq−1は深さ1以上と証明した。
そこから単元同士の和差、整なqについてq(q+1)の深さ1以上が従う。
これらは次の030-004で、付値0の点を除く際の演算法則になる。

## 4. 030-002: 既存の整数モデルを使う短縮

a₂の整性は上流のmod 4計算を再移植せず、既存の

```text
S.curve_map : S.curve.map (Int.castRingHom ℚ) = S.rationalCurve
```

のa₂成分を取る。するとa₂が整数`S.curve.a₂`の像と分かり、`lower_int`へ渡すだけでよい。
`a₂_twoAdic_integral`は全Sourceに適用でき、b偶数・p素数・p≥5を要求しない。
整数モデルの分母条件はSourceに保持されたままである。

a₄についてはbの偶数性を明示的に要求する。S.coprimeとb偶数からaは奇数となる。
S.a_neとS.b_neで非零性を保持し、aの付値0、冪p、積、分母16の付値4を順に使う。

```text
S.twoAdicGamma := p · padicValInt 2 S.b − 4
a₄_twoAdic_exact hbe : Exact S.twoAdicGamma S.rationalCurve.a₄
```

p≥5なら非零偶数bの付値が1以上なのでγ≥1となり、`a₄_twoAdic_positive`がLower 1を供給する。
この係数評価ではpの素数性やa≡3 mod4は不要である。
裸のSourceからb偶数を取り出したことにはしていない。

## 5. 030-003: 局所降下を有限周期で閉じる

### 5.1 群論だけの最小値原理

`nonnegative_of_strict_drop`は有限集合Sを保存する写像stepと値fを取り、
fが負の時にstepで厳密に下がるなら、S上の全てのfが非負であると証明する。
負の最小値からさらに小さい値ができるため矛盾する。stepの単射性・全射性は不要である。

`nsmul_nonnegative_of_double_drop`はこれをnQ=0の倍点軌道へ適用する。
有限集合range nと、step(k)=2k mod nを使う。剰余を取っても同じ点であることをnQ=0から証明する。
これは楕円曲線にも付値にも依存しない一般可換群の定理である。

### 5.2 接線と倍点の局所計算

有理数上の一般モデル

\[
y^2+xy=x^3+a_2x^2+a_4x
\]

に対し、a₁=1、a₃=a₆=0、Lower 0 a₂、Lower 1 a₄を明示する。
`WeierstrassNegativeValuation`はFreyの整数や指数を仮定しない。

xの正確な付値をe<0とすると、右辺ではx³が一意に低い付値3eを持つ。
左辺のy²+xyを比較して、y≠0、v₂(y)<e、2v₂(y)=3eを導く。
接線の分母はx+2yであり、倍点が有限点であることに相当するy≠negY(x,y)から非零性を確保する。
接線の傾きをℓとすると、その分子の付値は2eとなり、傾きの平方が倍点公式の一意な最小項になる。

`double_x_valuation_drop`の結論は

```text
x(2P) ≠ 0 かつ v₂(x(2P)) ≤ e−2
```

である。群の有限性はこの局所計算に使わない。

### 5.3 同じ点の有限軌道への帰還

位数p>2が素数なら、非零なkQの2倍も非零である。
p∣2kからp∣kまたはp∣2となり、両方を排除できるためである。
これが上記の接線分母の条件を供給する。

`x_nonnegative_of_prime_order`は実際のkQの既存の`Point.xc`を値関数として使う。
負の付値は倍点でさらに下がるため、有限軌道の最小値と矛盾する。
結果として全てのkについてv₂(x(kQ))≥0が得られる。
無限遠点のxc=0という便宜値は既存定義のままであり、その点を有限点と見なしてはいない。

x=0の有限点は曲線方程式からy=0となり、2倍で零となる。
従って位数が2より大きい有限点のxは非零である。
`nsmul_x_nonzero_of_prime_order`は、p∤kならkQも位数pを持つことを利用し、そのx非零性まで供給する。
非負付値と非零座標を別々の定理として保持し、後続の付値の積・商公式へ渡せる。

## 6. Sourceの入口

`FreyRationalTorsionIntegral`の終点は次の形である。

```text
S : Source p
hp : p.Prime
hp5 : 5 ≤ p
hbe : Even S.b
Q : S.rationalCurve.toAffine.Point
hQp : p • Q = 0
hQ0 : Q ≠ 0
──────────────────────────────────────────
∀ k, 0 ≤ padicValRat 2 (k • Q).xc
```

定理名は`S.x_nonnegative_of_prime_torsion`。
位数pであることは素数性とhQp,hQ0から証明し、係数の下界もSから供給する。
追加の位数・係数・降下providerは入力に取らない。
元のa,b,c、原始性、正規化、同じ曲線、同じQを保持する。

今回新たな反例の向き付け処理は追加していない。
必要なhbeは既存の`FreyCounterexample`の向き付け付き入口から得る設計のままであり、公開仮定に残す。

## 7. 実在する点による境界の回帰

`DkMathTest.FLT.FreyRationalTorsionIntegral`には、零・打ち消し・37乗・分数・有限性に加え、次を含む。

- 既存の実在Source 2（a=4,b=3,c=5）ではa₂=−2であり、bが奇数でもa₂の整性を適用できる。
- 指数1の実在Source（a=−1,b=16,c=15）ではbが偶数で、同じ係数定理からγ=0とa₄の付値0を確認する。
  係数の正確な評価にはp≥5が不要である一方、γ≥1には指数条件が必要である。
- 一般モデル(a₁,a₂,a₃,a₄,a₆)=(1,8,0,2,0)上のP=(−1/4,1/8)は非特異な非零2-torsion点で、x付値は−2。
  a₂整、a₄深さ1という係数条件も満たす。従って素数2を一般の非負付値定理へ含めることはできない。
- 一般モデル(1,3,0,−2,0)上のQ=(1,1)では、実際の倍点公式から2Q=−Qを証明し、位数3を得る。
  x付値は0だが、一般の有限軌道定理は全倍点に適用できる。非負と正の下界の違いが実例でも見える。
- Source 37の係数・有理点の入口も型検査する。この検査はSource 37や非零有理37-torsion点の存在を主張しない。

2点の例はFrey反例の代替ではなく、一般の座標定理の仮定・結論の境界を検査するためのものである。

## 8. 原典・帰属と検証

今回、一次資料の[Anthropicの有理p-torsion排除の証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean)を取得し、
返されたblobが`fe61fd5d4f94d55b5a9da38d1541903c84397df0`であることを確認した。
一般付値・局所座標計算・有限軌道の接続を翻訳した3ファイルに、Apache-2.0の帰属、blob、既存LICENSE/NOTICEへのパスを明記した。
有限集合の最小値の分離と、整数モデルからの係数bridgeはDkMathで記述した。
P2MWのマクロや上流モジュールそのものはimportしていない。

`Note030DependencyAudit`は本体71個・回帰28個の公理を検査し、主要9経路では型とopaque本体を含む依存グラフを走査する。
旧FLT終点、外部P2M/P2MW/FltRegular、Kummer終点、sorryAxを禁止する。
今回は未接続の`FoldedValuationOrbit`も監査経路で禁止し、最小値原理・実際の倍点計算・係数bridgeを通ることを必須にした。
一般付値・有限群論には楕円曲線やFreyへの依存を許していない。
公理は`propext`、`Classical.choice`、`Quot.sound`のみを許す。

focused build（3,152 jobs）、通常ルート・テストを含むビルド（11,673 jobs）、
`DkMathTest.lean`、ルートsmoke、マーカー照合、`git diff --check`は全て成功した。
新規コードに警告はなく、全体入口で再生される既存の別モジュールの`sorry`警告5件は今回の依存監査と区別する。
実行コマンド・結果とルート到達性は[evidence/validation-note030.txt](evidence/validation-note030.txt)に保存した。

## 9. 次の開始点

次は030-004である。今回の`y_integral_of_x_integral`、単元の法2での性質、非自明な倍点のx非零性を再利用し、
a₂が深さ1以上か単元かで分け、2Qと3Qの座標式から付値0を除く。
p≥5が2Q,3Qの消失を防ぐ条件となる。
ここで正の下界が閉じた後に、030-005の2-torsion反射へ進む。
反射後のP+Tをp-torsionとして扱うことはせず、2(P+T)=2Pへ戻す必要がある。

今回の区切りは、検証可能な001〜003の教科書を完成させるための作業範囲の選択である。
004〜008に未証明の仮定や空の終点を置くことはせず、既存NOTE-029の条件付きhrat入力も保持した。
