# NOTE-016: 正則ファイバーから核への単射と、素数ねじれ点群の二次元

日付: 2026-10-20。NOTE-016の最初の確定目標に加え、正則ファイバーからの単射と素数の場合の上下界の一致まで実装した。
標数0の体K上の楕円曲線Eと素数pについて、実際の代数閉包上の点群で

\[
|E[p]|=p^2,\qquad \dim_{\mathbb F_p}E[p]=2
\]

を証明した。位数・次元・独立な二点・一般ファイバーの存在は追加入力にしていない。
Frey側は同じSourceの楕円曲線性を供給して接続する。
実在するSource 2の(4,3,5)の曲線について、**その同じ曲線のE[37]** は1369点・二次元であり、
任意の非零点の直線の外に第二の点が存在する。ΨSq₃₇の相異なる根は684個となった。

## 1. 実装の分担

| モジュール | 役割 |
| --- | --- |
| `DkMath.Lib.Algebra.RationalPolynomialFiber` | 一般の有理関数のWronskian、例外値の有限性、有限集合を避ける分離的ファイバー |
| `DkMath.Lib.NumberTheory.EllipticMultiplicationCoordinates` | 実際のn倍点の有限座標、分子・分母の共通根の排除、互いに素性、Wronskian |
| `DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber` | 根から実際のファイバーへの単射、核との平行移動、下界n²、素数の位数p²・次元2 |
| `DkMath.FLT.FreyResidualRankTwo` | 同じFrey Sourceの位数・次元・直線の外の点・有限ガロアレベル |

本体4モジュール、教科書コメントを含め475行、名前付き公開宣言32個。
import直後の `#print "file: モジュール名"` を新規Leanファイルすべてに置き、
`DkMath.Lib`、`DkMath.FLT`、`DkMathTest` の公開入口へ配線した。

## 2. 共通根を排除する短縮: JacobianのXとZ

従来の参照経路では隣り合う除法多項式の互いに素性と再帰を使う。
今回はNOTE-012の `zsmul_eq_smulEval` を再利用した。

Φₙ(x)=ΨSqₙ(x)=0という共通根xがあると仮定する。
NOTE-014の `exists_affine_equation_y` で曲線方程式を満たすyを取り、楕円曲線性によって非特異性を供給する。
実際の[n]PはJacobianで `(φₙ(P),ωₙ(P),ψₙ(P))` と表示される。

- ψₙ(P)²=ΨSqₙ(x)=0なのでZ座標は零。
- φₙ(P)=Φₙ(x)=0なのでX座標も零。
- 実際の点の整数倍は非特異であり、`Jacobian.X_ne_zero_of_Z_eq_zero` はZ=0ならX≠0を保証する。

従って共通根はない。代数閉包上の共通根判定を使うと、

```lean
multiplication_polynomials_isCoprime (n : ℕ) :
  IsCoprime ((E.baseChange (AlgebraicClosure K)).Φ (n : ℤ))
    ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ))
```

が得られる。標数0・楕円曲線性を要求する。この共通根の排除自体はn=0も扱える。
後続の非定数性や有限性の結果ではn≠0を明示的に要求する。

同じJacobian公式をZ≠0の場合に有限座標へ戻すと、実際のn倍写像について

\[
x([n]P)\Psi_n^{\mathrm{Sq}}(x(P))=\Phi_n(x(P))
\]

を得る。`multiplication_finite_coordinates` はこの等式と非特異なn倍点をまとめて供給する。
有理式を形式的に置くだけではなく、既存の実際の群則の倍写像と一致させている。

## 3. Wronskianと有限な例外値を一般化する

一般の多項式F,Gに対し、W=F'G−FG'、H_c=F−cGと定義する。
標数0でFが非定数、FとGが互いに素ならW≠0である。
実際、W=0ならFはF'Gを割るので、互いに素性からFはF'を割る。
しかし標数0の非定数多項式ではF'≠0かつdeg F'<deg Fであり、矛盾する。
これにより参照実装の先頭係数の個別計算を、一般の微分と可除性の補題へ置き換えた。

次に、H_cが分離的でない値cを考える。代数閉体上の共通根判定により、
H_c(x)=H_c'(x)=0となるxを取れる。このとき

\[
F(x)=cG(x),\qquad F'(x)=cG'(x),\qquad W(x)=0.
\]

FとGは共通根を持たないのでG(x)≠0、従ってc=F(x)/G(x)と復元できる。
例外値の集合はWの有限根集合のこの像に含まれるため有限である。
`finite_not_separable_fiber` がこの結果を公開する。
分離的なら平方因子を持たないことから、NOTE-016にある `finite_not_squarefree_fiber` も供給する。

`exists_separable_fiber_avoiding` では代数閉体の無限性を使い、任意の追加の有限集合も避けて値cを選べる。
楕円曲線への適用では追加の有限集合を空にできるので、分離的な良いH_cが存在する。
なお、分離的にするのは **H_c** であり、奇数指数のΨSqₙの根の重複を消したと主張しているのではない。

## 4. 根から一つのファイバーへ、x座標を保存する単射

n≠0ならdeg Φₙ=n²、deg ΨSqₙ≤n²−1なので、cによらずdeg H_c=n²である。
分離的なH_cは代数閉包上で相異なる根をちょうどn²個持つ。

まずx座標がcの非特異点Q=(c,y_Q)を一つ固定する。
H_cの根xについて、方程式を満たすyを取り非特異点P=(x,y)を作る。
互いに素性からΨSqₙ(x)≠0であり、有限座標公式に戻すとx([n]P)=cとなる。
同じx座標の点はQと−Qなので、[n]P=Qまたは[n]P=−Qである。
後者の場合は−Pを選べば、どちらの場合も[n]P=Qとできる。

この選択にはQ≠−Qは不要である。Q=−Qでも同じ二択から一つ選べる。
従って2-torsion由来の像を追加で避ける計算も、nの奇数性も不要になった。

`exists_aligned_multiplication_preimage` は、選んだ点のxRepが元のxの `![x,1]` であることを保つ。
符号を変えてもx座標は変わらないため、異なる根が同じ点へ移ることはない。
`multiplicationRootEmbedding` は次の単射を、元の実際の点群で構成する。

\[
\{x:H_c(x)=0\}\hookrightarrow\{P:[n]P=Q\}.
\]

H_cの次数は正なので根が一つ以上あり、このファイバーも非空である。
その点P₀を一つ取り、T↦T+P₀とP↦P−P₀によって
元のn-torsionの核とファイバーの全単射 `torsionEquivMultiplicationFiber` を得る。
この平行移動後はx座標を保存する必要はなく、単射性が保たれれば十分である。

NOTE-012の実際のE[n]の有限性と合わせ、根から核への合成単射に濃度の比較を適用すると

\[
n^2\le|E[n]|
\]

を得る。これが `square_le_card_torsion` であり、標数0・楕円曲線性・n≠0が条件となる。
一般の合成数について、今回この下界を等号へ変える上界は追加していない。

## 5. 素数の位数・次元とFreyへの接続

素数pではNOTE-013の上界 |E[p]|≤p² が既にあるので、今回の下界と合わせて
`card_torsion_prime_sq` が位数p²を確定する。
実際の有限Fₚ空間の濃度公式から、`finrank_torsion_prime` は次元2を与える。
旧来の位数入力による次元定理を呼ばず、幾何学的な下界を実際に供給した。
この証明はp=2も含み、NOTE-015の指数2専用の位数定理にも依存しない。

任意の非零点Pの直線の外の点も、既存の次元判定の同値へ戻して供給する。
標準torsionBy表示へは、同じ点を保つ線形同型で次元2を運ぶ。
奇素数の場合はNOTE-015の正確な1+2rへ戻し、r=(p²−1)/2も確定する。

Frey側の `residual_rank_two_profile` は、同じSourceだけから

```lean
Nat.card S.ResidualSpace = p ^ 2 ∧
  Module.finrank (ZMod p) S.ResidualSpace = 2 ∧
  S.ResidualFactorsThroughFiniteLevel
```

を与える。素数性は必要だが、Finite・位数・次元・非零点・正則ファイバーの追加仮定はない。

## 6. 参照実装・帰属と短縮の範囲

参照した一次ソースは
[S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)。
再取得して確認した版は1,336行、blob SHAは `865709609f50e0e2ef445df7c01d01768ca731c5`。
上流の [LICENSE](https://github.com/anthropics/fermats-last-theorem/blob/main/LICENSE) はApache-2.0である。
例外値の有限性と有限座標の翻訳を含む二つの適応モジュールには、出典・改変内容・Apache-2.0の表示と
既存の `RegularKummer/LICENSE`、`RegularKummer/ANTHROPIC-NOTICE` へのパスを記した。
新たに構成した単射・素数の閉じ方・Frey facade・回帰・監査はMIT形式である。

参照実装全体をimportせず、共通根排除をJacobianへ、Wronskianを一般の可除性へ置き換えた。
二重ファイバーの正確な2n²個の計算、Qと−Qの重複排除、倍写像全体の全射性、
一般の素数冪・互いに素な指数の積への拡張は、この素数の閉じ方には必要ない。

## 7. 回帰・監査と残る境界

回帰は名前付き9補題と3例である。実在するSource 2の曲線のE[37]で位数1369・次元2・根684個、
任意の非零点の直線の外の点、さらに入力点も構成して独立な二点の存在を確認する。
合成数4では16≤位数という下界、指数2では一般の素数定理から次元2を確認する。
X²の零ファイバーが分離的でないこと、n=0のWronskianが零であることも境界として検査する。

監査は全32公開宣言と9回帰補題の公理、17の主要依存経路を対象とする。
実際のJacobian倍写像、非特異な無限遠点のX非零性、有限な例外値、相異なる根、単射、
平行移動、有限性、既存の上界・濃度公式を要求する。
旧条件付き位数・次元定理、NOTE-015の小さい下界を仮定する閉じ方、指数2専用の位数・次元定理、
外部のFLT終点や類群・Kummer providerへの迂回は禁止する。

今回で、NOTE-015に残っていた一般の素数ねじれ点の次元2と37次の根の下界を供給した。
基底を選んだGL₂への表現、Weil対・行列式、ガロア不変直線の不存在・既約性、
局所慣性・Artin導手、一般FLT・FLT37の終点は引き続き別の接続である。
標数0は座標体の仮定であり、係数体Fₚの標数pとは区別する。

検証結果は [validation-note016.txt](evidence/validation-note016.txt)、
公開ルートの検査は [RootSmokeNOTE016.lean](evidence/RootSmokeNOTE016.lean) に記録する。

回帰のfocused buildは3,176 jobs、依存監査のfocused buildは3,177 jobs成功。
32公開宣言と9回帰補題の公理監査、17経路の依存監査が通った。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,568 jobs成功し、新規6モジュールに警告はない。
ルートsmoke、`lake env lean DkMathTest.lean`、指定のマーカーチェッカー、`git diff --check` も成功した。
