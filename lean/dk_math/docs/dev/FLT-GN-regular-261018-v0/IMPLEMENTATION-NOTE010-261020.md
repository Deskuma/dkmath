# NOTE-010 §4以降: Freyの残余ガロア表現への入口

日付: 2026-10-20。第一優先の残余ガロア表現について、同じFrey曲線の実際のE[p]と
Krull位相に関する連続作用を構成した。Pascal行の構造は、残余表現の差分冪へ接続した。

## 1. 固定した範囲

| 項目 | 今回の実装 | 残る境界 |
| --- | --- | --- |
| 実際のE[p] | 代数閉包上の点群のp倍写像の核、Fₚ線形構造 | 位数p²、次元2、基底の存在 |
| ガロア作用 | 座標写像から構成した `Representation` と可逆作用素への準同型 | 行列式、Weil対、既約性 |
| 連続性 | 開固定部分群と、Krull位相から離散E[p]への同時連続性 | 慣性作用、不分岐性、有限平坦性 |
| 反例の入口 | 同じ `Source.ofCounterexample` から連続表現と全素数の局所算術入力 | Artin導手、モジュラー性、レベル降下 |
| Pascal差分 | `(ρ(σ)−1)^p=ρ(σ^p)−1`、条件付き冪零性 | 全慣性群の作用が自明となるための独立した条件 |

追加本体は4モジュール396行（解説込み）。回帰と依存監査を各1モジュール追加した。
新規ファイルは全て、import後に指定形式の `#print "file: モジュール名"` を持つ。

## 2. 模範解答から参照した入口

参照した一次ソースは
[ガロア作用とtorsionの定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_GaloisRep.lean)
と [Frey packageの曲線定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_FreyPackage.lean)。
前者の経路は、Mathlibの実際の点の写像からガロア作用を作り、整数torsion条件へ制限するものだった。
2026-10-20にmainの公開ソースを参照し、DkMathのLean 4.34.1のMathlib APIで再構成した。

DkMath側は `nsmulAddMonoidHom n` の核を使用し、線形表現を明示的な準同型として構成する。
`mem_torsionGroup_iff_torsionBy` が、この条件と標準の
`Submodule.torsionBy ℤ (Points E) (n : ℤ)` の条件を同値にする。
`torsionByAddEquiv` は標準表示との加法同型であり、`torsionByAddEquiv_val` により
元の幾何学的な点をそのまま保持することが分かる。
外部リポジトリの構造体をimportした同一型の定理ではなく、標準torsion表示への翻訳アダプタである。

## 3. 体と曲線から実際の点群を作る

`DkMath.Lib.NumberTheory.EllipticTorsionRepresentation` は、体KとK上の曲線Eを入力とする。

1. `Points E` は、同じ曲線を `AlgebraicClosure K` へ基底変換した滑らかな点群。
   無限遠点を含み、加法群則にはMathlibの既証明のものを使う。
2. `torsionGroup E n` はn倍写像の核。元の点と `n • P=0` の証拠を対で保持する。
3. `torsionModule` は、nで消える加法群の標準ZMod n線形構造を供給する。
   nが素数なら残余体上のベクトル空間となる。
4. `pointAction E σ` は、体の自己同型を座標へ適用する実際の `Affine.Point.map`。
   加法を保つためn倍零条件も保存し、`torsionAction` へ制限できる。
5. `representation E n` はこの作用をZMod n線形にした群準同型。
   `representation_inverse` はガロア逆元による逆写像を証明する。

`underlying_representation` は、線形表現を元の点へ戻した値が、同じ座標へのガロア作用であることを示す。
`pointAction_baseChange` はK有理点の基底変換が全てのガロア元で固定されることを示す。

この一般構成は滑らかな点群に対して定義できる。楕円曲線としての非特異性は利用側で供給する。
Freyの `Source` には既存の `rationalCurve_isElliptic` があり、同じ曲線を実際の楕円曲線として扱える。
一般のnに対して空間の非零性を仮定していない。特に `torsion_one_eq_zero` はE[1]が零点だけであることを示す。

## 4. Krull連続性を証明する

`DkMath.Lib.NumberTheory.EllipticTorsionContinuity` は、絶対ガロア群の既存のKrull位相を使う。

- 無限遠点の固定部分群は全群なので開く。
- 点(x,y)の座標はK上代数的であり、各座標の固定部分群は開く。
- 点の固定条件は `σ(x)=x ∧ σ(y)=y` なので、二つの開集合の交わりとなる。
- torsion部分群から元の点への単射により、同じ固定条件をE[n]へ制限する。
- 離散集合への群作用の連続性と固定部分群の開性の同値を使う。

従って `torsionContinuousSMul` と `representation_orbit_continuous` を得た。
証明はE[n]の有限性を使わず、ガロア変数を含む同時連続性まで扱う。
各線形写像だけが連続という条件に留めていない。

有限性が未証明の段階では、全点の固定部分群の無限交叉が開くとは結論できない。
従って表現全体の核の開性や、局所慣性群の自明作用を、この結果に足してはいけない。

## 5. 同じFrey Sourceへ接続する

`DkMath.FLT.FreyResidualRepresentation` は、既存の同じ `S.rationalCurve` を使う。

```lean
S.ResidualSpace
S.residualRepresentation :
  Representation (ZMod p) (Field.absoluteGaloisGroup ℚ) S.ResidualSpace
```

`ResidualSpace` は実際の幾何学的p-torsionである。
`residualAutomorphisms` は同じ作用を `Units (Module.End (ZMod p) S.ResidualSpace)` へ写し、
`residualAutomorphisms_coe` が元の表現と一致することを示す。
ここでは基底を選ばず、GL₂の添字に必要な次元2を仮定に追加していない。

`residual_action_continuous` の結論は、絶対ガロア群と残余空間の積上の同時連続性である。
`ofCounterexample_residual_entrance` は、任意の非零整数反例、素数p≥5から、
同じ選択済みSourceについて次を同時に得る。

- 曲線が実際に楕円曲線であること。
- 実際のE[p]への上記連続ガロア作用。
- 全素数ℓでの正式な最小性、良還元または乗法的還元。
- 同じ曲線の `p∣vℓ(Δ_min) ↔ ℓ≠2`。

原始化の共通因子や符号付き置換の証拠は、既存の `Source.ofCounterexample_spec` で保持される。
局所算術と表現を同じ曲線上に置いたが、判別式付値から慣性作用を消す定理はまだ必要である。
ℓ=pでの算術的なp倍性も、有限平坦性・有限性を意味するものではない。

## 6. Pascal行と差分作用素

`DkMath.Lib.RepresentationTheory.PascalDifference` では、まず係数体上で

\[
 (X-1)^p=X^p-1\quad\text{in }\mathbb F_p[X]
\]

を証明する。Pascal行の内部係数のp可除性を使う等式である。
次に `aeval T` で作用素へ写し、

\[
 (T-1)^p=T^p-1
\]

を得る。End(V)は一般には非可換だが、一つの作用素への多項式評価は可能である。
V=0も許すため、End(V)自体に「標数が正確にp」と仮定せず、係数体で先に証明した。
有限次元性・非零性は不要で、内部係数を巨大に展開する必要もない。

群表現の準同型性から、

\[
 (\rho(\sigma)-1)^p=\rho(\sigma^p)-1
\]

となる。`residual_difference_pow` が同じFrey残余表現にこの式を適用する。
`ρ(σ^p)=1` が供給されれば、`residual_difference_nilpotent` によりp段以内の冪零性を得る。
群内でσ^p=1ならその前提を供給できることも、一般ライブラリで証明した。

既存の `DkMath.Lib.Cosmic.prime_choose_exact_layer` と同様、ここは全素数に共通するPascal構造である。
この合同式に正則／非正則を分ける独立な条件を仮定していない。
依存監査では実際の二項係数可除性 `Nat.Prime.dvd_choose_pow` と多項式評価へ到達することも要求する。

## 7. 実在する点と、成立しない近道を検査する

回帰には、指数2の実在する原始解(4,3,5)から作ったSourceを用いた。
同じ曲線の(0,0)は非特異で非零の2-torsion点であり、全てのガロア元で固定される。
この非零点が保持されることから、各作用素が零写像ではないことを確認した。
作用が非自明であることや、指数5以上の反例の存在をこの例から主張していない。

Pascal側はF₃₇²上の

\[
 T=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
 N=T-1=\begin{pmatrix}0&1\\0&0\end{pmatrix}
\]

を使い、N²=0、T³⁷=1、T≠1を証明した。37回の逐次展開は行わない。
従って差分が冪零であるだけで作用が恒等だとはいえない。
この具体例は、Pascal構造から不分岐性やFLTの矛盾へ飛躍しないための境界を固定する。

## 8. 公開入口と監査

公開入口は `DkMath.Lib`、`DkMath.FLT` とルート `DkMath`。
回帰と監査は `DkMathTest.lean` に接続した。
回帰側には10件の `example` と7件の名前付き検証補題があり、実際の点の構成も検査する。
公理監査は本体43公開宣言と回帰側の名前付き12宣言を対象とする。
主要11経路では型・opaque本体を辿り、点の写像、n倍写像の核、Krull固定部分群、
同じSource、二項係数可除性を実際に使うことを要求する。
FLT終点・模範解答の外部namespace・全域的な正則性供給を禁止する。

次の数学的な接続点は、標数0におけるE[p]の位数p²・次元2、
Weil対による行列式、局所体への制限と慣性作用の解析である。
Artin導手・既約性・モジュラー性・レベル降下は引き続き別の証明が必要となる。

検証結果とコマンドは [検証証跡](evidence/validation-note010.txt) に記録した。
回帰build（3,142 jobs）、監査build（3,143 jobs）、統合build（11,531 jobs）、
ルートsmokeと統合build後の `DkMathTest.lean` 直接検査は全て成功した。
公開43宣言と回帰側12宣言の使用公理は、標準論理公理3種の範囲内である。
11経路の実依存監査、指定マーカーの照合、新規本体での禁止構文不使用検査、
`git diff --check` も通過した。新規6モジュールの警告はない。
