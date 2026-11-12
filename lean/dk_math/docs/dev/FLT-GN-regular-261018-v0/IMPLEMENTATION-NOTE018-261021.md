# NOTE-018: 交代対から円分行列式への接続と倍写像の全射性

日付: 2026-10-21。NOTE-018のうち、一般の交代対の行列式公式、実際の円分指標、
乗法的な対からの翻訳、同じFrey Sourceへの条件付き接続、倍写像の全射性を実装した。
**Weil対の幾何学的構成は未実装であり、円分行列式の無条件な証明はまだ得ていない。**

| 項目 | 今回の状態 |
| --- | --- |
| 実際のmod p円分指標χₚと根への作用式 | 無条件に構成・証明 |
| 二次元交代対に対する行列式倍の公式 | 一般の線形代数として証明 |
| 乗法的な対をAdditive μₚ上の双線形写像へ翻訳 | 法則を持つ対を明示入力して証明 |
| 同じ実際のE[p]の基底対の値の原始性 | 非退化な対を明示入力して証明 |
| 同じSourceのdet ρ=χₚ、任意のp乗根への作用式 | WeilPairingDataを明示入力する条件付き定理 |
| 安定直線の適合基底での上三角性・対角成分の積 | 上三角性は線形代数、積=χₚには対入力が必要 |
| 標数0の楕円曲線の非零自然数倍写像の全射性 | Weil対を仮定せず無条件に証明 |
| WeilPairingDataを実際に構成する幾何学的provider | 未実装 |

## 1. モジュールと公開入口

| モジュール | 役割 |
| --- | --- |
| `DkMath.Lib.RepresentationTheory.AlternatingDeterminant` | 座標展開、交代対と行列式、非退化性からの指標同定 |
| `DkMath.Lib.RepresentationTheory.StableLineMatrix` | 安定直線の適合基底での上三角性と対角積 |
| `DkMath.Lib.NumberTheory.CyclotomicRootModule` | μₙのZMod加群、実際の円分指標と定義式 |
| `DkMath.Lib.NumberTheory.RootPairingDeterminant` | 乗法的な対から双線形対への翻訳、円分行列式への一般接続 |
| `DkMath.Lib.NumberTheory.EllipticTorsionWeilDeterminant` | 実際のE[p]上の明示的な供給契約と条件付き定理 |
| `DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective` | 正次数のファイバーから任意の点への倍写像原像 |
| `DkMath.FLT.FreyResidualCyclotomic` | 同じSourceの行列式指標・任意基底・根への作用・安定直線への接続 |

本体7モジュール502行、教科書docstringを含む。名前付き公開宣言37個（構造・加群instanceを含む）。
全新規Leanファイルでimport後の `#print "file: モジュール名"` を保持した。
`DkMath.Lib`・`DkMath.FLT`・ルート `DkMath` と、回帰・監査の `DkMathTest` に配線した。

## 2. 冪の剰余計算を繰り返さない翻訳

乗法的な群μₙを `Additive (rootsOfUnity n L)` として読む。
全ての元がn乗で1になるので、加法的にはn倍で零になる。
`AddCommGroup.zmodModule` により、これはZMod n加群となる。
非零nでは、a∈ZMod nによるスカラー倍は根のa.val乗に一致する。
原始根の選択や離散対数は不要である。

`RootPairing` はV上の乗法値の対と、双加法性・交代性・左非退化性を記録する。
双加法性からe(0,y)=e(x,0)=1、e(ax,y)=e(x,y)^aを得る。
VがZMod n加群なのでn倍が零となり、e(x,y)^n=1も従う。
従って値はμₙに入り、各変数の加法準同型を `toZModLinearMap` で線形化できる。
この `rootForm` は交代性と非退化性を保つ。

この方法により、行列式の証明からZMod代表元の足し算・掛け算・負号の冪の処理を取り除いた。
一般の双線形写像として証明した結果を、最後に乗法的な根へ戻せばよい。

## 3. 交代対は行列式を測る

体k上の二次元空間V、任意のk加群W、交代双線形写像B:V×V→Wを取る。
基底bと座標x₀,x₁,y₀,y₁について

\[
B(x,y)=(x_0y_1-x_1y_0)B(b_0,b_1)
\]

を証明した。B(x,x)=0からB(y,x)=−B(x,y)を導くので、標数2も扱える。
反対称性だけを交代性の代用にはしていない。
線形写像fについては

\[
B(fb_0,fb_1)=\det(f)B(b_0,b_1)
\]

となる。非退化性があればB(b₀,b₁)≠0である。
群作用ρと指標χに対して

\[
B(\rho(g)x,\rho(g)y)=\chi(g)B(x,y)
\]

を与えると、非零の基底対の値に対するスカラー倍の単射性からdet ρ=χを得る。
値空間W自体の次元を仮定する必要はない。

## 4. 円分側と実際のE[p]への接続

標数0の体Kの代数閉包にはp個のp乗根が存在する。
Mathlibの `modularCyclotomicCharacter` を絶対ガロア群へ制限して、
`CyclotomicRootModule.cyclotomicCharacter p` を定義した。
全てのp乗根zに対するσ(z)=z^{χₚ(σ).val}を証明済みであり、楕円曲線の対は不要である。

一方、`WeilPairingData E p` は同じ実際の `Torsion E p` 上の `RootPairing` と、
既存の `representation E p` に関するガロア同変性を記録する。
型クラスによる存在の自動補完や、新しい公理としての存在仮定は導入していない。
このデータを明示入力した場合に限り、一般の交代対の定理を特殊化して

```lean
torsion_determinant_eq_cyclotomic_of_pairing
residual_determinant_eq_cyclotomic_of_pairing
```

を得る。前者はNOTE-017の実際のE[p]の基底を使い、後者は同じSourceの
`residualBasis` と `residualDeterminantCharacter` を使う。表現や曲線を置き換えない。
非退化性により基底対の値は1ではなく、素数pでは原始p乗根になる。
さらに任意のζ^p=1に対して、同じ線形作用素の行列式を用いた
σ(ζ)=ζ^{det(ρ(σ)).val}を証明した。これも対入力を保持する。

安定直線がspan{b₀}である基底では、作用行列の左下成分が零になる。
従って対角成分の積はdet ρとなり、対入力がある場合はχₚと等しい。
ここでは対角成分の積の等号を公開し、二つの一次元指標の独立した構成や
Mazur型の算術による安定直線の排除までは主張しない。

## 5. 倍写像の全射性を短く取り出す

NOTE-016の `multiplication_fiber_natDegree` は、任意の有限座標点Q=(c,y)に対して
H=Φₙ−cΨSqₙの次数がn²であると保証する。n≠0なら正次数なので、代数閉包上で根xを持つ。
`exists_aligned_multiplication_preimage` はこの根から、符号調整を含めて[n]P=Qとなる実際の点Pを作る。
Qが無限遠点ならPも無限遠点でよい。

従って

```lean
multiplication_surjective (n : ℕ) (hn : n ≠ 0) :
  Function.Surjective (nsmulAddMonoidHom n : Points E →+ Points E)
```

を得た。標数0・楕円曲線性を要求するが、素数性・奇数性・分離的ファイバーの選択は不要である。
これは対入力とは独立した、今回の無条件な幾何学的進展である。

## 6. 回帰と監査

実在するSource 2の(4,3,5)の曲線について、37倍・4倍写像の全射性を確認した。
零倍写像は、同じ曲線の既存の非零点を像に持たないので全射でない。
同じ曲線のE[37]の円分行列式と基底対の原始性は、実際の対データを明示入力する入口として確認した。
仮想的なSource 37を入力する入口も同様に検査する。

独立の線形代数の回帰ではF₃₇²上の面積対と、第一座標だけをu倍する非自明な対角表現を構成した。
対の同変性・非退化性から、行列式指標がu↦uであることを得た。
零の双線形対も自明指標に関して同変だが、この表現の行列式は自明ではない。
従って非退化性を落とした定理は偽になる、という反例も形式化した。

`Note018DependencyAudit` は公開37宣言・回帰17宣言の公理と、18経路の型・opaque本体を検査する。
円分行列式の条件付き経路では対データ・非退化性・同変性の使用を要求する。
逆に円分指標自体と倍写像全射性の経路では、対データへの依存を禁止する。
標準論理公理3種のみを許し、外部の未移植定理・FLT終点・旧条件付き位数provider等を禁止する。

検証結果は [検証記録](evidence/validation-note018.txt)、ルートimportの確認コードは
[RootSmokeNOTE018.lean](evidence/RootSmokeNOTE018.lean) に保存した。

## 7. 未実装の幾何学的providerと参照実装

参照したのは以下の一次ソースである。今回これらのソースをimport・コピーしていない。
線形代数と乗法・加法の翻訳は、現在のDkMathとMathlibのAPIを用いて実装した。

- [Weil対の存在](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean): 取得blob `54e84fd2cf33c04f0db723f5289f87f7d19b2573`。
- [対から行列式への証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean): 取得blob `61485795881143ba3b2aee16c237c67dba373734`。
- [関数体上の対の定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_EllipticCurve_WeilPairingFun.lean): 取得blob `87db2103488123818b08bf0d9302badff87ac510`。
- [座標環のDedekind性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean): 取得blob `08c1b731e747c7eab951239a306657dac633d42f`。
- [対のガロア同変性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_galois.lean): 取得blob `cc05c14d0a942efea28586bee5cc9b8d1bea7c41`。

参照実装の存在証明は、`weilFun` の平行移動で生じる定数を対の値とし、付値と関数体の議論で
法則・非退化性を供給する。現在のチェックアウトには、この`weilFun`、平行移動同型、
関連付値補題、座標環のDedekind性の対応する実装がない。
単に「適切な定数がなければ1」とする定義を移すだけでは、対の法則も非退化性も得られない。
今回の `WeilPairingData` を構成するには、これらの幾何学を実装する必要がある。

次の明確な入口は、この同じ `WeilPairingData E p` を標数0の楕円曲線から構成することである。
それができれば今回の条件付き定理から、同じFrey Sourceの円分行列式を無条件化できる。
Frey表現の既約性・Mazur型理論・慣性作用・Artin導手・FLT37や一般FLTの終点は、さらに別の境界である。

## 8. 実行結果

- `lake build DkMath.Lib.NumberTheory.EllipticTorsionWeilDeterminant DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective`: 成功（2869 jobs）。
- `lake build DkMathTest.FLT.FreyResidualCyclotomic`: 成功（3199 jobs）。
- `lake build DkMathTest.FLT.Note018DependencyAudit`: 成功（3200 jobs、37公開宣言・17回帰宣言・18経路）。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: 成功（11583 jobs）。
- ルートsmoke、`lake env lean DkMathTest.lean`、マーカー照合、静的検査、`git diff --check`: 成功。

新規9モジュールには警告・エラーなし。別の既存モジュールには歴史的な警告が残る。
公理監査の成功は新しい公理を導入していないという意味であり、定理の明示入力である
WeilPairingDataの存在を証明したという意味ではない。
