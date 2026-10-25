# NOTE-032 全点関数のGalois降下と軌道積

## 1. 今回確定したこと

前回の奇数核の非特異性に続き、同じ全点関数のGalois同変性、反転保存、
K係数標的への移送、固定剰余類の有理像を一括実装した。
加法性へ向けて、同じHの軌道積を同じ標的関数体へ降ろす構成と、源の位数公式も証明した。
内部枝番は追加していない。

| 数学的部品 | 判定 | 内容 |
|---|---|---|
| 特殊化したX_H,Y_HのGalois同変性 | 完了 | 同じ実点座標和の添字を置換 |
| 奇数核の全点関数の反転保存 | 完了 | H上のOも含む |
| 選択済みK係数モデル上の全点関数 | 完了 | 既存モデルの基底変換等式による移送 |
| 前回の同じ全点関数との同定 | 完了 | 移送を戻すとoddKernelPointMapに一致 |
| 降下後の零ファイバー、H軌道不変性 | 完了 | 同じHを保持 |
| 全点関数のGalois同変性 | 完了 | 標準のpointActionとの実際の可換図式 |
| 固定剰余類、Cofixed残余点の有理像 | 完了 | 同じK/ℚ係数標的上の実点、零判定も保持 |
| 軌道積の固定体所属・標的関数への一意な降下 | 完了 | 同じkernelModelPullを使用 |
| 軌道積の源での付値・整数位数公式 | 完了 | 剰余類上の積・和、Oを含む |
| 標的の像点での位数との比較 | 未完了 | 場所の制限と局所重複度の接続が必要 |
| 加法性、群準同型の核、isogeny | 未完了 | 主因子の押し出しは未構成 |
| 有理像のp捩れ性、整数モデル、零成分輸送、hno | 未完了 | 非零有理点の存在からは結論していない |

## 2. 所有者と公開入口

- [EllipticFiniteKernelPointDescent](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelPointDescent.lean):
  14定理・2定義。実点の移送、有限座標と全点関数の同変性、反転、固定剰余類とCofixed像の降下。
- [EllipticFiniteKernelNorm](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelNorm.lean):
  12定理・2定義。同じ核に沿う軌道積、その位数、同じ標的関数体での一意な実現。
- [FreyFiniteKernelPointDescent](../../../DkMath/FLT/FreyFiniteKernelPointDescent.lean):
  7定理・2定義。同じSource、直線L、実点核を保持したℚ係数標的と全点関数への接続。

本体は計33定理・6定義、536行。Libの公開宣言には教科書docstringと昇格マーカー
`[DkMath.Lib]`、各所有者にはimport直後のファイルマーカーを付けた。
DkMath.Lib、DkMath.FLT、DkMathTestの入口へ登録した。入口の確認は静的検査である。

## 3. Galois作用は「核の点を置換する」

kをKの代数閉包、Hを同じ幾何学的点群内の有限部分群とする。
Hの安定性は、各点を固定するという条件ではない。
既存の`kernelGaloisEquiv`はσとσ⁻¹からHの置換を作る。
これと実際の点の加法保存から

\[
 X_H(\sigma P)=\sigma X_H(P),\qquad Y_H(\sigma P)=\sigma Y_H(P)
\]

を証明した。補正定数の和も同じ置換で固定される。
Hへの所属はσの作用の前後で同値なので、核外点の特殊化も型の中で整合する。
座標に関するこの二定理は標数0を要求しない。

標数0・奇数位数Hでは、前回のIsEllipticから全点関数を利用できる。
既存の`descendedKernelModel`の基底変換等式を`pointModelEquiv`で点へ移し、
`descendedKernelPointMap`を構成した。これは別の曲線や別の点写像の存在選択ではない。
`descendedKernelPointMap_transport`が前回の同じ全点関数との一致を保証する。

核上はO、核外は同じ二座標、という二つの場合を合わせ、元の体上の標準的な
点作用`pointAction`に関するGalois同変性を証明した。
反転保存も既存の二座標の反転公式と同じa₁,a₃から供給した。

## 4. Cofixedから、有理像までは加法性なしで届く

PのH剰余類が固定なら、各σに対してσP=P+Q_σとなるQ_σ∈Hがある。
H軌道不変性と同変性から

\[
 \sigma\phi(P)=\phi(\sigma P)=\phi(P+Q_\sigma)=\phi(P).
\]

従って像の座標はKへ降りる。既存の`exists_baseChangePoint_of_fixed`で、
同じK係数標的上の実点Rを構成し、`baseChangePoint R = φ(P)`を保持した。
基底変換の単射性と既存の零ファイバー判定から`R=0 ↔ P∈H`も得る。

CofixedではσP−P∈Lなので、その実点像をQ_σとすれば上の条件が成立する。
`exists_rational_image_of_cofixed`は`R=0 ↔ P∈L`まで戻す。
SourceではE[p]の次元2とLの次元1から核外点を取り、
`exists_nonzero_rational_residual_kernel_image`で非零ℚ有理像を内部構成した。
これはCofixed直線の存在を証明する定理ではなく、同じ直線とCofixed性を入力に保つ。
また、φ(pP)=pφ(P)は未証明なので、得られた像をp捩れ点とは呼ばない。

## 5. 模範解答の加法性と、DkMathで構成した軌道積

閲覧した模範解答はanthropics/fermats-last-theoremの
[Vélu点群準同型の証明](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/fa5eda1fdc857b6445c21720c78805e7ecded543)。
blobは`fa5eda1fdc857b6445c21720c78805e7ecded543`。
リンクは当該ファイルのGit blob APIを指す。
参照先のファイル内容と識別子は保存済みソースで照合した。

証明の流れは、同じ関数体写像に沿う場所の制限、主因子を保存する因子の押し出し、
Pic⁰の群準同型、種数1の点群との同定、最後に座標で定義した関数との一致である。
モデルの非特異性やOを保存する集合写像の存在だけで加法性を済ませてはいない。
DkMathでは点イデアルと類群への単射は既存だが、この関数体写像に沿う
主因子の押し出しはまだ供給されていない。

その生成関数を先に具体化した。F=k(E)、ι=`kernelModelPull`として

\[
 N_H(f)=\prod_{Q\in H}t_Q(f)\in F_H,\qquad
 \iota(g_f)=N_H(f)
\]

となる標的関数g_fが一意に存在することを証明した。
H不変性は添字の置換、存在は`ι.fieldRange=F_H`、一意性はιの単射性から従う。
`kernelModelNorm`はこのg_fであり、乗法性、非零性、標的関数gに対する
`kernelModelNorm (ι g)=g^|H|`も証明した。
今回の定義は明示的な軌道積であり、`Algebra.norm`との等式は今回のAPIに含めていない。

全点での既存の平行移動付値公式から、源で

\[
 v_P(N_H(f))=\prod_{Q\in H}v_{P+Q}(f),\qquad
 \operatorname{ord}_P(N_H(f))=\sum_{Q\in H}\operatorname{ord}_{P+Q}(f)
\]

を証明した。後者ではf≠0を明示している。
この式の左辺は源の点Pでの位数であり、標的のφ(P)での位数ではない。

次の数学的単位は、ιによる場所の制限が同じ全点関数と一致することと、
正規化された局所位数の比較を閉じ、同じg_fによる主因子の押し出しへ接続することである。
源のアフィン座標環だけで処理すると、X_H,Y_HのH上の極を落とすため、
OとHの点を含む場所の議論を保つ必要がある。
今回はこの接続を仮定した準同型を新設して完了扱いすることはしていない。

軌道積の添字置換は既存のApache所有者の和の証明から拡張したため、
新しいNorm所有者にも元のApache表記・NOTICE参照・元blobを保持した。

## 6. 実例と検証

[対象テスト](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelPointDescent.lean) は
同じy²=x³−x、位数9の全3捩れ核、R=(−1,0)を使用する。13定理・2定義。
巡回生成元や核の各点の有理性を要求しない。

- 同じ全点関数のGalois同変性、零ファイバー、反転保存、前回の関数への移送等式。
- 任意のQ∈E[3]について剰余類R+E[3]の固定性と非零ℚ有理像。
- 非定数xの軌道積の一意な標的関数と非零性。
- 固定座標X_Hの軌道積がX_H⁹であることと、源のOでの位数−18。

[Source37検査](evidence/Note032PointDescentSmoke.lean) は5定理。
同じℚ係数標的の楕円性、同じ全点関数への移送、零ファイバー、同変性、
Cofixed入力から非零有理像への接続を確認した。

対象モジュールビルド、対象テストモジュールビルド、Source37の直接Lean検査は全て成功。
本体39宣言・実例15宣言・Source37の5宣言、計59宣言の公理依存は
`propext / Classical.choice / Quot.sound`の範囲内。
禁止構成、Lib依存方向、docstringと昇格マーカー、import直後のファイルマーカー、
入口登録、前回の所有者・契約資料の保持、差分の空白も検査した。

[検証記録](evidence/validation-note032-point-descent-norm.txt)、
[構造化証拠](evidence/note032-point-descent-norm.json)。
