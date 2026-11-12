# NOTE-027: 同じ Weil 固有値のガロア同変性

日付: 2026-10-21。標数0の体K上の楕円曲線、n≠0、S,T∈E[n]に対し、NOTE-025・026の同じ値について

\[
c(\sigma S,\sigma T)=\sigma(c(S,T))
\]

を証明した。交代的双指標の値を別の形式的な対へ置き換えず、既存の実際のtorsionガロア作用と接続した。
非退化性・固定体の同定・倍写像の引き戻し次数は今回の対象外であり、`WeilPairingData`や円分行列式の無条件化は未完である。

## 1. 読み順

| モジュール | 教科書の内容 |
| --- | --- |
| `DkMath.Lib.NumberTheory.EllipticFunctionFieldGalois` | 係数作用から座標環・分数体の同型を構成。半線形性、一般点、平行移動との交換則 |
| `DkMath.Lib.Algebra.DedekindValuationEquiv` | 素イデアルの冪への所属から、正規化された付値の環同型による輸送 |
| `DkMath.Lib.NumberTheory.EllipticGaloisValuation` | 点イデアルの像、有限場所の輸送、既存のpointActionへの接続 |
| `DkMath.Lib.NumberTheory.EllipticWeilGalois` | 一意な生成元定数倍、同じ固有値・根値・双指標の同変性 |
| `DkMath.FLT.FreyWeilGalois` | 同じSourceの有理曲線と剰余表現への接続 |

本体5ファイル、公開宣言46個。全宣言に日本語docstring、import後に正確な`#print "file: ..."`を付けた。
`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`へ公開し、回帰と依存監査を`DkMathTest`に接続した。

## 2. 関数体の作用は半線形である

一般の拡大K/FとF代数自己同型σに対して、曲線の係数がFにあることから二変数多項式への係数作用は曲線方程式を保つ。
`galRingHom`を商環の普遍性から構成し、逆自己同型による写像と互いに逆であることを示す。
`galRingEquiv`はこの実際の環同型、`galFunctionFieldEquiv`は分数体の普遍性によるその延長である。
拡張の存在を仮定として受け取ったり、一般点の像を別途仮定したりしない。

\[
\Phi_\sigma(af)=\sigma(a)\Phi_\sigma(f),\qquad
\Phi_\sigma(x)=x,\quad\Phi_\sigma(y)=y.
\]

`galAlgHom`はF上の代数準同型である。K上の線形性は主張しない。
一般点の像と、定数点の基底変換の像を計算し、既存の`pointHom`による平行移動を比較すると

\[
\Phi_\sigma(\tau_S^* f)=\tau_{\sigma S}^*(\Phi_\sigma f)
\]

を得る。恒等元・合成についても`galFunctionFieldEquiv_one/mul`で実際の関数上の作用則を証明した。

## 3. 付値は正規化ごと輸送する

単に付値環が同型というだけでは、整数の位数が同じとは言えない。
`mem_comap_pow_iff`で素イデアルの各冪への所属を比較し、`intValuation_comap_ringEquiv`で正規化された整数指数の一致を得る。
`valuation_comap_ringEquiv`は分子・非零分母の表示を使い、分数体の全ての元へ延長する。

点イデアルは

\[
\Phi_\sigma(\mathfrak m_P)=\mathfrak m_{\sigma P}
\]

と移り、`valuation_galFunctionFieldEquiv`と`finitePointValuation_galois`が

\[
v_{\sigma P}(\Phi_\sigma f)=v_P(f)\quad(P\ne O)
\]

を証明する。f=0も許す。今回追加したガロア付値輸送の定理は有限場所の定理であり、Oにおけるガロア輸送定理の追加はしていない。

## 4. 生成元は一致ではなく一意な定数倍になる

Tの像をT′=σTとする。任意の有限場所Qに対しP=σ⁻¹Qと置けば、

\[
[n]Q=T′\iff[n]P=T,\qquad[n]Q=O\iff[n]P=O.
\]

既存の`valuation_weilFunction`の二つの指示関数と付値輸送から、Φσ(w_T)とw_{T′}の付値が一致する。
両関数が非零なので比の全有限場所での付値は1となる。
`placeOf_surjective`と既存の`EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one`によって、その比を非零定数へ戻す。
この定数判定は既に証明済みの幾何学を再利用しており、有限場所だけを見た新たな未証明仮定は置かない。

`existsUnique_scalar_galois_weilFunction`は

\[
\exists!a\in\overline K^\times,\quad\Phi_\sigma(w_T)=a w_{\sigma T}
\]

を与える。生成元の選択がガロア不変だとは主張しない。一意性はw_{σT}≠0と係数体の埋め込みの単射性による。

## 5. 固有値の一意性で主定理を得る

同じ固有方程式τ_S*w_T=c(S,T)w_TにΦσを適用する。
平行移動との交換則と半線形性、前節の定数倍表示を代入すると

\[
a\tau_{\sigma S}^*w_{\sigma T}=\sigma(c(S,T))a w_{\sigma T}.
\]

a≠0を消去し、既存の`weilTranslationUnit_unique`を使えば主定理が得られる。
`galoisRootMap`は単元の係数作用をμₙへ制限した乗法準同型であり、根のn乗が1である条件を保存する。
`weilTranslationCharacter_galois`、`weilAlternatingBicharacter_galois`、`weilAlternatingBicharacter_representation`は同じ等式を根値と剰余表現の型へ移す。
Sourceでも同じ有理曲線・同じ比例定数・同じ剰余表現のAPIとして利用できる。

## 6. 回帰と検証

`DkMathTest.FLT.FreyWeilGalois`に名前付き回帰14個を追加した。
Source 2の曲線y²+xy=x³−2x²−9x上の相異なる非零2-torsion点(0,0)と(4,−2)を使う。
任意のσによる両点の固定性、非対角の固有値の同変性と固定性、任意係数の半線形性、一般点の座標、任意関数の移動と有限場所付値、生成元の一意な定数倍を検査する。
指数1と、展開を必要としない指数37の一般torsion点にも特殊化する。
これらから非対角の値が非自明であることや、特定の非自明なガロア自己同型の存在を結論しない。

検証結果は[evidence/validation-note027.txt](evidence/validation-note027.txt)に保存した。

- focused buildと監査: 3,218 jobs成功。46本体・14回帰の公理は`propext`、`Classical.choice`、`Quot.sound`のみ。13依存経路が成功。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: 11,645 jobs成功。
- ルートimportのsmoke・主定理の`#print axioms`・`lake env lean DkMathTest.lean`: 成功。
- マーカー追跡・禁止構文走査・ライセンスパス確認・`git diff --check`: 成功。

新規モジュールに警告はない。統合ビルドの既存5件の`sorry`警告は追加コードの外にあり、今回の監査経路は`sorryAx`を禁止している。
依存監査は全46本体・14回帰宣言の公理と、選択した13経路の型・opaque本体を検査する。
座標環と分数体の実際の同型、点イデアル、正規化付値、定数判定、固有値の一意性を要求し、未構成のWeil対データ・旧FLT終点・大域Kummer入力を禁止する。

## 7. 参照した実装と境界

以下の一次ソースを読み、既存のDkMathの点作用・平行移動・定数判定へ翻訳した。

- [関数体の係数作用と固有値の同変性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_galois.lean): blob `cc05c14d0a942efea28586bee5cc9b8d1bea7c41`
- [環同型による有限場所の付値輸送](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_placeOf_smul_of_algEquiv.lean): blob `98fe0128d5c2a913dd127b273fb542d7d5102761`
- [写したWeil関数の非零定数倍表示](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_exists_map_weilFun_eq_mul_weilFun_smul.lean): blob `60e4631bea5ae21bf113739f6471516d5e6ac7c3`

適応した4ファイルにはApache-2.0表示・原著作権・blob・既存LICENSE/NOTICEへの相対パスを保持した。
外部のP2M/P2MWをimportしていない。Source・回帰・監査は既存のDkMathライセンスに従う。

NOTE-028に残るのは非退化性である。忠実なtorsion平行移動作用、固定体と[n]*K(E)の同定、倍写像の関数体次数を接続する必要がある。
今回のガロア同変性だけで`WeilPairingData`、無条件のdetρ=χ、Frey表現の既約性、一般FLTを完成したとはしない。
