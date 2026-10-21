# NOTE-028: 倍写像・固定体・非退化性から円分行列式へ

日付: 2026-10-21。
A・B・Cを順に実装し、同じ実際のWeil双指標の非退化性まで証明した。
停止を要する未解決の数学的障害は残らず、既存の`WeilPairingData`への供給と、対データを追加入力に取らない円分行列式にも接続した。
標数0の体K、K上の楕円曲線E、代数閉包上の点・関数体、非零自然数nが対象である。
Frey表現の既約性・モジュラー性・レベル降下・一般FLTは今回の結論に含まない。

## 1. 三段階の到達点

L=K̄(E)、μ=[n]*、Hを同じ実際のE[n]による平行移動自己同型群とする。

| 段階 | 証明した内容 | 主な定理 |
| --- | --- | --- |
| 028-A | μ:L→ₐ[K̄]Lを実際に構成し、有限次元性と[L:μ(L)]≤n²を証明 | `multiplicationPull`, `finiteDimensional_finrank_multiplicationPull` |
| 028-B | [L:Lᴴ]=n²、μ(L)=Lᴴ。従って[L:μ(L)]=n² | `finrank_torsionFixedField`, `multiplicationRange_eq_torsionFixedField`, `finrank_multiplicationPull` |
| 028-C | 同じ双指標の左右非退化性 | `weilAlternatingBicharacter_nondegenerate_right/left` |
| 接続 | 同じ値からWeilPairingDataを構成し、detρ=χを無条件化 | `geometricWeilPairingData`, `torsion_determinant_eq_cyclotomic`, `Source.residual_determinant_eq_cyclotomic` |

ここで「無条件」は、標数0・楕円曲線性・非零指数（行列式では素数指数）という通常の条件の下で、未構成の対データや非退化性・次数評価を追加の入力に取らないという意味である。

## 2. 教科書の読み順

| モジュール | 役割 |
| --- | --- |
| `Lib.NumberTheory.EllipticFunctionFieldNegation` | 群の反転を関数体の実際の自己同型へ持ち上げる |
| `Lib.NumberTheory.EllipticFunctionFieldGenerators` | 座標環と関数体が同じX,Yで生成されることを証明 |
| `Lib.Algebra.QuadraticInvolutionDegree` | 二次関係と反転を使い、次数上界の余分な2を除く一般代数 |
| `Lib.NumberTheory.EllipticMultiplicationPullback` | 非零倍一般点の非定数性、単射な座標代入、実際の倍写像の引き戻し |
| `Lib.NumberTheory.EllipticMultiplicationFunctionDegree` | Jacobianによるx座標式、反転で動くy、関数体全体の次数上界n² |
| `Lib.NumberTheory.EllipticMultiplicationFixedField` | 忠実なtorsion平行移動群・固定体・引き戻しの像の同定 |
| `Lib.Algebra.PullbackPrincipalPrime` | 局所付値上界と一重零点から主素イデアルを復元する一般代数 |
| `Lib.NumberTheory.EllipticMultiplicationValuation` | Jacobianによるy座標式、x・yの合同、有限場所の局所付値上界 |
| `Lib.NumberTheory.EllipticWeilNondegenerate` | 固定されたWeil関数の原像、主点イデアル、同じ対の非退化性 |
| `Lib.NumberTheory.EllipticGeometricWeilPairing` | 同じ値のRootPairing・WeilPairingDataと円分行列式 |
| `FLT.FreyGeometricWeilPairing` | 同じSourceの曲線・剰余表現への接続 |

全て`DkMath.`を接頭辞とする。本体11ファイル、名前付き定理・定義66個（補助local instanceを除く）。
日本語docstringとimport後の正確な`#print "file: ..."`を付けた。
一般代数を楕円曲線やFLTから分離し、曲線の幾何学は`DkMath.Lib`、Sourceへの接続は`DkMath.FLT`に置いた。
ルート`DkMath`と`DkMathTest`の通常入口にも接続した。

## 3. 028-A: 引き戻しの構成と余分な2の排除

一般点をγとする。もしnγ=O、またはnγが定数点なら、全ての定数点Sによる平行移動を作用させることでnS=Oが全点で成立してしまう。
既存の非零倍写像の全射性と実際の非零2-torsion点の存在がこれを排除する。
従ってnγは非零・非定数であり、`pointHom_injective_of_ne_baseChange`から座標代入は単射になる。
`multiplicationPull E n hn`はその単射を分数体へ延長した写像である。n=0で恒等写像へ置き換える定義は採用せず、`hn : n ≠ 0`を必須入力に保持する。

x座標は、既存の実際のJacobian倍写像から

\[
x([n]P)=\Phi_n(x(P))/\Psi\mathrm{Sq}_n(x(P))
\]

と表される。従ってxはμ(L)上で次数n²の方程式を満たす。
ただし、これだけではyを加える際に上界2n²しか得られない。

反転ιを座標代入から構成するとι(x)=x、ι(y)=−y−a₁x−a₃となる。
ι(μ(y))=μ(y)なら[n]γが自分自身の負の点となり、一般点の2n倍が零になってしまう。
既に証明した`generic_nsmul_ne_zero`を2nに使えば矛盾する。
この箇所では、模範解答の2-torsion除法多項式からの整性判定を再移植せず、同じ一般点の非零倍を再利用した。

一般代数補題`QuadraticInvolutionDegree.finrank_fieldRange_le`は、この条件からy∈μ(L)(x)を証明する。
yが属さなければ、その二次最小多項式の別の根ι(y)を使ってμ(L)(x)を固定する体準同型を作れる。
x,yで全体を生成するため、この写像はιに一致する。しかしμ(y)は基礎体μ(L)に含まれるので固定され、矛盾する。
従ってL=μ(L)(x)であり、関数体全体について上界n²となる。

## 4. 028-B: 点数と忠実性が固定体を決める

`torsionTranslation`は同じtorsion点Sを既存の`transEquiv S`へ送る。
NOTE-021の忠実性で単射、NOTE-019の`card_torsion_sq`でその像の群Hはn²個の元を持つ。
Mathlibの有限自己同型群の固定体定理から[L:Lᴴ]=n²となる。

一方、S∈E[n]なら[n](γ+S)=[n]γなので、`transEquiv_multiplicationPull`がμ(L)⊆Lᴴを与える。
028-Aの[L:μ(L)]≤n²と比較して、`IntermediateField.eq_of_le_of_finrank_le'`からμ(L)=Lᴴを得る。
`finrank_multiplicationPull`は同じ拡大の正確な次数n²を公開する。
`exists_multiplicationPull_of_invariant`は、不変関数に実際の原像hがあることを取り出す。
この段階だけで原像の位数や非退化性を主張しない。

## 5. 028-C: 局所上界と一重零点から点イデアルの主性へ

Pと[n]Pがともに有限点なら、ψₙ(P)≠0となる。
Jacobian表示からy([n]P)=ωₙ(P)/ψₙ(P)³も証明し、x・y両方の有理式を係数の基底変換と整合させる。
一般座標のPでの合同をこれらの有理式に輸送し、NOTE-024までの`valuation_pointPull_le`へ渡すことで

\[
v_{[n]P}(h)\le\exp(-k)\Longrightarrow
v_P([n]^*h)\le\exp(-k)\quad(k\in\mathbb N)
\]

を証明した。分岐指数1や付値の完全一致を追加仮定に取っていない。

同じWeil関数g=w_{n,T}が全torsion移動で固定されると仮定すると、028-Bからg=μ(h)となる。
有限場所のうち[n]P=Oとなる場所は`Option.none`として除外する。
その他を場所([n]P)へ送る写像Nは、既存の倍写像の全射性により全有限場所へ到達する。
NOTE-023の同じgの付値公式は、これらの場所で

\[
v_P(g)=\begin{cases}\exp(-1)&[n]P=T,\\1&[n]P\ne T\end{cases}
\]

となる。

一般代数補題`PullbackPrincipalPrime.exists_eq_span_of_eq_pullback`で、この情報を目標Tの主素イデアルへ戻す。
まずhの有限の極があれば、その逆数と局所上界を使ってgの付値と矛盾する。従ってhは座標環の整元rへ戻る。
rの零点はTだけで、Tで二重零点にもなれない。Tのイデアルを割り出した残余イデアルが非単位なら、その極大イデアルで新たな零点または二重零点が生じるため矛盾する。
よってm(T)=(r)である。

最後はNOTE-022の同じ曲線の点群→類群の単射へ戻り、`Point.toClass_eq_zero`からT=Oとなる。
ここではhの無限遠点を含む因子全体を別途計算せず、有限点イデアルの主性を直接証明している。
位数の降下を飛ばしたのではなく、必要な局所上界と単純零点の情報を使って主性を復元した形である。

NOTE-025の固有方程式に値1を代入すればgの不変性が得られるため、同じ双指標の右非退化性が成立する。
NOTE-026の反対称性から左非退化性も得た。

## 6. 同じWeil対データと円分行列式

`geometricRootPairing`は値c(S,T)=`weilTranslationUnit T S`をそのまま使う。
左右加法性、交代性、非退化性を証明済みの定理から供給し、値は既存の`weilAlternatingBicharacter`と定義的に同じである。
NOTE-027の同変性と合わせた`geometricWeilPairingData`は、既存の供給契約を実際のデータで満たす。

素数pでは既存の`torsion_determinant_eq_cyclotomic_of_pairing`へこのデータを渡し、追加の対データ入力を除いた`torsion_determinant_eq_cyclotomic`を得る。
同じSourceにも`residual_geometricWeilPairingData`、`residual_determinant_eq_cyclotomic`、`residual_apply_eq_pow_det`を公開した。
既存の条件付きAPIは保持し、新しい無条件の供給と終点を別名で追加した。

## 7. 回帰・監査・検証

名前付き回帰20個。Source 2で同じ引き戻しのx・y、反転、次数上界と正確な次数4、平行移動群の四元性、固定体同定を検査する。
既存の実際の有限点U（2U=(0,0)）で局所付値上界を測る。
非零目標(0,0)と(4,−2)について、あるtorsion移動が同じ対で必ず値1以外を与えることを証明した。
指定した二点どうしの対の数値そのものは計算していない。
指数1、指数37の正確な次数1369・非退化性、任意のSource 37の円分行列式と根への作用にも特殊化する。

依存監査は本体66・回帰20宣言の公理と、選択した21経路の型・opaque本体を検査する。
幾何学Coreでは`RootPairing`・`WeilPairingData`・torsion基底の借用を禁止する。
完成後のデータ構成ではそれらを実際に構成する経路を要求する。
行列式アダプタでのみ既存の基底と位数→次元の補題を許可し、実際の位数providerと新しい幾何学的対データの経路を要求する。
全ての経路で未移植provider・旧FLT終点・大域Kummer入力・`sorryAx`を禁止する。

検証結果は[evidence/validation-note028.txt](evidence/validation-note028.txt)に保存した。

- focused buildと依存監査: 3,260 jobs成功。本体66・回帰20宣言は標準論理公理のみ、21依存経路が成功。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: **11,658 jobs成功**。
- ルートimportのsmoke、A・B・CとSource行列式の`#print axioms`、`lake env lean DkMathTest.lean`: 成功。
- マーカー追跡、禁止構文・外部import走査、ライセンスパス、空白検査、`git diff --check`: 成功。

許容公理は`propext`、`Classical.choice`、`Quot.sound`。新規モジュール・最終smokeに警告はない。
統合ビルドの既存5件の`sorry`警告は今回の追加コード外にあり、新規監査経路では`sorryAx`を禁止している。

## 8. 参照した一次実装と残る算術

以下を閲覧し、生成されたP2MW名前空間やexportマクロを取り込まず、既存DkMathの自然数倍・一般点・局所付値・同じ比例定数へ翻訳した。
適応した9本体ファイルにはApache-2.0表示、原著作権、blob、既存LICENSE/NOTICEへの相対パスを保持した。

| 上流ファイル（anthropics/fermats-last-theorem） | blob |
| --- | --- |
| [関数体引き戻しの定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean) | `ce8783a9e9613db1c4c0323ce93fb0d89917ee65` |
| [一般点の非定数倍](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_zsmul_genericPoint_good.lean) | `30497c5e52c4e9998217349ad7763aa4adb60a85` |
| [関数体のx,y生成](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_adjoin_X_Y_eq_top.lean) | `a38b593248665652d1fcca051b48c11068c35a8f` |
| [二次反転による一般次数評価](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_finrank_fieldRange_le_of_adjoin_pair_eq_top.lean) | `e01f529774b1e737f1e000fc457b24c1080fca9e` |
| [倍写像の関数体次数](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean) | `346a32fb08ba430a7125a16d9c7b96c9608ea417` |
| [固定関数から零点への降下](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean) | `e82e468ec9dc155bbe1c531016cbd83735a3b037` |
| [単純零点から主素イデアル](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_eq_span_singleton_of_map_eq.lean) | `7b00f567f061b8924a0d23d55b057de611121a78` |

残るのは、Frey残余表現の既約性・局所慣性・導手・モジュラー性・レベル降下などの算術的接続である。
今回の無条件の幾何学的Weil対と円分行列式から、それらや一般FLTの完成を結論してはいない。
