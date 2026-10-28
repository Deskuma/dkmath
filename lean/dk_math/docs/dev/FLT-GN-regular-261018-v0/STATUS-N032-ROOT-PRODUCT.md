# NOTE-032: 2捩れ三根と一般判別式積公式への接続

## 今回固定したこと

標数2以外の体上の Weierstrass 曲線について、2捩れ三次式に相異なる三根
`e₁,e₂,e₃` があれば、その多重集合は全根に一致し、次が成立する。

- 三次式の値は `4 (x-e₁)(x-e₂)(x-e₃)`。
- 判別式は `16 ((e₁-e₂)(e₁-e₃)(e₂-e₃))²`。
- 曲線上の点では接線式 `(2y+a₁x+a₃)²` が上の三次式の値に等しい。

同じ幾何学的奇数核 `H` の既存の半核について、接線式の平方の積を、
`4^|halfKernel|` と三根それぞれへの距離積の積に分解した。奇数核の非零点は
反転固定点ではないので、接線式と三つの距離はいずれも非零である。
これは滑らかな核・特異な核のどちらにも共通する。

さらに、源と標的の三根に関する三組の差の関係を入力として、それらを掛け合わせ、
非零の距離積を消去して `Δ' U^4 = Δ^(2n+1)` を得る体の計算を固定した。
一組の差の関係を有理式評価と移動点の積の関係から導く補題もある。
消去計算は Anthropic の Vélu 判別式証明の `delta_identity` を参照して再構成し、
ソースのライセンスと blob をコード先頭に記録した。

今回さらに、2捩れ根 `(e₁, e₂, e₃)` と一般点 `(x,y)` の affine 加法について、
`x((e₁,0)+(x,y)) - e₂ = (e₁-e₂)(x-e₃)/(x-e₁)` を証明した。
これを根差関係と有限積の関係へ変換する API も追加したため、半核の各点での
平行移動公式を `pair_relation` の入力へ持ち上げられる。

さらに、根 `e` と移動根 `ξ q` から作るモニックな
`fiberFactor = (X-e) ∏ (X-ξ q)^2` を導入し、その評価公式を証明した。
その根の多重集合も `fiberFactor_roots` として固定し、一本の根と各移動根の
二重コピーに一致することを確認した。
これは上記の `hF` の右辺を多項式として明示する教科書層である。

その次数 `2 |s| + 1` と非零性も `fiberFactor_natDegree`、
`fiberFactor_ne_zero` として固定した。さらに、別のモニック多項式が同じ根の
多重集合を持ち、根が次数を尽くすなら `eq_fiberFactor_of_monic_of_roots` により
`fiberFactor` へ一意化できる。したがって、実際の `kernelXAt` の分子については、
根の同定と根数（次数）の確認を別々に証明すればよい。
評価の零点形 `fiberFactor_eval_eq_zero_iff` も追加し、評価値が零となる場合を
`z = e` または `z = ξ q`（`q ∈ s`）へ直接分解できるようにした。
さらに `fiberFactor_dvd_of_roots_le` により、根の多重集合の包含から
任意の非零多項式への可除性を得られるようにした。有限ファイバーの各根を
平行移動公式から供給できれば、既存の次数上界と組み合わせて因子同定へ進める。
その組合せを `eq_fiberFactor_of_monic_of_roots_le` として固定した。これは
モニック性、根の包含、`p.natDegree ≤ fiberFactor.natDegree` だけを仮定し、
根数上界の鎖から根の多重集合の等号を回収する。

幾何学側では `kernelAt_twoTorsion_root_translation` を追加した。反転固定点
`P` の標的2捩れ根への着地を、任意の `Q ∈ H` による平行移動へ輸送する。
これは軌道上の根の存在を供給するが、根の多重度・ファイバー全体の列挙は
まだ仮定していない。

この輸送を半核添字へ明示化した `kernelAt_twoTorsion_root_halfKernel` も追加した。
さらに `eq_halfKernel_fiberFactor_of_monic_of_roots_le` により、半核ファイバーの
根を多重集合として含むモニック分子が `|H|` 以下の次数を持つなら、
`fiberFactor` への一致を直接得られる。残る幾何学課題は、各軌道根の二重性を
`kernelXAt` の分子多項式へ供給することに限定された。

今回、`fullKernel_factor_eq_root_and_half_square` を追加した。反転不変な有限族
`ξ : H → AlgebraicClosure K` に対して、全核積を無限遠点の単純根と半核積の
平方へ分解する。したがって、半核の各根が `kernelXAt` の分子に二重に現れる
ことを別途示せば、全核側の因子分解へ直ちに戻せる。これは `ξ(-Q)=ξ(Q)` と
奇数核の半核分割だけを使う純粋な有限積の教科書定理であり、標的判別式の
無条件公式そのものではない。

また `eq_halfKernel_fiberFactor_of_monic_of_dvd_of_degree` を追加し、半核因子の
可除性から根の多重度包含を `Polynomial.roots.le_of_dvd` で回収した。したがって
実際の分子側では、(i) `fiberFactor ∣ p`、(ii) モニック性、(iii) 次数上界、の
三つを示せば因子同定が完了する。根を直接列挙する証明と可除性を先に示す証明の
二つの教科書ルートを、同じ `fiberFactor` API に揃えた。

さらに `kernelXAt_neg_translation_eq` と
`kernelXAt_fullKernel_factor_eq_root_and_half_square` を追加した。反転固定点
`P=-P` の軌道では、`P+(-Q)` と `P+Q` の特殊化 x 値が一致することを
`kernelXAt_neg` から導き、その有限族を全核積分解へ直接代入できる。これにより
「抽象的な反転不変族」から実際の `kernelXAt` 軌道積への幾何学的な橋ができた。
ただし各半核根が分子で二重になること、及びその分子がこの積を割ること自体は
まだ別証明であり、判別式積公式は引き続き条件付きである。

さらに `translated_root_product_relation` を追加し、各 affine 平行移動の
根差恒等式を有限積へ一括輸送した。これにより、半核点の曲線方程式と
`x ≠ e₁` という分母条件が揃えば、`product_root_difference_relation` の
入力を直接構成できる。

判別式積恒等式を局所計算へ渡す `discriminant_product_value` と
`discriminant_value_of_unit_factor` も追加した。前者は任意の線型順序付き
付値値群へ写し、後者は接線因子の付値1から商判別式の
`(2*n+1)` 乗則を得る。さらに `halfKernel_fiberFactor_natDegree` により、
奇数核では `fiberFactor` の次数 `2 |halfKernel| + 1` が `|H|` へ一致することを
半核分割定理から内部供給した。

今回の次段として `orbit_x_factor_eq_root_and_half_square` を追加した。これは
`ξ Q = (P + Q).xc` とする正しい有限ファイバー側の特殊化であり、反転固定点
`P` の x 軌道積を `P.xc` の単純因子と半核軌道積の平方へ分解する。従って、
`kernelXAt = c` の分子多項式へ軌道根を供給する際の重複度データが、抽象族では
なく実座標の形で利用できるようになった。

併せて `orbit_x_factor_eq_fiberFactor` を追加し、この軌道積を標準の
`fiberFactor (halfKernel E H) P.xc (fun Q => (P+Q).xc)` へ正規化した。以後の
多項式可除性・モニック因子同定はこの名前付き因子を直接使える。

さらに `orbit_x_injective_on_halfKernel` を追加した。核外条件と `P=-P` のもとで、
半核代表の x 軌道は単射である。x 座標の二点判定と半核の反転対排除を組み合わせ、
`fiberFactor` の二重根が異なる半核代表に対応することを明示した。これは根の
集合衝突を避けた上で、実分子の可除性を証明する次の入力になる。

また `orbit_x_root_ne_halfKernel` により、単純根 `P.xc` が半核軌道根のいずれとも
一致しないことを固定した。従って、実軌道から得た `fiberFactor` は「単純根一個」
と「互いに異なる半核根の二重コピー」へ分離される。ここまでで根の配置と次数は
確立した。

今回、一般代数層に `fiberFactor_dvd_of_rootMultiplicity` を追加した。`Option ι`
で単純根と二重根を一つの有限族へまとめ、根の分離から線型因子の pairwise
coprime 性を得て、局所多重度 `1` と `2` を `Finset.prod_dvd_of_coprime` で
全因子の可除性へ組み立てる。この定理は根の多重集合を手で展開せず、局所評価を
そのまま分子可除性へ運ぶ教科書用の共通核である。

さらに実軌道への特殊化として `orbit_x_fiberFactor_dvd_of_rootMultiplicity` を
追加した。核外条件と `P=-P` から既に確立した単射性・単純根分離を使い、`P.xc`
で一重、各半核軌道根で二重という入力だけで、実軌道の `fiberFactor` が `p` を
割ることを得る。`eq_orbit_x_fiberFactor_of_monic_of_rootMultiplicity` はそこへ
モニック性と次数上界 `natDegree p ≤ |H|` を加え、因子等号まで閉じる。
これにより、残る幾何学的課題は「`kernelXAt = c` の実分子について局所多重度
`1/2` を評価から供給すること」と明確化された。多重度供給をまだ自動化して
いないため、判別式積公式そのものは引き続き条件付きである。

続いて、評価零点から根多重度への最初の輸送を実装した。
`exists_veluX_fiber_polynomial_with_rootMultiplicity` は、既存の非零ファイバー
多項式 `p` と次数上界を保ったまま、`kernelXAt = c` の各点で
`1 ≤ p.rootMultiplicity P.xc` を供給する。さらに
`exists_veluX_fiber_polynomial_with_orbit_rootMultiplicity` は
`kernelXAt_translation` を使って、この一重根情報を `P+Q` の全核軌道へ運ぶ。
したがって、現時点で実分子から無条件に得られるのは「軌道全体が一重以上の根」
までであり、`fiberFactor` の二重因子へ進むには、なお別の分岐・接線評価が必要
であることを Lean の定理境界として固定した。

また `Polynomial.normalize` を用いた
`exists_veluX_monic_fiber_polynomial_with_rootMultiplicity` を追加した。非零性を
保ったままモニック性を供給し、`roots_normalize` と `natDegree_normalize` で根の
多重集合と次数上界を保存する。さらに
`exists_veluX_monic_fiber_polynomial_with_orbit_rootMultiplicity` により、モニック
分子と全軌道の一重根情報を同時に得られる。これで最終因子同定に必要な
「モニック性・次数・一重根」は自動供給され、未解決部分は半核根の二重性だけに
縮約された。

二重性の入口も `two_le_rootMultiplicity_of_isRoot_of_derivative_isRoot` として
一般化した。値零点と一階微分零点から `2 ≤ rootMultiplicity` を得るだけの
代数補題であり、`orbit_x_fiberFactor_dvd_of_derivative_roots` はこれを半核
軌道へ適用して `fiberFactor ∣ p` まで運ぶ。従って、今後の幾何学的分岐証明は
各 `P+Q` で `p` と `p.derivative` の同時零点を示す形へ整理できる。

さらに `eq_orbit_x_fiberFactor_of_monic_of_derivative_roots` を終端として追加
した。モニック性・次数上界・単純根の値零点に加え、半核軌道での値零点と微分
零点を入力すれば、実軌道 `fiberFactor` との多項式等号まで得られる。したがって
現在の完全な証明経路は、分子の構成 → モニック化 → 軌道値零点 → 軌道微分零点
→ 因子同定、という五段階に分離されている。

今回、一般有理関数ファイバー層にもこの分岐入力を固定した。
`fiberPolynomial_derivative_isRoot_iff_wronskian_isRoot` は、互いに素な分子・分母
`F,G` のファイバー `F-cG` の根上で、その微分零点と Wronskian
`F'G-FG'` の零点を同値にする。さらに
`rootMultiplicity_ge_two_of_fiberPolynomial_root_of_wronskian_root` は非零性を
加えて二重根を直接供給する。これにより、分子・分母の有理式計算で得た
Wronskian 条件を、根多重度 API が要求する微分条件へ形式的に変換できる。

この橋を奇数核の終端へ接続する
`eq_orbit_x_fiberFactor_of_monic_of_wronskian_roots` も追加した。各半核移動点
が同じファイバー根であり、かつ Wronskian がそこで消えるという入力から、上の
同値で軌道微分零点を生成し、`fiberFactor` との多項式等号まで一段で進める。
Wronskian の軌道零点自体は引き続き幾何学側の未解決入力であり、この定理は
その入力を隠さず保った条件付きの教科書終端である。

また `exists_veluX_coprime_rational` により、Vélu の `X_H` の RatFunc 表示から
分子・分母 `F,G` と `IsCoprime F G`、および次数等式を同時に取り出せるように
した。これで次段では、Wronskian の有限例外値論を `X_H` の実際の有理式へ
適用する際に、互いに素性を別途再構成する必要がない。

さらに、一般補題 `fiberPolynomial_natDegree_eq_of_natDegree_lt` と、Vélu の
無限遠点次数データを組み合わせた `exists_veluX_fiber_polynomial_exact_degree`
を追加した。これにより `F-cG` の次数上界は、任意の有限値で核位数に等しい
exact degree として扱える。非零性も同時に供給されるため、今後の
`rootMultiplicity`・モニック化・因子同定の入力が一つの定理から得られる。

さらに `exists_veluX_coprime_fiber_polynomial_exact_degree` を追加した。これは
同じ無限遠点次数データを、標準 RatFunc 表示の互いに素な分子・分母 `F,G` と
`veluX = F/G` の等式へ束ね、`deg G < deg F = |H|`、および有限ファイバー
`F-cG` の非零性と exact degree `|H|` を一つの証明オブジェクトとして公開する。
したがって、後段の Wronskian 零点判定は抽象的な分子の存在ではなく、実際の
Vélu 有理式の係数対へ直接適用できる。今回の補題は根の二重性をまだ供給せず、
その幾何学的入力を残すという境界も保持している。

加えて `exists_veluX_separable_coprime_fiber_avoiding` を固定した。exact degree
から分子の非定数性を得て `wronskian_ne_zero` を適用し、任意に指定した有限集合
`s` を避ける分離ファイバー値 `c` を構成する。出力には同じ `F,G`、`X_H = F/G`、
`deg G < deg F = |H|`、`c ∉ s`、`Separable (F-cG)`、および exact degree が
同時に含まれる。従って、有限例外値の除去と Vélu 有理式の次数管理を、後段の
分岐・根多重度証明へ渡す前処理として再利用できる。

一般有理関数層には `not_wronskian_isRoot_of_separable_fiberPolynomial` も追加
した。分離ファイバーでは各根の多重度が高々1なので、根上の Wronskian 零点は
存在しない。これにより、分離ファイバーの「一般値」経路と、軌道因子同定に必要な
Wronskian 零点を仮定する「分岐値」経路が、定理の型で相互排他的になる。

さらに、`fiberPolynomial_isRoot_of_veluX_eq_quotient` を追加した。これは任意の
非零分母 `G` と関数体恒等式 `X_H = F/G` を入力に、`kernelXAt P = c` から
`(F-cG).IsRoot P.x` を直接導く。RatFunc 表示を内部で選ぶ従来の存在定理と違い、
後段の Wronskian 計算で使う同じ係数対を保持したまま、点評価・付値合同・多項式
評価を接続する。

この橋を `eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_wronskian_roots`
へ接続した。核外の反転固定点 `P`、モニック性、次数上界、同じ `F/G` の
Wronskian 軌道零点を仮定すると、`kernelXAt P = c` と平行移動不変性から単純根と
全半核軌道根を自動生成し、有限ファイバー多項式を `fiberFactor` と同定する。
残る未実装入力は、半核軌道上の Wronskian 零点を幾何学から供給する部分に限定
された。

さらに `normalize_fiberPolynomial_eq_orbit_x_fiberFactor_of_veluX_quotient_of_wronskian_roots`
を追加した。実際の `F-cG` にモニック性を要求せず、非零性から `normalize` を
取り、根の多重集合と次数上界を保存して因子同定する。これにより、exact-degree
ファイバーの出力をそのまま受けて、モニックな `fiberFactor` へ進む代数層が完成
した。二重根の根元である Wronskian 軌道零点は引き続き明示入力として残る。

その逆向きとして `exists_wronskian_root_of_not_separable_fiber` も公開した。
非分離な有限値 `c` から、ファイバー根 `x`、Wronskian 根 `x`、および
`F.eval x / G.eval x = c` を同時に取り出す。これにより、例外値を有限集合へ
押し込めるだけでなく、各例外値の具体的な臨界根データを後段の軌道比較へ渡せる。

## 次に必要なこと

上の消去定理は一般判別式積公式の無条件の証明ではない。残る中心課題は、
実際の `kernelModel E H` の三根と、半核点の平行移動座標を同じ `ξ` として
`kernelXAt` のファイバー因数分解へ接続すること。
そのために、2捩れ点を半核点で平行移動した座標の積と、既存の有理関数の
分子多項式のファイバー分解を結び付け、上で追加した局所多重度入力を実際に
供給する必要がある。標的の三根は既存の
2捩れ像と分離定理から供給できるが、この接続自体は今回まだ実装していない。
したがって、一般核の判別式積公式・付値公式も従来どおり条件付きであり、
素数3の個別公式が一般核に拡張されたと主張しない。

## 検証

対象モジュールおよび具体例 `y²=x³-x` のテストをビルドし、三根と判別式64、
消去定理の退化しない計算例、付値輸送の自明付値例を検査した。主要定理の
`#print axioms` は `propext`, `Classical.choice`, `Quot.sound` のみ。
本サイクルでは `RationalPolynomialFiber`、`EllipticFiniteKernelRationalFiber`、
`EllipticFiniteKernelRootProduct` と既存テストモジュールの focused build、ならびに
`git diff --check` を実行した。
フルビルドは依頼側で確認済み、`lake test` はここでは実行していない。
