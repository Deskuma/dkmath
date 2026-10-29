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

今回、Vélu 有理式の標準 RatFunc 表示をさらに一つの教材用パッケージへ束ねた。
`exists_veluX_normalized_coprime_fiber_data` は、同じ `F,G` に対して
`IsCoprime F G`、`G ≠ 0`、`deg G < deg F = |H|`、`X_H = F/G`、非零ファイバー、
`normalize (F-cG)` のモニック性と exact degree、さらに核外点の評価根を同時に
返す。これにより、点評価から多項式の根、そこから軌道因子へ進む際に、表示を
途中で選び直す必要がなくなった。

その上で `exists_veluX_separable_or_wronskian_critical` を追加した。同じ実際の
Vélu 係数対と正規化データを保ったまま、有限ファイバーを、分離多項式を持つ
一般値か、具体的な `x` における `F-cG` と Wronskian の同時根および
`F.eval x / G.eval x = c` を持つ臨界値かに分類する。これは商曲線の非特異性や
判別式非零性を自動的に結論するものではないが、分離経路と分岐経路を同じ係数対
で比較するための境界を明示する。

さらに `exists_veluX_normalized_separable_fiber_avoiding` を追加した。任意の有限
例外集合 `s` を避ける分離値 `c` について、分母非零・非零ファイバー・正規化
モニック多項式・exact degree・核外点の根性まで一括して供給する。したがって、
一般値を使う局所計算ではこの補題だけを入口にでき、臨界値側では上記の二分岐の
Wronskian 根データへ切り替えられる。

最後に RootProduct 層から `exists_veluX_normalized_fiberFactor_of_wronskian_transport`
を追加した。これは Surjective 層の実際の係数対を選び、正規化ファイバーの
exact degree を未正規化次数へ戻し、既存の軌道因子同定定理を適用して、
`normalize (F-cG) = fiberFactor` を得る。仮定は基点 `P` のファイバー値と、
選ばれた `F,G` に沿った半核軌道上の Wronskian 零点だけであり、後者を幾何学から
供給する部分は明示的に未完了のまま残る。RootProduct はこの接続の所有モジュール
を直接 import し、`DkMath.Lib` 全体への依存を増やしていない。

## 今回の一般値ファイバー閉包

Wronskian の全半核軌道零点を要求するのは、反転固定点へ写る二捩れ分岐に
限られる。そこで `orbit_x_injective_of_two_smul_not_mem` を追加し、`2 • P ∉ H`
なら `Q ↦ (P + Q).xc` が全核上で単射になることを証明した。衝突の反転枝から
`2P ∈ H` を直接導くため、追加の次数仮定や非分岐 provider は不要である。

次に `fullKernel_factor_dvd_of_injective_roots` で、各軌道値が多項式の根なら
一次因子積がその多項式を割ることを、一次因子の互いに素性と
`Fintype.prod_dvd_of_coprime` だけで閉じた。`eq_fullKernel_factor_of_monic_of_injective_roots`
は、モニック性と次数 `≤ |H|` を加えて全軌道因子との等号を回収する。

さらに `exists_veluX_normalized_fullKernel_factor_of_two_smul_not_mem` は、実際の
Vélu 係数対 `F,G` を内部選択し、`kernelXAt P = c` と `2P ∉ H` から、正規化
ファイバー `normalize (F-cG)` を全核軌道の一次因子積へ同定する。したがって、
一般値ファイバーの因子分解は Wronskian 仮定なしで完了した。残る Wronskian
条件は、必然的に `2P ∈ H` の二捩れ分岐枝へ局在している。

この追加定理は、分岐枝の二重根を一般値の一次根計算へ混ぜないための重要な
境界線を提供する。一般核の判別式積公式を無条件にしたわけではなく、二捩れ枝の
局所接線・一様化計算は引き続き未実装である。

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

## 今回の無条件分岐閉包

残っていた `2 • P ∈ H` 枝を、有限奇数群の倍写像で正規化した。
`exists_two_torsion_translate_of_two_smul_mem` は
`Nat.Coprime.nsmul_right_bijective` と `Odd (Nat.card H)` から、ある `Q : H` に
対して `2 • (P - Q) = 0` を構成する。従って `T = P-Q` は反転固定点となる。

`exists_two_torsion_kernelXAt_representative_of_two_smul_mem` はさらに、元の
`P ∉ H` を保ち、`kernelXAt T = kernelXAt P` を平行移動不変性から証明する。
この結果、例外枝の任意の有限ファイバー値は、核外の二捩れ代表で評価できる。

`exists_two_torsion_kernelXAt_root_of_two_smul_mem` はその代表に
`kernelAt_twoTorsion_root` を適用し、標的二捩れ多項式の根と全 `T+Q` 軌道への
根輸送を供給する。これは根の存在までを無条件化するが、根の二重性はまだ
主張しない。

さらに `exists_two_torsion_kernelXAt_halfKernel_factorization_of_two_smul_mem` は、
同じ代表に全核軌道積の反転分解を適用し、単純根 `X-c` と半核積の平方を
無条件に得る。ここで確定した平方は点群軌道積の構造であり、正規化された
Vélu 分子がその積を持つことまでは含めない。

最後に `exists_veluX_normalized_fullKernel_factor_or_twoTorsion_root` を追加し、
任意の核外ファイバーを、

* `2 • P ∉ H`：正規化ファイバーの全核一次因子積（完全な因子等号）、または
* `2 • P ∈ H`：二捩れ代表、二捩れ根、全核軌道への根包含

の二枝へ分岐した。これでファイバーの入口は無条件に閉じた。一方、二捩れ枝を
`fiberFactor` 等号や判別式積へ進めるには、引き続き二重根（同値な微分零点／
Wronskian 軌道零点）の幾何学計算が必要であり、そこを仮定なしにしたとはしていない。

## 検証

対象モジュールおよび具体例 `y²=x³-x` のテストをビルドし、三根と判別式64、
消去定理の退化しない計算例、付値輸送の自明付値例を検査した。主要定理の
`#print axioms` は `propext`, `Classical.choice`, `Quot.sound` のみ。
本サイクルでは `RationalPolynomialFiber`、`EllipticFiniteKernelRationalFiber`、
`EllipticFiniteKernelSurjective`、`EllipticFiniteKernelRootProduct` と既存テスト
モジュールの focused build、ならびに `DkMath.Lib` の再ビルドと `git diff --check`
を実行した。RootProduct の新しい直接 import と係数対からの条件付き因子同定も
ルートビルドで確認済みである。
フルビルドは依頼側で確認済み、`lake test` はここでは実行していない。

## 今回の有限根住所の数え上げ

模範解答の `injOn` による根数評価を、DkMath の軌道 API へ移した。
`card_orbit_x_image_of_two_smul_not_mem` は、`2 • P ∉ H` の一般枝で
`Q ↦ (P + Q).x` の像がちょうど `|H|` 個であることを証明する。
これは既存の全核因子等号と同じ単射性を、有限集合の濃度として公開したもの
である。

二捩れ枝では `card_halfKernel_orbit_x_image` により、半核上の x 根が
`|halfKernel|` 個であることを固定した。さらに
`card_distinguished_halfKernel_root_set` は単純根 `P.x` と半核根が衝突せず、
異なる根の住所が `|halfKernel| + 1` 個になることを示す。`fiberFactor` の
次数 `2 * |halfKernel| + 1` は半核根を二重に数えるため、この集合濃度と多重度を
明確に分離できる。

このサイクルでも、二重根そのものや Wronskian の軌道零点は導入していない。
従って、判別式積の局所計算は引き続き別入力であり、今回の成果は根の住所と
重複度を接続する有限組合せ層に限定される。

## 今回の Wronskian 局所接続

Wronskian の幾何学的零点を優先し、既存の `veluX_half` と `veluZ_half` の
各反転対補正を分母消去した新規モジュール
`EllipticFiniteKernelWronskian` を追加した。半核全体の和を直接再展開せず、
一対の補正項に対して

* `xCorrectionNumerator` と `xCorrectionDenominator` による
  `xCorrection = N / D` の評価表示を確立し、
* `N' D - N D' = (X-a) Z` を多項式恒等式として証明し、
* その評価版 `xCorrection_numerator_wronskian_eval` と、非零分母上で
  `N'(x)D(x)-N(x)D'(x)=(x-a)^4 zCorrection(x)` と書く
  `xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection` を公開した。

ここで `Z` は `zCorrection` の分母を払った分子であり、既存の
`translated_pair` が使う平方完成座標補正と同じ係数を持つ。従って、今回実際に
新しく証明した数学的内容は、Vélu の一対補正における形式微分と Wronskian の
厳密な局所恒等式である。証明は `Field` 上の多項式微分、評価、分母消去、
`ring` に限定され、有限核・楕円性・二捩れ点の仮定を必要としない。

`veluX_half`、`veluZ_half`、`translated_pair` との関係は既存定理の組合せであり、
今回のファイルではそれらを再証明していない。また、この局所恒等式だけから
実際の半核和の係数対 `F,G` に対する
`W(F,G)(x(T+Q)) = 0` を結論してはいない。未解決の義務は、各補正項の共通分母を
半核全体で組み立て、`veluZ_half` の平方完成表示をその分子・分母の微分へ
移すことである。さらに二捩れ点 `T` での反転固定と `T+Q` の根輸送を用いて、
その組み立てた Wronskian が実際に消えることを示す必要がある。

次の具体的な補題は、半核添字 `Q` に対する `x(T+Q) ≠ x(S)` の幾何学的非衝突を
証明し、`hxa : ∀ i ∈ s, x ≠ a i` を実際に供給することである。その後、
`veluX_half` の関数体係数対と `finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z`
を接続し、二捩れ点で平方完成座標が零となる局所評価を加えれば、目標の二重根／
Wronskian 零点へ進める。

## Wronskian 層の検証

`lake build DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskian` と
`lake build DkMath.Lib` は成功した。新規定理
`xCorrection_eq_eval_numerator_div_denominator`、
`xCorrection_numerator_wronskian_eq`、
`xCorrection_numerator_wronskian_eval`、
`xCorrection_numerator_wronskian_eval_eq_pow_mul_zCorrection` の
`#print axioms` はいずれも
`propext`, `Classical.choice`, `Quot.sound` のみで、新しい `sorry` や独自
`axiom` は導入していない。`git diff --check` も実行済みである。
回帰入口として `DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskian` を追加し、
公開した局所定理を一般の体上で再利用できることも focused build で確認した。
重い `lake test` 全体は依頼の運用方針に従い、このサイクルでは省略した。

## 有限積への Wronskian 持ち上げ

レビューで指定された式 (1) を、曲線に依存しない新規モジュール
`DkMath.Lib.Algebra.FiniteProductWronskian` に実装した。有限集合 `s`、
分子族 `N`、分母族 `D` に対して、

`Eᵢ = ∏ⱼ∈s.erase i Dⱼ`,
`D = ∏ᵢ∈s Dᵢ`,
`A = X D + Σᵢ Nᵢ Eᵢ`

を定義し、

`A' D - A D' = D² + Σᵢ Eᵢ² (Nᵢ' Dᵢ - Nᵢ Dᵢ')`

を `commonNumerator_wronskian_eq` として証明した。有限積の微分は
巨大展開に頼らず、積・和の微分則、除去積 `Finset.prod_erase_mul`、
局所ごとの `ring` に分解している。

さらに `commonNumerator_wronskian_eq_of_local` を追加し、局所 Wronskian を
任意の `Z i` に置き換えられる形を公開した。これを既存の一対補正恒等式へ
適用する `finite_xCorrection_wronskian_eq` も追加したため、Vélu 補正族について

`A' D - A D' = D² + Σᵢ Eᵢ² (X-C(aᵢ)) Zᵢ`

が無条件に得られる。これはレビューの式 (2) に対応する新しい確立部分である。

さらに `finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z` を
追加した。各 `x-aᵢ` の非零性を仮定すれば、点評価後に

`W(A,D)(x) = D(x)² (1 + Σᵢ zCorrectionᵢ(x))`

という式 (3) を得る。ここで必要な分母非零条件はまだ半核の幾何学から供給せず、
`hxa : ∀ i ∈ s, x ≠ a i` として明示している。この分離により、次工程では
`T+Q` と半核点の x 座標非衝突をこの仮定へ渡せばよい。

この段階では、まだ `veluX_half` の実際の半核添字と関数体係数を代入していない。
従って標準 `RatFunc` 表示の `F,G` との交差乗算、
二捩れ点 `T+Q` での Wronskian 零点は未解決である。次の具体的な補題は、
半核族の各分母 `Dᵢ(x)` の非零性と `D(x)=∏Dᵢ(x)` の非零性を接続し、
この有限積恒等式を `veluZ_half` の評価式へ輸送することである。

今回の検証では、対象の有限積モジュール、Vélu 補正族モジュール、回帰テスト、
`DkMath.Lib` を focused build した。新規公開定理の `#print axioms` は
いずれも `propext`, `Classical.choice`, `Quot.sound` のみである。

## 実半核への共通分母特殊化

レビューの次工程として、一般有限積を実際の `halfKernel E H` に代入した。
新規モジュール `DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianHalf` では、
関数体上の多項式族

* `veluHalfNumerator E H := commonNumerator (halfKernel E H) N D`、
* `veluHalfDenominator E H := commonDenominator (halfKernel E H) D`

を定義した。ここで `N Q` と `D Q` は既存の `xCorrectionNumerator` と
`xCorrectionDenominator` を半核点の座標へ特殊化したものである。

一般評価補題 `commonNumerator_eval_div_commonDenominator` を用い、
`genericX` が半核点の定数 x 座標と異なることを
`genericX_ne_const` から供給した。その結果、分母因子の非零性
`veluHalf_denominator_factor_ne_zero` と、既存の `veluX_half` を組み合わせた

`veluX_eq_veluHalfNumerator_div_denominator`

を無条件に証明した。すなわち、Vélu x 座標は実半核で構成した共通分母表示
`A_H / D_H` の関数体評価と一致する。新規部分は分母評価の非零性と有限分数和の
通分であり、`veluX_half` 自体や局所補正の式は既存定理を組み合わせている。

この段階で未解決なのは、`veluZ_half` を同じ `A_H,D_H` の Wronskian へ接続する
無分母恒等式、二捩れ軌道での `D_H ≠ 0` と `z_H = 0` の同時評価、標準
`RatFunc` 係数対への輸送である。従って、実半核特殊化は完了したが、
`W(A_H,D_H)(x(T+Q)) = 0` および標準 `W(F,G)` の零点まではまだ到達していない。

次に攻める具体的な補題は、`veluZ_half` の補正和を各局所
`zCorrectionNumerator` へ通分し、`D_H^2 z_H = z W(A_H,D_H)` を関数体上で
証明することである。その後、二捩れ点の局所評価と `RatFunc` 交差乗算法へ進む。

対象モジュール `EllipticFiniteKernelWronskianHalf`、回帰テスト
`DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskian`、および
`DkMath.Lib` の focused build は成功した。回帰テストの `#print axioms` で
`veluHalf_denominator_factor_ne_zero` と
`veluX_eq_veluHalfNumerator_div_denominator` はいずれも
`propext`, `Classical.choice`, `Quot.sound` のみを報告した。

## 平方完成座標と Wronskian の接続

さらに、上の有限評価公式を既存の `veluZ_half` に直接代入し、
`veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian` を追加した。この定理は、
`F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField`、
`x := genericX E (AlgebraicClosure K)`、
`z := 2 * genericY + a₁ * x + a₃` と置いたとき、

`D_H(x)^2 * z_H = z * (A_H'(x) D_H(x) - A_H(x) D_H'(x))`

を関数体上で証明する。証明は、
`finite_xCorrection_wronskian_eval_eq_denominator_sq_mul_one_add_z` と
`veluZ_half` の二つの既存表示を同じ補正和へ正規化し、最後に可換体上の
`ring` で因子を並べ替える構造である。したがって、ここで新しく閉じたのは
有限補正族の Wronskian と平方完成座標を結ぶ無分母恒等式であり、まだ特定点の
評価や二捩れ性を仮定していない。

残る境界は、`z = 0` となる二捩れ軌道点への正則評価、共通分母の非零性をその
点で供給する幾何学的非衝突、および標準 `RatFunc` の係数対 `F,G` へ
Wronskian を輸送することである。次の具体的な補題は、点評価 API を使って
この恒等式を `T + Q` へ特殊化し、`D_H(x(T+Q)) ≠ 0` と
`z_H(T+Q) = 0` から `W(A_H,D_H)(x(T+Q)) = 0` を得ることである。

この新定理も回帰テストで再利用し、`#print axioms` は
`propext`, `Classical.choice`, `Quot.sound` のみを報告した。

## 代数閉包係数への基底橋渡し

レビューで指摘された「関数体係数多項式を評価の単射性なしに比較しない」という
境界を明示するため、新規モジュール
`DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianBase` を追加した。
ここではまず

* `veluHalfNumeratorBase E H : (AlgebraicClosure K)[X]`、
* `veluHalfDenominatorBase E H : (AlgebraicClosure K)[X]`

を定義し、同じ半核の有限積を代数閉包係数で構成する。そのうえで
`moments_map` と `Polynomial.map` の有限和・有限積との可換性から、

`map_veluHalfNumeratorBase`、`map_veluHalfDenominatorBase`

を証明した。従って、関数体係数の `A_H,D_H` は、係数埋め込み
`AlgebraicClosure K →+* FunctionField` による基礎体側の `A₀,D₀` の像として
扱える。評価写像の非単射性を使った多項式同一視は行っていない。

さらに、任意の体準同型に対する
`map_wronskian` を追加した。多項式の微分が係数写像と可換することを
`derivative_map` で明示し、Wronskian の係数体輸送を代数的に固定した。
これは将来、標準 `RatFunc` の分子分母対 `F,G` と `A₀,D₀` を交差乗算で比較する際の
入口になる。

新しく確立した内容は、半核有限積の係数体降下と Wronskian の写像可換性である。
`veluX_half`、`veluZ_half`、および二捩れ点の幾何学的評価は既存定理を利用するだけで、
この段階ではまだ閉じていない。未解決の証明義務は、`T+Q` における各分母因子の
非零性、`z_H(T+Q)=0` と `z(T+Q)≠0` の同時供給、そして関数体恒等式の正則な点評価である。

対象モジュール、回帰テスト、`DkMath.Lib` のビルドを実行した。新規橋渡し定理の
`#print axioms` は既存層と同じく `propext`, `Classical.choice`, `Quot.sound` のみで、
新しい `sorry` や独自 `axiom` は導入していない。`git diff --check` も成功した。

## 二捩れ局所特殊化の入口

新規モジュール
`DkMath.Lib.NumberTheory.EllipticFiniteKernelWronskianSpecialization` を追加した。
これは Wronskian 恒等式を再展開する層ではなく、既存の点評価 API と反転公式を
二捩れ軌道へ接続する教科書用の局所入口である。

新しく無条件で証明した定理は次の通りである。

* `eq_neg_of_completedSquare_eq_zero`：有限点 `P ≠ 0` の平方完成座標
  `2 y(P) + a₁ x(P) + a₃` が零なら `-P = P`。
* `completedSquare_ne_zero_of_neg_ne`：反転で固定されない有限点では、同じ
  平方完成座標が非零。
* `kernelAt_completedSquare_eq_zero_of_neg_fixed`：核外の反転固定点の像は、
  `kernelModel` の平方完成座標が零。
* `kernelAt_completedSquare_eq_zero_of_neg_fixed_translation`：上の零性を
  核点による平行移動 `P + Q` へ輸送する。

前二定理は Weierstrass 反転公式の座標計算だけで閉じ、後二定理は既存の
`kernelYAt_neg`、`kernelXAt_translation`、`kernelYAt_translation`、および
モデル係数の書換えを組み合わせたものである。これにより、軌道点 `T + Q` に
対して標的側の `z_H = 0` を供給する形式的な入口が得られた。ただし、ここでは
まだ `T` の二捩れ性を自動生成しておらず、源側の `z(T+Q) ≠ 0`、共通分母
`D_H(x(T+Q)) ≠ 0`、関数体恒等式の正則な点評価も未解決である。

回帰テストへ三つの `example` と新定理の `#print axioms` を追加した。対象モジュール、
`DkMathTest.Lib.NumberTheory.EllipticFiniteKernelWronskian`、`DkMath.Lib` を
focused build し、いずれも成功した。新定理の依存公理は
`propext`, `Classical.choice`, `Quot.sound` のみであり、`sorry` と独自 `axiom` は
導入していない。`git diff --check` も成功した。

次に攻める具体的な補題は、既存の二捩れ根 API から `T + Q` の源側反転非固定性を
取り出し、`D_H` の各有限積因子が非零であることを同時に与える点評価補題である。
それが閉じれば、既に確立した
`D_H^2 z_H = z W(A_H,D_H)` を `T + Q` へ特殊化して、まず基底係数対の
`W(A₀,D₀)(x(T+Q)) = 0` を得る段階へ進める。

## `T + Q` の局所評価パケット

局所特殊化モジュールを拡張し、
`completedSquare_ne_zero_of_neg_ne_translation` と
`completedSquare_translation_pair` を追加した。前者は `P ∉ H` から
`P + Q ∉ H` を示し、反転非固定という明示的な入力のもとで源側の平方完成座標
が非零であることを返す。後者はこの非零性と、既存の
`kernelAt_completedSquare_eq_zero_of_neg_fixed_translation` による標的側零性を
一つの論理積に束ね、次の点評価定理へ直接渡せる形にした。

ここで `-(P + Q) ≠ P + Q` は意図的に仮定として保持している。奇数核の位数から
この非反転性を供給する群論補題は、今回の座標・Wronskian 層と混ぜず、既存の
`eq_zero_of_mem_odd_kernel_fixed` を利用する別の輸送補題で閉じるべき証明義務である。
したがって、今回の追加は既存定理の組合せによる構造整理であり、まだ共通分母の
点評価非零性や Wronskian 零点そのものを主張していない。

新しい回帰例と `#print axioms` を追加し、対象モジュールおよび回帰テストの
focused build は成功した。新定理の公理依存は
`propext`, `Classical.choice`, `Quot.sound` のみである。

## 奇数核による非反転性の閉包

さらに `neg_ne_of_odd_kernel_twoTorsion_translate` を追加した。`P` が反転固定で、
`Q : H` が非零なら、`H` の位数が奇数である限り `P + Q` は反転固定でない。
証明は、反転固定を仮定して `P+P = 0` と `(P+Q)+(P+Q)=0` を比較し、
`Q+Q = 0` を得る。`eq_zero_of_mem_odd_kernel_fixed` によって `Q = 0` となり、
非零仮定に矛盾する。このため、`completedSquare_translation_pair_of_odd_kernel`
では `hnegTranslation` を外部入力から除去し、奇数核・非零核点だけで源側非零性と
標的側零性のペアを供給できるようになった。

ここまでで、二捩れ核外点 `P` と非零核点 `Q` に対する平方完成座標の局所条件は、
点評価へ渡せる形で閉じた。未解決なのは依然として `D_H` の有限積因子の点評価非零性と、
関数体上の無分母 Wronskian 恒等式をこの点へ特殊化する正則性である。

## 共通分母の点評価非零性

最後に `veluHalfDenominatorBase_eval_ne_zero` を追加した。半核の各代表 `Q` と
評価点 `R` の x 座標が衝突しないという条件から、基礎係数体側の共通分母
`D_H` の評価が非零になることを、有限積の各因子へ分解して証明する。
`xCorrectionDenominator a = (X - a)(X - a)` の形を直接評価するため、分母非零性を
関数体の超越性に依存せず、実点側の衝突判定へ切り出せる。

従って現在の局所データは、奇数核と非零半核代表から源側の平方完成座標非零性、
標的側の平方完成座標零性、および x 座標非衝突を仮定した共通分母非零性をそれぞれ
供給できる。残る中心課題は、この三つを
`veluHalf_denominator_sq_mul_z_eq_z_mul_wronskian` へ正則に特殊化し、
`W(A₀,D₀)(x(T+Q)) = 0` を閉じることである。

さらに `translated_x_ne_halfKernel_of_kernel_outside` と
`veluHalfDenominatorBase_eval_ne_zero_translation` を実装した。前者は、
`P ∉ H` ならば `x(P + Q)` が半核の任意の代表 `S` の x 座標と一致しないことを
示す。x 座標が一致した場合に `point_eq_or_eq_neg_of_xc_eq` を適用し、
`P = S - Q` または `P = -S - Q` として核所属を導くため、二捩れ性や標的楕円性を
追加仮定しない。後者はこの衝突排除を有限積の各因子へ代入し、任意の核点移動
`P + Q` で `D_H(x(P+Q)) ≠ 0` を無条件に供給する。

この結果、Wronskian の点特殊化に必要な分母非零性は、実点の x ファイバーの
基本事実と `P ∉ H` だけで閉じた。残る未解決義務は、関数体恒等式の評価写像を
基礎係数多項式へ移し、`z_H(P+Q)=0` と `z(P+Q)≠0` を用いて実際の
`W(A₀,D₀)` 零点へ到達することである。

## 標準分子・分母対への Wronskian 根輸送

さらに `DkMath.Lib.Algebra.WronskianCrossMultiplication` を追加した。
ここでは、同じ有理関数を表す多項式対について交差乗算
`F * D = A * G` を仮定すると、微分後の整理だけから
`W(F,G) * D^2 = W(A,D) * G^2` を得る
`wronskian_mul_denominator_sq_eq` を証明している。この定理は体上の一変数
多項式だけに依存し、Vélu や楕円曲線の構造を要求しない。

その評価版として、`wronskian_isRoot_of_cross_relation` と
`wronskian_isRoot_of_cross_relation_rev` を実装した。前者は共通分母 `D` の
評価が非零なら、`W(A,D)` の根から `W(F,G)` の根を得る。後者は標準分母 `G`
の非零性を使って逆向きに輸送する。したがって、今後 `A₀,D₀` と標準
`RatFunc` 対 `F,G` の交差乗算だけが確立すれば、既存の軌道因子定理が要求する
Wronskian 根条件へ直接接続できる。

この段階でも、交差乗算そのものを関数体の評価一致から自動的に導くことはしていない。
係数体 `AlgebraicClosure K[X]` での `A₀,D₀` と標準 `RatFunc` 表示の比較が、
依然として次の独立した証明義務である。新定理の回帰例と `#print axioms` を追加し、
公理依存は既存と同じく `propext`, `Classical.choice`, `Quot.sound` に限定した。

さらに `wronskian_isRoot_of_denominator_cleared_identity` を追加した。これは評価済みの
無分母式
`D(x)^2 * z_H = z * W(A,D)(x)`
に `z_H = 0` と `z ≠ 0` を代入し、`W(A,D)(x) = 0` を取り出す最後のスカラー消去を
一般体上で閉じる補題である。したがって、実際の楕円曲線側では、正則な点評価と
係数降下を用いてこの仮定を供給すればよく、二捩れ幾何と Wronskian の根抽出を
別々の層に保てる。

加えて `cross_relation_of_aeval_div_eq` を実装した。係数体 `R` 上の多項式対を
拡大体 `S` の超越元 `x` で評価し、両分母の評価非零性と分数等式を与えると、
`Polynomial.aeval` の単射性から `F * D = A * G` を係数多項式の等式として回収する。
これは「関数体係数多項式をそのまま評価して係数等式と誤認する」危険を避けるための
形式的な係数降下の入口である。残る作業は、実際の標準 `RatFunc` 対 `F,G` と
`veluHalfNumeratorBase`, `veluHalfDenominatorBase` の評価分数等式、ならびに
`genericX` の超越性と分母評価非零性を一つの専用補題へ束ねることである。

このうち `genericX` の超越性は、`genericX_transcendental_for_wronskian` として
既存の無限遠点の二位極評価から公開した。これで係数降下側に必要な単射性の入力は
独立した教材定理になった。標準対との評価分数等式と、有限点での正則評価だけが
残るため、次工程は「標準 `RatFunc` 対を基礎共通分母対へ接続する専用定理」に
絞り込める。
