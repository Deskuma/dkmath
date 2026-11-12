# CF2D Intrinsic π — 第3次レビュー 🐺🍎

ぬしよ、最新コミット [`9e4063fdda4f`](https://github.com/Deskuma/dkmath/commit/9e4063fdda4f036a7b45b808468f4676f8ba6364) を確認したぞ。

今回の実装は、前回のレビューで求めた π-free の二次収束評価 を正しく取り込んでいる。さらに、抽象的な面積候補から、測度を持つ具体的なユークリッド平面の領域へ進んでおる。

`develop` との差分も確認した。対象ブランチは8コミット先行、遅れ0コミット。ブランチ運用については問題ない。

## 1. 誤差評価：合格

[IntrinsicBounds.lean](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicBounds.lean)

特に評価したいのが、今回追加された厳密な恒等式じゃ。

\[ \boxed{ U_n-A_n =\frac{A_{n+1}s_{n+1}^{\,2}}{c_{n+1}} } \]

ここには、CF2D の保存量、

\[ c_{n+1}^{\,2}+s_{n+1}^{\,2}=1 \]

が直接反映されている。

さらに、

\[ A_{n+1}\le4,\qquad c_{n+1}\ge\frac12,\qquad s_{n+1}\le2^{-n} \]

から、

\[ \boxed{ 0\le U_n-A_n\le8\cdot4^{-n} } \]

が従う。

`outerApprox_sub_areaApprox_eq` と `outerApprox_sub_areaApprox_le_quarter_pow` を確認したが、数式と実装の対応に問題は見当たらぬ。

そして、

\[ \boxed{ A_n\le\Pi_{\mathrm{CF2D}}\le U_n } \]

も既に証明されているため、上下それぞれの誤差評価まで得られる。

これは、円周率や三角関数を使わずに成立する、厳密な誤差保証じゃ。

CF2D の内在的定数の構成・収束・誤差評価は、一つの自立した数学的体系として成立している。

ただし、\(8\cdot4^{-n}\) は保証上界であって、実際の誤差と等しいわけではない。ここを区別している点も適切じゃ。

## 2. `IntrinsicPolygonMeasure.lean`：設計は妥当、面積定理は未完成

[ソースを見る](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygonMeasure.lean)

実装を確認すると、多角形領域は、

\[ K_n= \operatorname{conv} \{v_0,v_1,\ldots,v_{N_n-1}\} \]

として定義されている。

この領域について、既にコンパクト性・可測性・単位閉円盤への包含を証明しておる。

したがって、測度を扱うための基本条件は揃っている。

ただし、現段階の定理、

\[ \operatorname{volume}(K_n) \le\operatorname{volume}(B(0,1)) \]

は包含関係から得られる上界であり、面積候補 \(A_n\) との一致ではない。

また、`intrinsicPolygonRegion_volume_le_intrinsicPi` は、`intrinsicPi_eq_real_pi` と既存の円盤面積公式を利用している。

これは報告どおり、π-free な幾何学的証明ではない。

この依存関係を明示したうえで、未証明の主張を定理として扱っていない点は評価できるぞ。

## 3. 次の証明では、三角形分割を少し工夫したい

現在の `intrinsicPolygonFanTriangle` は、多角形の最初の頂点 \(v_0\) を共通頂点としている。

これは正しい方法じゃ。ただし、わっちなら 原点を共通頂点とする分割 も検討する。

\[ T_{n,j}= \operatorname{conv}\{0,v_j,v_{j+1}\} \]

こちらを使えば、既に証明されている、

\[ \det(v_j,v_{j+1})=s_n \]

が直接利用できる。

各三角形の面積は、

\[ \boxed{ \operatorname{Area}(T_{n,j})=\frac{s_n}{2} } \]

となるからじゃ。

辺数は \(N_n=4\cdot2^n\) なので、

\[ \begin{aligned} \sum_{j=0}^{N_n-1}\operatorname{Area}(T_{n,j}) &=\frac{N_ns_n}{2}\\ &=2^{n+1}s_n\\ &=A_n \end{aligned} \]

となる。

この計算にはπが一切登場しない。

ただし、原点が凸包に含まれること、三角形群が凸包を覆うこと、異なる三角形の内部が重ならないことは別途証明しなければならない。

既存の頂点ファンと原点ファンを比較し、Lean で証明しやすい方を採用するとよいじゃろう。

### Mathlib に使えそうな定理がある

現行の Mathlib ドキュメントには、次の定理が存在している。

`Affine.Simplex.volume_eq_volume_real_closedInterior`

これは、単体の幾何学的体積と、その内部のルベーグ測度を結び付けるものじゃ。


また、`Affine.Simplex.volume_eq` では、単体の体積を底辺と高さから求める定理も提供されている。


これらは今回必要な「三角形の測度と面積公式の接続」に有力な候補じゃ。

ただし、DkMath の依存バージョンは `Mathlib v4.34.1` なので、その固定バージョンにも補題が存在するか を、Codex に `#check` で確認させる必要がある。

## 4. さらに重要な発見：稠密性を先に証明する必要はない！

ぬしよ、わっちはここに、もっと直接的な経路を見つけた。

既に定義されている外接候補、

\[ U_n=\frac{A_{n+1}}{c_{n+1}} \]

を思い出してほしい。

既存の恒等式、

\[ A_n=c_{n+1}A_{n+1} \]

を使うと、

\[ \boxed{ U_n=\frac{A_n}{c_{n+1}^{\,2}} } \]

となる。

これは非常に重要じゃ。

内接正多角形の外接円半径は1。

その内接円半径は、

\[ r_n=c_{n+1} \]

である。

そこで、内接正多角形の凸包 \(K_n\) を、

\[ \frac1{c_{n+1}} \]

倍に拡大した領域を \(K_n^{\mathrm{out}}\) としよう。

この領域は、単位円に外接する正多角形になる。

したがって、

\[ \boxed{ K_n\subseteq B(0,1)\subseteq K_n^{\mathrm{out}} } \]

という幾何学的包含関係が成立する。

ここで、まだ証明していない三角形分割による面積定理、

\[ \operatorname{Area}(K_n)=A_n \]

が完成すれば、拡大による面積の倍率から、

\[ \operatorname{Area}(K_n^{\mathrm{out}}) =\frac{A_n}{c_{n+1}^{\,2}} =U_n \]

まで得られる。

すると測度の単調性により、

\[ \boxed{ A_n\le \operatorname{Area}(B(0,1)) \le U_n } \]

となる。

そして、今回すでに証明された、

\[ U_n-A_n\longrightarrow0 \]

を使うと、

\[ \boxed{ \operatorname{Area}(B(0,1)) =\Pi_{\mathrm{CF2D}} } \]

が導かれる！

この経路では、有限軌道の稠密性を別途証明する必要がない。

内接・外接する領域の測度を使って、円盤の面積を直接挟み込むことができるからじゃ。

ここまでの測度の接続をπなしで構成し、最後に既存の円盤面積公式と比較すれば、CF2D から `Real.pi` への別の証明経路になる。

これは次段階の設計として、非常に魅力的じゃ。

## 5. 残っている実装課題

わっちは、次の順序を推奨する。

1. 三角形の測度：\(\operatorname{Area}(T_{n,j})=s_n/2\) を証明。
2. 凸包の分割：三角形群が \(K_n\) を覆い、重複部分の測度がゼロであることを証明。
3. 面積の同一性：\(\operatorname{Area}(K_n)=A_n\) を証明。
4. 外接多角形：拡大領域 \(K_n^{\mathrm{out}}\) と単位円盤の包含関係を証明。
5. 幾何学的極限：内外の測度評価から、円盤面積が `intrinsicPi` に一致することを証明。

なお、今回の \(4^{-n}\) は誤差が等比的に減少する評価じゃ。数値解析でいう Newton 法などの quadratic convergence とは区別して記述すると、さらに正確になる。

## 賢狼の総合判定

今回の変更は採用してよい。新しい測度モジュールも、未完成部分を明確に分離しており、設計は妥当じゃ。

何より重要なのは、既に得られている、

\[ \boxed{ A_n\le\Pi_{\mathrm{CF2D}}\le U_n,\qquad U_n-A_n\le8\cdot4^{-n} } \]

という π-free の定理が、次の幾何学的証明にもそのまま使えることじゃ。

ぬしよ、ここまで来て初めて、われわれが最初に考えた 「正方形の対称性から円の面積を構成する」 という構想が、形式化可能な完全な証明経路として見えてきた。

わっちは、次の段階では稠密性よりも 内接・外接正多角形による円盤面積の挟み込み を優先したい。

これなら、これまで積み上げた CF2D の保存量、二分核、代数的面積、誤差上界が、すべて同じ証明の中で働く。

ふふっ。実に美しい数学的な構造になってきたのう！🐺🍎
