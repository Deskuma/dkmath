# 🐺 NOTE-024 レビュー — 無限遠点を含む付値輸送が完成

[NOTE-024 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE024-261021.md?utm_source=chatgpt.com)、主要な Lean 証明、依存監査と検証記録を照合した。

判定：NOTE-024 は無条件の幾何学 Core として固定を推奨する。

今回の進展は、これまで別々に扱っていた有限点と無限遠点 \(O\) を、同じ付値輸送の定理で統一したことじゃ。

### 1. 無限遠点に隠れていた一重極が確定

NOTE-022 の実際の生成元 \(f_{n,T}\) に対して、

\[ \boxed{ \deg\operatorname{Norm}(f_{n,T}) =n^2-\mathbf1_{T=O} } \]

を証明した。

ここでは任意の素イデアル冪の付値総和を経由せず、中国剰余定理（CRT）と剰余体の次元1を使って、相異なる有限零点を直接数えている。

これは DkMath の既存 Core に合わせた、実際の証明経路の短縮じゃ。

さらに、ノルム次数から無限遠点の離散付値を構成し、

\[ \boxed{ \operatorname{ord}_O(w_{n,T})= \begin{cases} -1&T\ne O,\\ 0&T=O \end{cases} } \]

を確定した。

以前予測した「有限点で数えたときに不足する1」が、関数体上の実際の付値として表現されたわけじゃな。

### 2. 平行移動の例外がなくなった

最も重要なのは、[`pointValuation_transEquiv`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticWeilTransport.lean?utm_source=chatgpt.com) じゃ。

任意の点 \(P,S\)、任意の有理関数 \(h\) に対し、

\[ \boxed{ v_P(\tau_S^\ast h)=v_{P+S}(h) } \]

を証明した。

この等式には、

\[ P=O,\qquad P+S=O \]

という例外も含まれる。しかも付値の等式は \(h=0\) の場合も成立する。

有限点間の輸送は割線・接線の局所合同から、無限遠点への輸送は付値環の分類と正規化から、それぞれ構成されている。

特に良いのは、付値環が同じという事実だけで、付値そのものが一致すると飛躍していないことじゃ。

値群への全射性を利用して正規化まで確定している。この点は `DiscreteValuationRigidity` に一般原理として分離された。

### 3. torsion による移動で、関数の零点・極が保存される

NOTE-023 の有限点公式が、NOTE-024 では全点の公式となった。

\[ \operatorname{ord}_P(w_{n,T}) = \mathbf1_{[n]P=T} - \mathbf1_{[n]P=O}. \]

ここで \(S\in E[n]\) とすると、

\[ [n](P+S)=[n]P. \]

従って、

\[ \boxed{ \operatorname{ord}_P(\tau_S^\ast w_{n,T}) = \operatorname{ord}_P(w_{n,T}) } \]

が、すべての点 \(P\) について成立する。

これが `pointOrder_transEquiv_weilFunction_of_torsion` の内容じゃ。

現段階では形式的な因子型を導入していないが、数学的には二つの非零有理関数の因子が一致することを、点ごとの位数で証明している。

### 検証について

取得した監査コードと保存された検証記録では、本体90宣言・回帰12宣言の公理監査、選択した11経路の依存監査、統合ビルド 11,625 jobs 成功を確認できた。

許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。今回の検査対象では、Weil 対の未構成データを借りず、有限点の局所幾何と無限遠点の付値を実際に接続している。

ただし、わっち自身が独立に Lean ビルドしたわけではない。また、既存の別モジュールの `sorry` 警告5件は残っている。

## NOTE-025：次は比例定数を、実際の関数体から取り出す

ここから先は、模範解答を参考にしながらも、かなり短い経路を取れそうじゃ。

確認したのは、Anthropic の二つの補題じゃ。

- [全有限場所で付値1なら定数](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.lean?utm_source=chatgpt.com)
- [平行移動による比例定数の存在](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq.lean?utm_source=chatgpt.com)

### 第一の橋：零点も極もなければ定数

非零有理関数 \(g\) が、すべての有限点で

\[ v_P(g)=1 \]

を満たすとする。

すると、Dedekind 整域の付値判定によって、

\[ g\in A,\qquad g^{-1}\in A \]

となる。ここで \(A\) は楕円曲線のアフィン座標環じゃ。

従って \(g\) は \(A\) の単元。

さらに楕円曲線のアフィン座標環では、単元は非零定数に限られる。

\[ \boxed{g\in\overline K^\times} \]

これは 任意の関数の付値情報から、実際の定数を復元する原理じゃ。

NOTE-024 にはノルム次数の一般的な計算道具もある。従って、単元が定数であることを既存の二元基底とノルム次数から示す経路も検討できる。

重要なのは、この補題の証明に、まだ Weil 対そのものを必要としないことじゃな。

### 第二の橋：平行移動による固有値

ここで、NOTE-022 の実際の関数をそのまま使う。

\[ w=w_{n,T},\qquad S,T\in E[n]. \]

新しい関数を仮定する必要はない。

\[ g=\frac{\tau_S^\ast w}{w} \]

と置く。

NOTE-024 の保存定理によって、すべての有限点で分子と分母の位数が一致する。

従って、

\[ \operatorname{ord}_P(g)=0, \qquad v_P(g)=1. \]

第一の橋から、

\[ g=c(S,T)\in\overline K^\times. \]

すなわち、

\[ \boxed{ \tau_S^\ast w_{n,T} = c(S,T)\,w_{n,T} } \]

を得る。

NOTE-025 の主定理として、わっちはこれを推奨する。

この \(c(S,T)\) は単に存在するだけでなく、一意じゃ。なぜなら \(w_{n,T}\ne0\) であり、定数体から関数体への埋め込みは単射だからじゃ。

さらに、生成元 \(f_{n,T}\) を非零定数倍で選び直しても \(c(S,T)\) は変化しない。

つまり、ここで新しい保存核が確定する。

### 第三の橋：比例定数から群準同型へ

平行移動の合成則を使えば、

\[ \tau_{S+S'}^\ast = \tau_S^\ast\circ\tau_{S'}^\ast \]

なので、

\[ \boxed{ c(S+S',T)=c(S,T)c(S',T) } \]

が従う。

また \(S\in E[n]\) なら、

\[ [n]S=O. \]

従って、

\[ \boxed{c(S,T)^n=1}. \]

すなわち、各 \(T\) を固定すると、

\[ \boxed{ c(-,T):E[n]\longrightarrow\mu_n } \]

という群準同型が得られる。

ここまでの推論には、まだ右側変数 \(T\) に関する双加法性も、非退化性も必要ない。

従って、NOTE-025 ではこの片側の乗法性までを無条件 Core として固定するのが適切じゃろう。

右側変数についての双加法性、

\[ c(S,T+T')=c(S,T)c(S,T'), \]

交代性、

\[ c(T,T)=1, \]

および非退化性は、次の独立した Frontier として残すべきじゃ。

## 研究上の位置づけ

NOTE-021 からの到達経路は、今やこうなった。

\[ \begin{aligned} &\text{Dedekind 座標環・関数体}\\ &\quad\Downarrow\\ &\text{ファイバーイデアルの主性}\\ &\quad\Downarrow\\ &\text{非零 Weil 関数候補}\\ &\quad\Downarrow\\ &\text{全点での零点・極の位数}\\ &\quad\Downarrow\\ &\text{平行移動による位数保存}\\ &\quad\Downarrow\\ &\boxed{\text{比例定数 }c(S,T)\text{ の存在と一意性}}\\ &\quad\Downarrow\\ &\text{乗法性と }n\text{ 乗根への着地} \end{aligned} \]

今回の NOTE-024 で、最後の二段を証明するための入力がそろった。

そして、もう一つ大切なことがある。

わっちは当初、無限遠点の輸送が大きな障害になると見ていた。しかし、今回ぬしがそれを無条件に閉じたことで、比例定数の構成では例外点を再び扱う必要がない。

`pointOrder_transEquiv_weilFunction_of_torsion` を一度使えば、以降は一般的な関数体と群作用の議論になる。

これは DkMath のモジュール分割が、うまく働いている証拠じゃな。

NOTE-024 は固定。NOTE-025 は「全有限付値が1なら定数」から始めて、Weil 関数の比例定数と片側の乗法性を証明する。

いよいよ、点の移動が関数の固有値として観測される段階に到達したのぅ。🐺🍎
