# 🐺🍎 NOTE-027 レビュー — Weil 双指標のガロア同変性が完成

うむ、ぬしよ。これで NOTE-026 の交代的双指標が、実際のガロア表現とも結び付いたのじゃな。

[NOTE-027 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE027-261021.md?utm_source=chatgpt.com)、Lean の主要な証明本体、回帰・依存監査、検証記録を照合した。

判定：NOTE-027 は無条件の幾何学 Core として固定を推奨する。

今回確定した中心定理は、同じ Weil 関数から取り出した比例定数についての

\[ \boxed{ c(\sigma S,\sigma T)=\sigma\bigl(c(S,T)\bigr) } \]

じゃ。

ここで \(\sigma\) は基礎体 \(K\) の絶対ガロア群の元、\(S,T\in E[n]\) である。

### 何が証明として重要だったか

まず、[`EllipticFunctionFieldGalois.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticFunctionFieldGalois.lean?utm_source=chatgpt.com) では、座標環への係数作用を実際に構成し、関数体へ延長している。

この作用 \(\Phi_\sigma\) は、係数について半線形じゃ。

\[ \Phi_\sigma(af)=\sigma(a)\Phi_\sigma(f). \]

そして、平行移動との交換則

\[ \boxed{ \Phi_\sigma(\tau_S^\ast f) =\tau_{\sigma S}^\ast (\Phi_\sigma f) } \]

を証明している。

次に、有限場所の付値を正規化ごと輸送し、

\[ v_{\sigma P}(\Phi_\sigma f)=v_P(f) \]

を得ている。付値環が対応するだけで済ませず、素イデアル冪への所属から実際の離散付値の値を照合している点がよい。

### 生成元の任意性が消える

ここが NOTE-027 の核心じゃろう。

NOTE-022 で作った Weil 関数の生成元は、ガロア作用の下で文字どおり一致するとは限らない。

そのため、正しくは

\[ \boxed{ \Phi_\sigma(w_{n,T}) =a_{\sigma,T}\,w_{n,\sigma T}, \qquad a_{\sigma,T}\in\overline K^\times } \]

となる。

[`EllipticWeilGalois.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticWeilGalois.lean?utm_source=chatgpt.com) の `existsUnique_scalar_galois_weilFunction` は、この定数の存在と一意性を実際の付値比較から証明している。

そして、既存の固有方程式

\[ \tau_S^\ast w_{n,T}=c(S,T)w_{n,T} \]

に \(\Phi_\sigma\) を適用すると、

\[ a_{\sigma,T}\tau_{\sigma S}^\ast w_{n,\sigma T} = \sigma(c(S,T))a_{\sigma,T}w_{n,\sigma T}. \]

非零定数を消去し、NOTE-025 の固有値の一意性へ渡す。

これで、生成元の任意性を残さずにガロア同変性が得られる。

新しい Weil 対を仮定していない。NOTE-025・026 と同じ値を、そのままガロア作用へ接続している。

### 既存の剰余表現への接続

`weilAlternatingBicharacter_representation` によって、

\[ \boxed{ e_n(\rho_n(\sigma)S,\rho_n(\sigma)T) = \sigma(e_n(S,T)) } \]

も成立した。

これは NOTE-018 の円分行列式定理に必要な同変性と同じ内容じゃ。ただし、非退化性はまだ必要である。

取得した検証記録では、本体46宣言・回帰14宣言の公理監査、13経路の依存監査、統合ビルド 11,645 jobs 成功を確認した。許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。既存の別モジュールにある `sorry` 警告5件は、今回の監査経路とは別じゃ。

なお、これはソースと保存された検証記録に基づくレビューであり、わっち自身による独立ビルドではない。

## NOTE-028 — 非退化性の最短経路を確認した

模範解答の [eq_zero_of_forall_transEquiv_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean?utm_source=chatgpt.com) を調べると、次に証明すべきものが明確になる。

今回、DkMath に既に存在する Core が特に役立つ。

NOTE-019 の \(|E[n]|=n^2\)、NOTE-021 の平行移動作用の忠実性、そして NOTE-016 の除法多項式の次数 \(n^2\) じゃ。

### 1. 固定体の次数は既存 Core から得られる

\[ L=\overline K(E),\qquad H=\{\tau_S^\ast :S\in E[n]\} \]

とする。

平行移動作用は忠実なので、

\[ |H|=|E[n]|=n^2. \]

有限自己同型群の固定体定理から、

\[ \boxed{[L:L^H]=n^2}. \]

ここで NOTE-021 の `transEquiv_injective` と NOTE-019 の `card_torsion_sq` を直接利用できる。

### 2. 最大の新規証明は倍写像の関数体次数

倍写像の引き戻しを

\[ [n]^\ast :L\hookrightarrow L \]

として構成する。

\([n]S=O\) であることから、

\[ [n]^\ast L\subseteq L^H \]

が成立する。

ここで、さらに

\[ \boxed{[L:[n]^\ast L]\le n^2} \]

を証明できれば、両方の拡大次数の比較によって

\[ \boxed{L^H=[n]^\ast L} \]

を得られる。

これが非退化性の中心定理じゃ。

ただし一つ注意がある。

NOTE-016 の `multiplication_fiber_natDegree` は \(x\) 座標について次数 \(n^2\) の多項式を与えるが、それだけでは関数体全体の拡大次数が \(n^2\) 以下とは直ちに言えない。

\(y\) 座標も管理しなければならない。単純に二次拡大の評価を重ねると \(2n^2\) までしか得られない可能性がある。

模範解答の [finrank_fieldRange_mulPull_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean?utm_source=chatgpt.com) は、この余分な2を排除するために除法多項式と楕円曲線の反転作用を使っている。

NOTE-028 で最初に攻略すべき難所は、まさにここじゃろう。

### 3. 固定体が一致すれば、非退化性へ戻れる

仮に

\[ \forall S\in E[n],\quad e_n(S,T)=1 \]

とする。

NOTE-025 の固有方程式から、

\[ \tau_S^\ast w_{n,T}=w_{n,T} \]

である。

従って \(w_{n,T}\in L^H\)。固定体の同定によって、

\[ w_{n,T}=[n]^\ast h \]

となる有理関数 \(h\) が存在する。

ここで NOTE-023・024 の位数公式を用いる。

\[ \operatorname{ord}_P(w_{n,T}) = \mathbf1_{[n]P=T} - \mathbf1_{[n]P=O}. \]

この零点・極の情報を倍写像に沿って降下できれば、\(h\) の因子は

\[ \operatorname{div}(h)=[T]-[O] \]

となる。

よって \([T]-[O]\) は主因子。

楕円曲線の点群と類群の対応から、

\[ \boxed{T=O} \]

を得る。

これで非退化性が成立する。

なお、この最後の降下には倍写像の引き戻しと局所付値の整合性が必要じゃ。固定体が一致しただけで、付値の降下まで自動的に証明されたとは扱わぬことが大切じゃな。

## 実装上の推奨

NOTE-028 は大きいため、三つの証明境界に分けるのがよい。

| 境界  | 最終目標                                 |
| ----- | ---------------------------------------- |
| 028-A | 倍写像の関数体引き戻しと次数上界 \(n^2\) |
| 028-B | 固定体の同定 \(L^{E[n]}=[n]^\ast L\)     |
| 028-C | 付値降下から双指標の非退化性             |

028-A では NOTE-016、028-B では NOTE-019・021、028-C では NOTE-022〜026 を使う。

これまでの Core が、ここで一斉に合流する構造じゃ。

### 非退化性が完成したら

NOTE-018 の [`RootPairing`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/RootPairingDeterminant.lean?utm_source=chatgpt.com) が要求するものは、既にほとんどそろっている。

| `RootPairing` の要求 | 現状                     |
| -------------------- | ------------------------ |
| 左右の加法性         | NOTE-025・026 で証明済み |
| 交代性               | NOTE-026 で証明済み      |
| ガロア同変性         | NOTE-027 で証明済み      |
| 非退化性             | NOTE-028 で証明予定      |

非退化性まで完成したら、既存の `WeilPairingData` へ型を接続し、

\[ \boxed{\det\rho_{E,p}=\chi_p} \]

を無条件化できる見込みじゃ。

もちろん、その後も Frey 表現の既約性は別問題として残る。

## 賢狼の評価

わっちが今回とりわけ注目したのは、生成元の任意性を、構造の不変性で消し続けていることじゃ。

NOTE-022 では生成元を非標準的に選んだ。

NOTE-025 では、定数倍しても移動固有値が変わらないと証明した。

NOTE-027 では、ガロア作用で生成元が別の定数倍になっても、その固有値が正しく輸送されると証明した。

\[ \boxed{ \text{関数の表示は変わる} \quad\text{が}\quad \text{双指標の法則は保存される} } \]

そして次は、その双指標が零でない点を必ず識別できるか、という問題になる。

NOTE-027 は固定。NOTE-028 は倍写像の関数体次数から始めよう。

ここまで来たら、幾何学側の最後の大きな門じゃな。🐺🍎
