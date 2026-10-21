# 🐺 NOTE-025 レビュー — Weil 対の「片側」が実際の指標になった

うむ、ぬしよ。今回も [NOTE-025 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE025-261021.md?utm_source=chatgpt.com)、Lean 証明本体、回帰・依存監査、保存された検証記録を照合した。

判定：NOTE-025 は無条件の Core として固定を推奨する。

今回は、NOTE-021 から積み上げてきた幾何学が、初めて具体的な群の指標を生み出した。

### 1. 実際の平行移動から一意な固有値を取り出した

標数0の楕円曲線 \(E\)、\(n>0\)、\(S,T\in E[n]\) について、

\[ \boxed{ \tau_S^\ast w_{n,T}=c(S,T)\,w_{n,T}, \qquad c(S,T)\in\overline K^\times } \]

を証明した。

しかも、この \(c(S,T)\) は一意じゃ。

[`EllipticFunctionFieldConstants.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticFunctionFieldConstants.lean?utm_source=chatgpt.com) では、全有限場所で付値1となる非零関数が定数であることを、Dedekind 整域とノルム次数から証明している。

それを一般的な固有値復元定理に整理し、NOTE-024 の位数保存と接続した。

つまり、比例性を新しい仮定として導入したのではない。既に証明した付値保存から、実際に比例定数を復元したのじゃ。

### 2. 比例定数が根の世界へ着地した

平行移動の合成と固有値の一意性から、

\[ \boxed{ \begin{aligned} c(O,T)&=1,\\ c(S+R,T)&=c(S,T)c(R,T),\\ c(S,T)^n&=1 \end{aligned} } \]

が成立する。

これによって、

\[ \boxed{ c(-,T):E[n]\longrightarrow\mu_n } \]

という `AddChar` が構成された。

[`EllipticWeilCharacter.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticWeilCharacter.lean?utm_source=chatgpt.com) の `weilTranslationCharacter` が、その実際の対象じゃ。

この段階では、まだ任意の双線形形式を仮定していない。

点群の加法が、関数体の自己同型を経由して、乗法群の指標になった。

これは数学として大きな変化じゃな。

### 3. 固有値は生成元の選び方から独立している

NOTE-022 の分子 \(f_{n,T}\) は、非標準的な生成元の選択だった。

NOTE-025 では、分子と分母をそれぞれ非零定数倍で選び直しても、比の固有値 \(c(S,T)\) は変化しないことを証明した。

\[ w_{n,T}\longmapsto \frac ab w_{n,T} \]

としても、

\[ \boxed{c(S,T)\text{ は不変}} \]

じゃ。

これで、生成元の選択に由来する任意性が、数学的な結論へ漏れないことが確定した。

### 監査結果

取得した検証記録は以下と一致している。

| 項目                      | 結果             |
| ------------------------- | ---------------- |
| 本体宣言                  | 28               |
| 回帰宣言                  | 16               |
| 依存監査                  | 13経路成功       |
| 統合ビルド                | 11,631 jobs 成功 |
| 新規宣言の公理            | 標準論理公理のみ |
| ルート import・テスト入口 | 成功             |

既存の別モジュールにある `sorry` 警告5件は残っている。今回の監査対象の証明経路とは区別されている。

なお、わっちが独立に Lean ビルドしたのではなく、取得したソースと検証記録に基づくレビューじゃ。

## 次の Frontier：右変数の加法性と交代性

模範解答の次の二つも確認した。

- [weilPairing0_add_right](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_add_right.lean?utm_source=chatgpt.com)
- [weilPairing0_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_self.lean?utm_source=chatgpt.com)

ここに、DkMath の既存 Core を利用した短縮経路が見える。

### 第一段階：右変数の加法性

目標は、

\[ \boxed{c(S,T+T')=c(S,T)c(S,T')}. \]

このために、新しい Weil 関数を構成する必要はない。

NOTE-018 の全射性から、

\[ [n]U=T \]

を満たす点 \(U\) を取る。

ここで、既存の Weil 関数三つを組み合わせ、

\[ h=w_{n,T}\cdot\tau_{-U}^\ast w_{n,T'} \]

と定める。

NOTE-024 の全点位数公式を使うと、

\[ \begin{aligned} \operatorname{ord}_P(h) &= \bigl(\mathbf1_{[n]P=T}-\mathbf1_{[n]P=O}\bigr)\\ &\quad+ \bigl(\mathbf1_{[n]P=T+T'}-\mathbf1_{[n]P=T}\bigr)\\ &=\mathbf1_{[n]P=T+T'}-\mathbf1_{[n]P=O}. \end{aligned} \]

したがって、

\[ \boxed{ \operatorname{ord}_P(h) =\operatorname{ord}_P(w_{n,T+T'}) } \]

がすべての点で成立する。

NOTE-025 の `existsUnique_scalar_of_pointOrder_eq` を適用すれば、

\[ w_{n,T+T'}=a\,h \qquad(a\in\overline K^\times) \]

が得られる。

そして \(S\in E[n]\) による平行移動を作用させる。

\[ \begin{aligned} \tau_S^\ast h &=(\tau_S^\ast w_{n,T})   (\tau_S^\ast \tau_{-U}^\ast w_{n,T'})\\ &=c(S,T)c(S,T')h. \end{aligned} \]

平行移動が可換であることと、NOTE-025 の固有値の一意性から、

\[ \boxed{c(S,T+T')=c(S,T)c(S,T')} \]

を得る。

ここでは NOTE-024 の全点位数公式と NOTE-025 の定数比判定が、そのまま再利用できる。

模範解答の右加法性の中心部分を、既存モジュールの定理呼び出しへ整理できる見込みが高い。

### 第二段階：交代性

次は、

\[ \boxed{c(T,T)=1} \]

じゃ。

これにも、模範解答に明確な構成がある。

まず \([n]U=T\) を満たす \(U\) を取る。

そして、

\[ H=\prod_{i=0}^{n-1}\tau_{[i]U}^\ast w_{n,T} \]

と定める。

この積の零点・極を NOTE-024 の全点位数公式で計算すると、隣接項が相殺する。

実際、

\[ \operatorname{ord}_P (\tau_{[i]U}^\ast w_{n,T}) = d_{i-1}(P)-d_i(P) \]

と書ける。ただし、

\[ d_i(P)=\mathbf1_{[n]P+[i]T=O}. \]

したがって総和は望遠鏡型に消え、

\[ \operatorname{ord}_P(H)=0 \]

となる。最後の端点も \([n]T=O\) によって一致する。

NOTE-025 の定数比判定から、\(H\) は非零定数じゃ。

ここで \(U\) によって平行移動すると、積の添字が一つずれる。

\[ \tau_U^\ast H = \prod_{i=1}^{n}\tau_{[i]U}^\ast w_{n,T}. \]

一方、\(H\) は定数だから \(\tau_U^\ast H=H\)。

共通する非零因子を消去すれば、

\[ \tau_{[n]U}^\ast w_{n,T}=w_{n,T}. \]

\([n]U=T\) より、

\[ \tau_T^\ast w_{n,T}=w_{n,T}. \]

よって比例定数の一意性から、

\[ \boxed{c(T,T)=1}. \]

これで交代性が得られる。

さらに両変数の加法性と組み合わせれば、

\[ \boxed{c(S,T)=c(T,S)^{-1}} \]

という反対称性も従う。

この構成も新しい幾何学を要求せず、NOTE-018、024、025 の既存 Core で閉じられる可能性がある。

## NOTE-026 の推奨目標

右加法性・交代性・反対称性を、一つのアジャイルで無条件化する。

ここを閉じれば、

\[ \boxed{ e_n:E[n]\times E[n]\longrightarrow\mu_n } \]

が実際の関数体から構成され、両変数に関して加法的、かつ交代的な対となる。

ただし、これだけではまだ完全な Weil 対ではない。

残る二つの重要な性質を区別しよう。

| 残る性質     | 必要な数学                                                        |
| ------------ | ----------------------------------------------------------------- |
| ガロア同変性 | 係数体のガロア作用を関数体へ持ち上げ、平行移動との可換性を示す    |
| 非退化性     | すべての torsion 移動で不変な関数が、倍写像から降下することを示す |

とりわけ非退化性が、次の大きな Frontier になる。

模範解答は [eq_zero_of_forall_transEquiv_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean?utm_source=chatgpt.com) において、有限ガロア群による不変体と倍写像の引き戻しを比較する。

その核心は、

\[ \boxed{ K(E)^{E[n]}=[n]^\ast K(E) } \]

という固定体の同定じゃ。

これを得ると、すべての \(S\in E[n]\) に対して \(c(S,T)=1\) なら、\(w_{n,T}\) は倍写像から引き戻された関数となる。

しかしその零点・極の構造を降下させると、単一の点差 \([T]-[O]\) が主因子になることを要求する。楕円曲線の点群と類群の対応により、それは \(T=O\) を意味する。

これが非退化性の本質的な障害排除じゃ。

ここは右加法性や交代性ほど短くならない可能性があるため、独立した段階として扱うのが適切じゃろう。

## 今回の発見を DkMath の言葉で整理すると

NOTE-021 から NOTE-025 まで、ずっと同じ対象を追っている。

最初は関数体に平行移動を作用させるだけだった。

次に、イデアルから関数を作った。

そして、関数の零点・極を測定し、平行移動でその情報が変わらないことを証明した。

そこから比例定数が現れた。

\[ \boxed{ \tau_S^\ast w_{n,T}=c(S,T)w_{n,T} } \]

ここで重要なのは、左辺の関数は変形しているのに、右辺ではその変形が一つの乗法定数へ集約されていることじゃ。

さらに今回、

\[ c(S+R,T)=c(S,T)c(R,T) \]

が証明されている。

まさに加法が乗法へ変換されている。

しかし、これは抽象的な交換式を仮定して得られたものではない。楕円曲線の関数体、Dedekind 性、付値、平行移動、非零関数の定数比という一連の証明から自然に現れた構造じゃ。

次に右加法性まで証明できれば、二つの点の加法構造が、そのまま \(\mu_n\) の乗法へ写る。

\[ \boxed{ \text{点群の二つの加法} \longrightarrow \text{一つの乗法的不変量} } \]

NOTE-025 は固定。NOTE-026 は右加法性と交代性へ。

その次に非退化性とガロア同変性を閉じれば、NOTE-018 の条件付きだった行列式公式が、いよいよ無条件の定理へ変わる。

長い橋じゃったが、対の値そのものは既に手の中にある。残るのは、その値がどれほど強く点群の構造を識別できるかを証明することじゃな。🐺🍎
