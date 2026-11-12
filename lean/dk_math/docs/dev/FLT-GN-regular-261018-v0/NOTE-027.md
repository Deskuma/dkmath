# 🐺🍎 NOTE-026 レビュー — Weil 対の双加法性と交代性が完成

うむ、ぬしよ。ついに、片側の指標が実際の楕円曲線から構成された交代的双指標になったのじゃな。

[NOTE-026 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE026-261021.md?utm_source=chatgpt.com)、Lean 本体、回帰、依存監査、検証記録を照合した。

判定：NOTE-026 は無条件の幾何学 Core として固定を推奨する。

今回確定したのは、同じ Weil 関数の平行移動から得た値

\[ e_n(S,T):=c(S,T) \]

について、次の法則がすべて成立することじゃ。

\[ \boxed{ \begin{aligned} e_n(S+R,T)&=e_n(S,T)e_n(R,T),\\ e_n(S,T+R)&=e_n(S,T)e_n(S,R),\\ e_n(T,T)&=1,\\ e_n(S,T)&=e_n(T,S)^{-1}. \end{aligned} } \]

しかも値は \(\mu_n\) に属する。

### 証明本体で確認した核心

右加法性は、既存の三つの Weil 関数の比較で閉じている。

\[ h=w_{n,T}\,\tau_{-U}^{\ast }w_{n,R}, \qquad [n]U=T. \]

全点の位数を計算すると、中間ファイバーの寄与が相殺され、\(h\) と \(w_{n,T+R}\) の位数が一致する。

NOTE-025 の定数比判定と固有値の一意性から右加法性を得ており、別の形式的な対へ置き換えていない。

交代性では、実際の軌道積

\[ H=\prod_{i=0}^{n-1}\tau_{[i]U}^{\ast }w_{n,T} \]

を構成している。

各点の位数が周期的差分

\[ d(i-1)-d(i) \]

となり、一周期の総和が零になることを証明した。

従って \(H\) は非零定数。その平行移動による固定性から

\[ \tau_T^{\ast }w_{n,T}=w_{n,T} \]

を導き、

\[ \boxed{e_n(T,T)=1} \]

を得ている。

これは単なる \(e_n(T,T)^n=1\) ではない。交代性そのものの証明じゃ。

### 二重の `AddChar` へ到達

[`EllipticWeilBicharacter.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticWeilBicharacter.lean?utm_source=chatgpt.com) では、

```
AddChar (Torsion E n)
  (AddChar (Torsion E n)
    (rootsOfUnity n (AlgebraicClosure K)))
```

という実際の双指標を構成した。

そして `weilAlternatingBicharacter_apply` により、その値が NOTE-025 の比例定数と定義的に一致することも確認できた。

Source 2 の回帰では、相異なる非零2-torsion点 \((0,0)\) と \((4,-2)\) も実際に使用している。

ただし、これら二点の対の値が非自明であることまでは証明していない。この区別も実装報告と一致する。

### 検証状況

| 項目                      | 確認結果         |
| ------------------------- | ---------------- |
| 本体宣言                  | 28               |
| 回帰宣言                  | 22               |
| 依存監査                  | 14経路成功       |
| 統合ビルド                | 11,638 jobs 成功 |
| 新規証明の公理            | 標準論理公理のみ |
| ルート import・テスト入口 | 成功             |
| 非退化性・ガロア同変性    | 未証明           |

これは取得したソースと保存された検証記録に基づくレビューで、わっちが独立に Lean ビルドしたものではない。

## NOTE-027 はガロア同変性を先に閉じるのがよい

模範解答の [weilPairing0_galois](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_galois.lean?utm_source=chatgpt.com) を確認した。

わっちの推奨は、NOTE-027 でガロア同変性、NOTE-028 で非退化性という順序じゃ。

ガロア同変性は、NOTE-025・026 で得た比例定数の一意性を再利用できる。一方、非退化性には倍写像による関数体の拡大次数や固定体の理論が必要になる。

まず既存の Core で閉じられる部分を固定しよう。

### 第一の橋：ガロア作用を関数体へ持ち上げる

\(\sigma\in G_K\) に対し、係数体の作用を関数体へ拡張した写像 \(\Phi_\sigma\) を構成する。

ここで重要なのは、\(\Phi_\sigma\) は一般に \(\overline K\)-線形ではなく、\(\sigma\)-半線形だということじゃ。

\[ \Phi_\sigma(a f)=\sigma(a)\Phi_\sigma(f). \]

次に、平行移動との交換則を証明する。

\[ \boxed{ \Phi_\sigma(\tau_S^\ast f) = \tau_{\sigma S}^\ast (\Phi_\sigma f) } \]

これは NOTE-021 の一般点と平行移動の構成を再利用する箇所になる。

### 第二の橋：Weil 関数はガロア作用で定数倍だけ変わる

ここでは、一般に

\[ \Phi_\sigma(w_{n,T})=w_{n,\sigma T} \]

と断定してはいけない。

`weilNumerator` は非標準的に選んだ生成元だからじゃ。

正しい目標は、

\[ \boxed{ \Phi_\sigma(w_{n,T}) = a_{\sigma,T}w_{n,\sigma T}, \qquad a_{\sigma,T}\in\overline K^\times. } \]

NOTE-024 の全点位数公式と、NOTE-025 の `existsUnique_scalar_of_pointOrder_eq` を使えば、証明できる見込みがある。

ここで再び「生成元の選択の違いは非零定数倍に吸収される」という保存核が働く。

### 第三の橋：固有値のガロア同変性

既に証明済みの

\[ \tau_S^\ast w_{n,T}=c(S,T)w_{n,T} \]

に \(\Phi_\sigma\) を作用させる。

第一・第二の橋を使い、非零関数を消去すれば、

\[ \boxed{ c(\sigma S,\sigma T)=\sigma(c(S,T)) } \]

が得られる。

これが NOTE-027 の主目標じゃ。

ガロア作用を受けるのは、関数の表示だけではない。平行移動から取り出した比例定数そのものが、ガロア作用と整合することになる。

そして、既存の `weilAlternatingBicharacter` にこの同変性を追加できる。

## NOTE-028：非退化性は固定体と倍写像の問題

こちらは、もう少し深い。

目標は、

\[ \boxed{ \bigl(\forall S\in E[n],\ e_n(S,T)=1\bigr) \Longrightarrow T=O. } \]

NOTE-026 の反対称性により、これを証明すれば左右双方の非退化性が得られる。

仮定から、

\[ \tau_S^\ast w_{n,T}=w_{n,T} \qquad(\forall S\in E[n]) \]

となる。

したがって \(w_{n,T}\) は、torsion 平行移動群による固定体に属する。

\[ w_{n,T}\in K(E)^{E[n]}. \]

ここから必要になるのが、

\[ \boxed{ K(E)^{E[n]}=[n]^\ast K(E) } \]

という固定体の同定じゃ。

模範解答の [eq_zero_of_forall_transEquiv_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean?utm_source=chatgpt.com) では、忠実な平行移動作用と \(|E[n]|=n^2\) による固定体の拡大次数を、倍写像による関数体の拡大次数の上界と比較している。

ここには DkMath 独自の短縮余地がある。

NOTE-019 が \(|E[n]|=n^2\) を無条件化し、NOTE-021 が平行移動の忠実性を既に固定しているからじゃ。

必要なのは主に、倍写像の引き戻し

\[ [n]^\ast :K(E)\longrightarrow K(E) \]

の構成と、

\[ [K(E):[n]^\ast K(E)]\le n^2 \]

という次数評価への接続になる。

ただし、この評価には除法多項式の有理関数表示などが必要で、NOTE-019 の位数公式だけから直ちに従うわけではない。

この固定体の同定が済めば、非退化性の最後の障害を NOTE-022 の点群と類群の橋へ戻せる。

つまり、長い幾何学の旅の最後に、再び

\[ \text{主イデアル} \iff \text{点群の総和が零} \]

という Core が現れるわけじゃな。

## 最後の接続先は既に完成している

NOTE-027・028 の両方が完成すれば、NOTE-018 の

```
WeilPairingData E p
```

を、現在の実際の双指標から無条件に構成する道が開ける。

その後の円分行列式は、既に証明済みの

```
torsion_determinant_eq_cyclotomic_of_pairing
```

へ渡すだけじゃ。

\[ \boxed{ \text{実際の幾何学的 Weil 対} \Longrightarrow \det\rho_{E,p}=\chi_p } \]

ただし、この先も Frey 表現の既約性そのものは別の算術的問題として残る。

### 賢狼の総合判定

NOTE-026 までで、

\[ \text{座標環} \longrightarrow \text{関数体} \longrightarrow \text{付値} \longrightarrow \text{平行移動の固有値} \longrightarrow \boxed{\text{交代的双指標}} \]

という長い連鎖が、実際の Lean 証明で接続された。

次は、その双指標について二つの問いを閉じる。

ガロア作用を受けても同じ数学を表すか。そして、その値は異なるねじれ点を識別できるか。

前者が同変性、後者が非退化性じゃ。

NOTE-027 はガロア同変性。NOTE-028 は固定体から非退化性。

これを閉じれば、ぬしが目標としてきた円分行列式への橋が完成する。

いやはや、NOTE-021 から始まった関数体の幾何学が、とうとう Galois 表現論の入口まで来た。良い進展じゃな。🐺🍎
