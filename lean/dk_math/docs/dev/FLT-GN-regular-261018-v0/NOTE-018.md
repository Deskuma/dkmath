# 🐺 NOTE-017 — GL₂ 表現の Core を固定

うむ、ぬしよ。指定ブランチの [NOTE-017 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE017-261021.md?utm_source=chatgpt.com)、Lean 本体、回帰、依存監査と検証記録を照合した。

判定：NOTE-017 は採用・固定を推奨する。

今回確定した数学は、単に GL₂ の行列を作れたことではない。

\[ \boxed{ \rho_{E,p}:G_K\longrightarrow \operatorname{GL}_2(\mathbb F_p) } \]

が、NOTE-016 で二次元性を証明した実際の \(E[p]\) から構成され、元のガロア作用と同じ情報を保持することじゃ。

### 固定できた保存核

実装の核心は、基底 \(b\) から \(c\) への変更が

\[ M_c(\sigma)=C M_b(\sigma)C^{-1} \]

となること。そして、次の不変性が証明されている。

| 対象       | NOTE-017 で確定した性質          |
| ---------- | -------------------------------- |
| ガロア作用 | 行列作用と実際の点への作用が一致 |
| 核         | \(\ker M=\ker\rho\)              |
| 行列式指標 | 基底変更で不変                   |
| 特性多項式 | 基底変更で不変                   |
| 既約性     | 元の表現と座標表示で同値         |
| 有限レベル | 元の開核・有限正規レベルを保持   |

特に `matrixGroupHom_ker` と `determinantCharacterWithBasis_independent` は、今後の数論で繰り返し使える一般表現論の Core になっておる。

そして、

\[ \boxed{ S.\mathrm{ResidualIsIrreducible} \iff \text{ガロア安定な一次元部分空間が存在しない} } \]

も、既存の `ResidualIsIrreducible` を変更せずに証明できている。

### 回帰例が確認している本質

実在する曲線の \(E[37]\) では、二つの異なる基底の間で共役関係と不変量を検査できている。

さらに \(E[2]\) では、非零の有理点 \((0,0)\) が生成するガロア安定直線を実際に構成した。

したがって、

\[ \dim_{\mathbb F_2}E[2]=2 \quad\text{なのに}\quad \rho_{E,2}\text{ は可約} \]

という反例も確定している。

これは重要じゃ。二次元性と既約性を混同する誤った推論を、抽象論だけでなく実際の楕円曲線で防いでいる。

検証記録では統合ビルド、標準論理公理に限定した公理監査、主要依存経路の監査が成功している。わっち自身が独立ビルドしたわけではないが、取得した証明本体と監査コードの構造は報告内容と整合している。

## 次のアジャイル：NOTE-018 は円分行列式の証明へ

模範解答の後続を確認したところ、次に必要なのは一般の GL₂ 表現論ではなく、楕円曲線固有の Weil 対じゃ。

参照先は次の二つ。

- [Weil 対の構成](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean?utm_source=chatgpt.com)
- [Weil 対から行列式を求める定理](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean?utm_source=chatgpt.com)

数学的な核心は美しい。

NOTE-017 で確定した基底を \(P,Q\) とし、ガロア元 \(\sigma\) の作用行列を

\[ M_\sigma= \begin{pmatrix} a&b\\c&d \end{pmatrix} \]

とする。

Weil 対 \(e_p\) が双加法性・交代性・ガロア同変性を満たせば、

\[ \begin{aligned} \sigma(e_p(P,Q)) &=e_p(\sigma P,\sigma Q)\\ &=e_p(P,Q)^{ad-bc}\\ &=e_p(P,Q)^{\det M_\sigma}. \end{aligned} \]

非退化性により、基底に対する \(e_p(P,Q)\) は原始 \(p\) 乗根となる。

ゆえに、

\[ \boxed{\det\rho_{E,p}=\chi_p} \]

が得られる。

ここで \(\chi_p\) は \(p\) 乗根へのガロア作用から定まる円分指標じゃ。

NOTE-017 で基底によらないことまで確定した行列式指標に、今度は具体的な算術的意味を与える。

これが NOTE-018 の中心目標になる。

### DkMath 流の実装順序

まず、一般表現論側で「二次元空間にガロア同変な非退化交代対があるなら、その行列式は対の値へのガロア作用で決まる」という定理を作る。

これは楕円曲線に依存せず、線形代数で閉じられる。

次に、実際の `Torsion E p` 上で Weil 対を構成し、その双加法性・交代性・非退化性・ガロア同変性を供給する。

最後に、NOTE-017 の `residualDeterminantCharacter` へ接続し、同じ Frey Source に対する円分指標との一致を証明する。

ただし、Weil 対の幾何学的構成は小さくない。模範解答も座標環の Dedekind 性、付値、関数の平行移動などに依存している。ここは既存の Mathlib と DkMath の Core を比較し、必要な依存だけを取り込むべきじゃろう。

線形代数側の条件付き定理だけを完成させた場合、それを円分行列式の無条件証明として扱わないことも重要じゃ。

### 既約性との接続

模範解答では、Frey 表現の可約性から、特別なガロア安定直線が存在することを導き、それを Mazur 型の算術によって排除している。

NOTE-017 は、その入口となる「安定直線」の判定器を確定した。

NOTE-018 で行列式が円分指標と一致すれば、安定直線があると仮定した際に、行列の対角成分に対応する二つの一次元指標の積が \(\chi_p\) になる。

\[ \rho(\sigma)\sim \begin{pmatrix} \alpha(\sigma)&\ast\\ 0&\beta(\sigma) \end{pmatrix}, \qquad \alpha\beta=\chi_p. \]

この制約が、可約性から矛盾を導く後続の算術に使われる。

ただし、\(\alpha\beta=\chi_p\) だけでは安定直線は排除できない。ここから先に Mazur の理論が必要になる。

## もう一つ見えている Core

NOTE-016 のコードには、将来一般化できそうな成果も残っておる。

既存の `multiplication_fiber_natDegree` と `exists_aligned_multiplication_preimage` を組み合わせれば、任意の \(n>0\)、任意の \(Q\in E(\overline K)\) に対して、

\[ \boxed{\exists P,\quad [n]P=Q} \]

すなわち 倍写像 \([n]\) の全射性を直接証明できる見込みがある。

なぜなら、任意の \(Q\) の \(x\) 座標 \(c\) に対して、\(\Phi_n-c\Psi_n^{\mathrm{Sq}}\) は正の次数 \(n^2\) を持ち、代数閉包上で根を取れるからじゃ。\(Q=O\) は \(P=O\) でよい。

これは模範解答にも現れる定理で、NOTE-016 の短縮経路からさらに短く取り出せる可能性がある。今回はまだ Lean での新たな接続を確認していないので、将来の Core 候補として扱う。

NOTE-017 は固定。次の主戦場は Weil 対と円分行列式。

そして、わっちは今回の成果を、ぬしの保存核の思想そのものとして評価しておる。

基底をどれほど入れ替えても、

\[ M\longmapsto CMC^{-1} \]

という変形を受けるだけで、

\[ \boxed{\det M,\quad\operatorname{charpoly}M,\quad\ker\rho} \]

は変わらない。

これはまさしく、表現が動いても失われない Core じゃ。

今度はその行列式に、円分体という別の数学世界から意味を与える番になる。

DkMath の幾何学と円分体が、いよいよ接続するところじゃな。🐺🍎
