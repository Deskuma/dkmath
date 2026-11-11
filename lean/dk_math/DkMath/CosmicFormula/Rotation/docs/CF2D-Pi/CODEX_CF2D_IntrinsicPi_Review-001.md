# DkMath CF2D — Intrinsic π 実装レビュー 🐺

対象ブランチ： [`dev/CF2D-pi-261112-v0`](https://github.com/Deskuma/dkmath/tree/dev/CF2D-pi-261112-v0?utm_source=chatgpt.com)

ぬしよ！！ 実コードを確認したぞ。

これは数学的にも Lean の設計としても、非常によくできた実装じゃ！ 🍎

特に、Codex は単に `Real.pi` を別名で定義するような実装をしておらぬ。

実際に、次の順序で構成している。

\[ \boxed{ \begin{gathered} \text{CF2D 単位回転核}\\ \downarrow\\ \text{平方根による回転の二分割}\\ \downarrow\\ \text{面積近似列の構成}\\ \downarrow\\ \text{単調性・有界性の証明}\\ \downarrow\\ \text{上限による内在的定数の定義}\\ \downarrow\\ \text{標準の }\pi\text{ との同一性証明} \end{gathered} } \]

## 1. 総合評価

| 審査項目           | 評価       | 所見                                        |
| ------------------ | ---------- | ------------------------------------------- |
| 数学的構成         | 優秀       | 半角反復からπへ収束する正しい数列           |
| π-free な定義      | 合格       | `intrinsicPi` は `Real.pi` を参照せずに定義 |
| 代数的不変量       | 合格       | `UnitKernel` の保存量を再利用               |
| 反復の正当性       | 合格       | `half_star` で核の平方関係を証明            |
| 単調性・有界性     | 合格       | πを使用せず証明                             |
| πとの同一性        | 合格       | 独立した bridge で証明                      |
| 幾何学的対応       | 未完成     | 多角形としての解釈は未証明                  |
| 極限の幾何学的意味 | 部分的     | 解析的な一致は証明済み                      |
| 実ビルド           | 報告上成功 | わっちの環境では Lean を再実行していない    |

判定：数学的な中心部分は採用可能。正式統合前に、依存関係とブランチ構成を整備したい。

特に `intrinsicPi_eq_real_pi` の証明は、コード上では循環論法になっていない。

ただし「πを一切使わずにπの同一性まで証明した」という意味ではない。正確には、π-free な定数を構成したうえで、bridge では既知の三角関数の定理を利用して、その値がπであると証明している。

これは正当な数学的構成じゃ。

## 2. 重要定理のレビュー

### `HalfKernel.lean` — 回転の二分割

[ソース](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/HalfKernel.lean?utm_source=chatgpt.com)

```
theorem half_star (u : QuadrantUnitKernel) :
    Vec.star (half u).kernel.val
             (half u).kernel.val = u.kernel.val
```

ここは正しい。

\[ u=(c,s),\qquad c^2+s^2=1 \]

に対して、

\[ h(u)= \left( \sqrt{\frac{1+c}{2}}, \sqrt{\frac{1-c}{2}} \right) \]

を構成している。

そして、

\[ \boxed{h(u)\star h(u)=u} \]

を証明する。

この証明で重要なのは、第二成分の符号じゃ。

\[ 2\sqrt{\frac{1+c}{2}} \sqrt{\frac{1-c}{2}}=s \]

は、\(s\ge0\) という条件なしには一般に成立しない。

Codex はこれを `beam_nonneg` で保証している。

したがって、平方根の符号に由来する誤りは見当たらぬ。

### `IntrinsicPolygon.lean` — ここが今回の核心

[ソース](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPolygon.lean)

実際に定義されているのは、

\[ A_n=2^{n+1}s_n \]

\[ P_n=2^{n+1}\sqrt{2-2c_n} \]

じゃ。

そして、

```
halfPerimeterApprox_eq_areaApprox_succ
```

によって、

\[ \boxed{P_n=A_{n+1}} \]

を証明している。

これは偶然の数値的一致ではない。

単位円に内接する正 \(4\cdot2^n\) 角形を考えると、\(A_n\) はその面積、\(P_n\) は半周長に相当する。

つまり、ある正多角形の半周長と、辺数を二倍にした正多角形の面積が厳密に一致する という関係じゃ。

これは今回の研究で、特に価値の高い恒等式だと思う。

幾何学的な対応はまだ形式化されていないが、代数的な証明は完成している。

さらに、

```
areaApprox_eq_core_mul_succ
areaApprox_monotone
outerApprox_antitone
areaApprox_le_four
```

まで証明されている。

\[ A_n=c_{n+1}A_{n+1} \]

かつ、

\[ 0\le c_{n+1}\le1 \]

なので、

\[ A_n\le A_{n+1} \]

が成立する。

この流れも正しい。

### `IntrinsicPi.lean` — π-free な定数の定義

[ソース](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPi.lean)

```
noncomputable def intrinsicPi : ℝ :=
  sSup (Set.range areaApprox)
```

これは、数学的に正当な定義じゃ。

さらに、

\[ 2\le A_n\le4 \]

と単調増加が保証されているため、

\[ \boxed{ \Pi_{\mathrm{CF2D}} =\sup_{n\in\mathbb N}A_n =\lim_{n\to\infty}A_n } \]

が成立する。

この時点では、円周率の存在も、円という幾何学的対象も必要ない。

ここが大きな成果じゃ。

### `IntrinsicPiBridge.lean` — πへの接続

[ソース](https://github.com/Deskuma/dkmath/blob/dev/CF2D-pi-261112-v0/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/IntrinsicPiBridge.lean)

このファイルでは、

\[ \theta_n=\frac{\pi}{2^{n+1}} \]

を導入し、

\[ (c_n,s_n)=(\cos\theta_n,\sin\theta_n) \]

を証明する。

それによって、

\[ A_n=2^{n+1}\sin\theta_n \]

となる。

さらに、

\[ A_n=\pi\,\operatorname{sinc}(\theta_n) \]

へ変形している。

\[ \lim_{n\to\infty}\theta_n=0 \]

および、

\[ \lim_{x\to0}\operatorname{sinc}(x)=1 \]

から、

\[ \lim_{n\to\infty}A_n=\pi \]

が従う。

一方、`IntrinsicPi.lean` で同じ数列が `intrinsicPi` に収束すると証明されている。

したがって、極限の一意性より、

\[ \boxed{ \Pi_{\mathrm{CF2D}}=\pi } \]

となる。

この証明経路に数学的な問題は見当たらぬ。

## 3. レビューで見つかった改善点

数学的な致命的問題は見つからなかった。ただし、次の4点は改善を勧めたい。

### 1. 最優先：幾何学的対応の形式化

現在の `IntrinsicPolygon.lean` では、`areaApprox` は代数的な式として定義されている。

そのため、名前は面積近似でも、Lean が直接証明しているのは実数列の性質じゃ。

次に証明したいのは、

\[ \boxed{ A_n= \operatorname{Area} \left( \text{単位円内接正}(4\cdot2^n)\text{角形} \right) } \]

という命題じゃ。

`RegularOrbit` と接続すれば、CF2D の回転軌道が実際の正多角形を構成していることを明示できる。

これが完成すると、代数列と幾何学的面積の対応が Lean 内で保証される。

### 2. π-free 層をさらに強化できる

ここは、わっちから新しい提案がある。

現在、Codex は、

\[ A_n\uparrow\Pi_{\mathrm{CF2D}} \]

と、外接候補 \(U_n\) の単調減少を証明している。

そこで追加したいのが、

\[ \boxed{ \lim_{n\to\infty}(U_n-A_n)=0 } \]

という定理じゃ。

これは三角関数を使わずに証明できる。

実際、半回転核の第一成分について、

\[ c_{n+1}=\sqrt{\frac{1+c_n}{2}} \]

である。

\(0\le c_n\le1\) だから、

\[ 1-c_{n+1}\le\frac{1-c_n}{2} \]

が成立する。

初期値 \(c_0=0\) より、

\[ \boxed{ 0\le1-c_n\le\frac1{2^n} } \]

を導ける。

したがって、

\[ c_n\longrightarrow1 \]

となる。

外接候補は、

\[ U_n=\frac{A_{n+1}}{c_{n+1}} \]

じゃから、\(A_{n+1}\) が有界であることを使えば、

\[ U_n-A_{n+1}\longrightarrow0 \]

さらに \(A_n\to\Pi_{\mathrm{CF2D}}\) なので、

\[ \boxed{ A_n\le\Pi_{\mathrm{CF2D}}\le U_n } \]

という上下評価を、π-free 層だけで完結させられる。

これは追加する価値が高い。

πを知らなくても、自分自身が構成した定数へ、内側と外側の両方向から近づくことを証明できるからじゃ。

## 4. 今回、特に評価したい数学的成果

わっちは、`intrinsicPi_eq_real_pi` そのもの以上に、こちらを高く評価している。

\[ \boxed{ A_n=c_{n+1}A_{n+1} } \]

そして、

\[ \boxed{ P_n=A_{n+1} } \]

この二つが、πを使用しない代数から証明できていることじゃ。

なぜなら、これらは正方形の角度二分割を繰り返したとき、面積と周長がどのように結び付くかを表しているからじゃ。

ぬしが最初に述べた、

「半分の構造を解析し、対称性によって全体を復元する」

という考え方が、実際に数学的な関係式として現れておる。

しかも最終的な定数は、

\[ \Pi_{\mathrm{CF2D}} =\sup_{n\in\mathbb N}A_n \]

という形で、円周率とは無関係に定義できた。

これは πの値を証明することと、πという定数を構成することの分離に成功している という意味で、大きな前進じゃ。

## 5. 次段階の推奨

わっちなら、次は新しいπの計算式を探すのではなく、現在の成果を数学的に強化する。

| 優先度 | 次の作業                        | 目的                           |
| ------ | ------------------------------- | ------------------------------ |
| 高     | `c_n → 1` の π-free 証明        | 二分割反復の収束性             |
| 高     | `U_n - A_n → 0`                 | 内外近似による独立した収束証明 |
| 高     | `RegularOrbit` と正多角形の接続 | 面積・周長の幾何学的意味を確定 |
| 中     | 有限軌道の細分化と稠密性        | 離散的対称性から連続的な円へ   |
| 中     | π-free な誤差上界               | 計算精度の保証                 |
| 中     | CF2D 専用テスト群と文書整備     | 長期保守と公開への準備         |

## 6. 最終判定

今回の実装は、CF2D の π 構成における第一段階の完成として認めてよいと思う。

数学的に確認できたことは明瞭じゃ。

\[ \boxed{ \begin{aligned} &Q(u_n)=1\\ &u_{n+1}\star u_{n+1}=u_n\\ &A_n\le A_{n+1}\le4\\ &\lim_{n\to\infty}A_n=\Pi_{\mathrm{CF2D}}\\ &\Pi_{\mathrm{CF2D}}=\pi \end{aligned} } \]

最後の同一性だけを独立した bridge に置いていることも、正しい設計判断じゃ。

ただし、今回の証明は既知の正多角形近似を CF2D の言葉で形式化したものであり、πが純粋な代数的対称性だけから決定されると証明したものではない。

ここは、ぬしの研究をさらに進めるうえで重要な境界になる。

ぬしよ。

わっちは、これまでの研究の流れを思い返しておる。

古代エジプトの直径9の円から始まり、正方形の格子、八角形、45°の交点、白銀比、ガウス整数、そして宇宙式の回転不変量へと話が進んだ。

そして今、その考察の一部が Lean の定理として成立した。

CF2D の代数的な回転核から、πを参照せずに定数を構成し、その値が既知のπと一致すると証明できた。

これは確かな成果じゃ。

次は、幾何学的な円や多角形を用いずに構成した定数が、どのようにして実際の円の面積・周長へ対応するのかを、形式的に証明する段階じゃな。

ふふっ……正方形の対称性から始めた数学の旅が、随分と遠くまで来たものじゃ。🐺🍎
