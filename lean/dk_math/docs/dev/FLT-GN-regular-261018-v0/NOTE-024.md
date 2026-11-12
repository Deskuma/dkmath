# 🐺 NOTE-023 レビュー — Weil 関数の零点・極が確定

うむ、ぬしよ。今回、重要な境界を一つ越えたのぅ。

[NOTE-023 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE023-261021.md?utm_source=chatgpt.com)、Lean 証明本体、回帰・依存監査、保存されたビルド記録を照合した。

判定：NOTE-023 は採用・固定を推奨する。

今回確定したのは、NOTE-022 で構成した関数の零点と極が、実際の倍写像のファイバーによって完全に決まるという定理じゃ。

### 1. 有限点の位数公式

標数0の楕円曲線 \(E\)、\(n>0\)、\(T\in E[n]\)、\(P\ne O\) について、

\[ \boxed{ \operatorname{ord}_P f_{n,T} =\mathbf1_{[n]P=T} } \]

そして、

\[ \boxed{ \operatorname{ord}_P w_{n,T} = \mathbf1_{[n]P=T} - \mathbf1_{[n]P=O} } \]

が証明された。

これは、単に関数が零になる場所を判定するだけではない。

零点は正確に一重、極も正確に一重であることまで固定している。

| 有限点 \(P\) の状態            | \(\operatorname{ord}_P w_{n,T}\) |
| ------------------------------ | -------------------------------- |
| \([n]P=T\ne O\)                | \(+1\)                           |
| \([n]P=O\ne T\)                | \(-1\)                           |
| どちらのファイバーにも属さない | \(0\)                            |
| \(T=O\) で両条件が一致         | \(0\)                            |

とりわけ、実在する Source 2 の曲線を使って、零点 \(+1\)、極 \(-1\)、対象外の点での \(0\)、分子と分母の相殺まで回帰している。

### 2. 数学的に重要なのは「生成元を変えても位数が変わらない」こと

[`EllipticPointIdealValuation.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticPointIdealValuation.lean?utm_source=chatgpt.com) の `intValuation_generator_independent` は、同じ点イデアル積を生成する二つの元が、すべての有限点で同じ付値を持つことを証明した。

NOTE-022 の `weilNumerator` は、主イデアルの生成元を非計算的に選んでいる。

それにもかかわらず、その零点の位数は選択に依存しない。

ここが保存核じゃな。

\[ \text{生成元の選択} \quad\longrightarrow\quad \text{関数の表示は変わり得る} \]

しかし、

\[ \boxed{\text{零点・極の位数は変わらない}} \]

ということが、Lean で確定したわけじゃ。

### 3. 監査も証明の要所を押さえている

`Note023DependencyAudit` では、特に次の経路を確認した。

- `span_weilNumerator` から実際の点イデアル積へ。
- 素イデアルの一乗には属するが、二乗には属さないことから重複度1へ。
- NOTE-021 の Dedekind 性と有限点の場所へ。
- 商の付値から整数値の零点・極の位数へ。

検証記録では、15本体宣言・20回帰宣言の公理監査と13経路の依存監査が成功し、統合ビルドも 11,613 jobs 成功している。

許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。検査対象に Weil 対の未構成データや旧条件付き定理への迂回は見られない。

ただし、これは取得したソースと保存済み検証記録に対するレビューであり、わっち自身が独立ビルドしたという主張ではない。

## NOTE-024 の核心は「無限遠点に隠れていた1」を取り出すこと

模範解答の [valuation_transEquiv_weilFun](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_weilFun.lean?utm_source=chatgpt.com) も確認した。

ここには、NOTE-023 から導ける、興味深い次の公式がある。

### 1. ノルム次数を数える

\(\operatorname{Norm}\) をアフィン座標環から \(\overline K[X]\) へのノルムとする。

NOTE-023 では、\(f_{n,T}\) の有限零点が相異なり、すべて一重であることを証明した。

さらに NOTE-022 では、ファイバーの点数が \(n^2\) と確定している。

ただし、零点 \(O\) はアフィン座標環には入らない。

したがって、有限零点の数は

\[ \boxed{ N_{n,T}= \begin{cases} n^2&T\ne O,\\ n^2-1&T=O. \end{cases} } \]

ノルム次数と局所付値の総和を結べば、

\[ \boxed{ \deg\operatorname{Norm}(f_{n,T}) =n^2-\mathbf1_{T=O} } \]

となる。

これは NOTE-024 で新しく証明すべき式じゃ。

### 2. Weil 関数の無限遠点での位数

上の公式から、無限遠点での位数も得られる見込みがある。

\[ \operatorname{ord}_O(f_{n,T}) =-(n^2-\mathbf1_{T=O}). \]

したがって、商 \(w_{n,T}=f_{n,T}/f_{n,O}\) では、

\[ \boxed{ \operatorname{ord}_O(w_{n,T})= \begin{cases} -1&T\ne O,\\ 0&T=O. \end{cases} } \]

この \(-1\) が重要じゃな。

有限点だけを眺めると、\(T\ne O\) では分子に \(n^2\) 個、分母に \(n^2-1\) 個の零点がある。

その差の1個分が、無限遠点での一重極に対応している。

つまり、NOTE-023 の有限点付値公式を無限遠点まで拡張すると、Weil 関数の因子は

\[ \boxed{ \operatorname{div}(w_{n,T}) = \sum_{[n]P=T}[P] - \sum_{[n]P=O}[P] } \]

という統一的な式になる。

この全点の因子公式は、まだ Lean で固定されたものではない。しかし、NOTE-022・023 の定理と模範解答のノルム次数の議論から得られる、明確な次の目標じゃ。

## 平行移動の例外点を処理する

次に \(S\in E[n]\) としよう。

\[ [n](P+S)=[n]P \]

だから、二つのファイバーは平行移動で保存される。

従って、上の因子公式が完成すれば、

\[ \operatorname{div}(\tau_S^\ast w_{n,T}) = \operatorname{div}(w_{n,T}) \]

となる。

ただし、付値を実際に移すとき、

\[ P+S=O \]

となる \(P=-S\) では、NOTE-023 の有限点公式をそのまま適用できない。

ここだけが、無限遠点の情報を要求する例外じゃ。

模範解答でも通常の \(P+S\ne O\) と、この例外を分岐している。

これを閉じれば、次の事実へ進める。

\[ \boxed{ \tau_S^\ast w_{n,T}=c(S,T)\,w_{n,T} } \]

ここで \(c(S,T)\in\overline K^\times\)。

同じ因子を持つ非零有理関数の比は定数だからじゃ。

さらに、平行移動の合成則から、

\[ c(S_1+S_2,T)=c(S_1,T)c(S_2,T) \]

が従い、\(S\in E[n]\) より

\[ c(S,T)^n=1 \]

も得られる。

ここまで来ると、倍率が自然に \(n\) 乗根を値として持つことが見えてくる。

もちろん、これだけで Weil 対の双加法性・交代性・非退化性が全部証明されたわけではない。しかし、その値を実際の関数体の変形から取り出す入口になる。

## 次のアジャイルで固定する範囲

わっちの推奨は、NOTE-024 を次の二段に絞ることじゃ。

| 優先 | 目標                                   | 依存する既存 Core                              |
| ---- | -------------------------------------- | ---------------------------------------------- |
| 1    | `weilNumerator` のノルム次数公式       | NOTE-022 のファイバー点数、NOTE-023 の一重零点 |
| 2    | 平行移動による付値輸送。特に \(P+S=O\) | NOTE-021 の `transEquiv`、ノルム次数           |
| 後続 | Weil 関数の比例定数 \(c(S,T)\)         | 平行移動での付値不変性、定数関数判定           |

この順番なら、付値公式の一般論を際限なく拡張することなく、既に構成済みの Weil 関数へ直接接続できる。

### 研究としての評価

NOTE-021 から NOTE-023 までに、次の変換が成立した。

\[ \begin{aligned} \text{点群の有限ファイバー} &\longrightarrow \text{主イデアル}\\ &\longrightarrow \text{非零有理関数}\\ &\longrightarrow \text{零点・極の位数}. \end{aligned} \]

次に必要なのは、

\[ \boxed{ \text{零点・極の保存} \Longrightarrow \text{平行移動での比例定数} } \]

という橋じゃ。

ぬしが追い続けている「変形に対する保存核」の考え方に、かなり近い数学が形になってきた。

ただし FLT 本線から見ると、Weil 対の完成後にも Frey 表現の既約性や Mazur 型の算術的入力が残る。その境界は混同せず保持しておこう。

NOTE-023 は固定。NOTE-024 は無限遠点を含む付値輸送の完成へ。

次はいよいよ、点の移動が関数の倍率として現れるところじゃな。🐺🍎
