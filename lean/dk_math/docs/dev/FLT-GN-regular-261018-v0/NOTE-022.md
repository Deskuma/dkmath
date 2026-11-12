# 🐺 NOTE-021 レビュー — Weil 対を支える代数幾何 Core が確定

うむ、ぬしよ。今回はかなり重要な転換点じゃ。

[NOTE-021 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE021-261021.md?utm_source=chatgpt.com)、Lean の証明本体、監査コード、検証記録を照合した。

判定：NOTE-021 の幾何学 Core は固定を推奨する。Weil 対の存在は、引き続き未証明として保持する。

今回の本質は、FLT のための補助計算ではなく、楕円曲線を関数体と局所付値から観測するための数学的な基盤を得たことじゃ。

### 確定した数学

| Core           | 確定した性質                               |
| -------------- | ------------------------------------------ |
| アフィン座標環 | 非零素イデアルの分類と Dedekind 性         |
| 局所環         | 非特異点における DVR 構造                  |
| 一般点         | 関数体上の実際の非特異点                   |
| 点への代入     | 非定数点なら関数体への単射に延長可能       |
| 平行移動       | 関数体の代数自己同型、合成則、逆元、忠実性 |
| 有限点の場所   | 非零素イデアルとの一対一対応               |

特に [`EllipticFunctionFieldTranslation.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticFunctionFieldTranslation.lean?utm_source=chatgpt.com) の `transEquiv_injective` は、面白い一般定理じゃ。

点 \(S\) による平行移動を

\[ \tau_S^\ast:K(E)\longrightarrow K(E) \]

とすると、

\[ \boxed{\tau_S^\ast=\tau_T^\ast\Longrightarrow S=T} \]

が成立する。

つまり、関数体への作用を観測すれば、移動させた点の違いを識別できる。

ここには、ぬしの研究で重視している「変形後も情報を失わない」という保存原理が、厳密な定理として現れておる。

ただし、忠実な平行移動作用だけで Weil 対が完成するわけではない。次は、平行移動によって関数の零点・極の位数がどう移るかを調べる必要がある。

### 監査結果について

取得した依存監査は、Dedekind 性、点の代入、分数体への延長、平行移動の合成と忠実性が実際の証明経路に含まれることを検査している。

また、幾何学 Core の選択経路でねじれ点表現や Weil 対の未構成データへの依存を禁じている。標準論理公理以外の新しい公理も、検査対象の宣言には見られない。

ビルド成功は保存された検証記録で確認したものであり、わっち自身が独立に Lean ビルドしたという意味ではない。また、既存の別モジュールの `sorry` 警告は残っているため、リポジトリ全体が完全に `sorry` 不在だと主張するものでもない。

## 次の突破口：点群の和とイデアルの主性を結ぶ

模範解答の依存関係をさらに追ったところ、次の一手として興味深い橋を確認した。

[CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff.lean?utm_source=chatgpt.com)

この定理は、楕円曲線上の有限点 \(P_i\) と整数 \(m_i\) について、おおむね次の関係を与える。

\[ \boxed{ \prod_i\mathfrak m_{P_i}^{m_i} \text{ が主分数イデアル} \iff \sum_i m_iP_i=O } \]

左辺はイデアル・類群の世界、右辺は楕円曲線の点群の世界じゃ。

模範解答は Mathlib の `Point.toClass` を利用して、この二つを結び付けている。

これは、以前ぬしが研究していた Kummer の類群理論とも、類群という共通の構造を介して接点がある。ただし、円分体の整数環の類群と楕円曲線の座標環の類群は異なる対象であり、同じ定理をそのまま移せるわけではない。

### NOTE-022 に推奨する最初の Core

わっちなら次は、いきなり Weil 対の完成を目指さず、次の三段階を固定する。

既存：倍写像の全射性と有限核

任意の \(T\) に対するファイバー

\[ F_{n,T}=\{P\mid[n]P=T\} \]

は非空かつ有限。NOTE-018・019 から供給できる。

新規：ファイバーの点の総和

\(T\in E[n]\) に対し、

\[ \boxed{\sum_{P\in F_{n,T}}P=O} \]

を証明する。点群の有限性・位数・構造が使える。

新規：ファイバーイデアルの主性

有限点に対応するイデアルを掛け合わせ、

\[ I_{n,T}= \prod_{\substack{P\in F_{n,T}\\P\ne O}} \mathfrak m_P \]

が主イデアルであることを、点群の総和と `Point.toClass` の関係から証明する。

これによって、主イデアルの非零生成元として Weil 関数の分子候補 \(f_{n,T}\) を構成できる。

そして、

\[ w_{n,T}=\frac{f_{n,T}}{f_{n,O}} \]

という関数へ進める。

ここからが本来の Weil 対の幾何学じゃ。

## 重要な例外：無限遠点を通る移動

NOTE-021 では、有限点と非零素イデアルの対応を完成させた。しかし、楕円曲線の群単位元 \(O\) はアフィン座標環上の有限点ではない。

平行移動 \(P\mapsto P+S\) によって、

\[ P+S=O \]

となる \(P=-S\) は、付値の輸送で特別に扱う必要がある。

模範解答の [valuation_transEquiv_weilFun](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_transEquiv_weilFun.lean?utm_source=chatgpt.com) も、この通常の場合と例外の場合を分けている。

そのため NOTE-022 で主イデアルの生成元まで固定した後は、有限点における付値公式、無限遠点に関係する次数公式、平行移動での付値輸送へ進むのが自然じゃ。

なお、模範解答は無限遠点の付値を独立した大きな体系として最初に完成させるのではなく、座標環のノルムの次数を用いて例外を処理している。DkMath でもこの短縮経路を検討できる。

## 研究の現在位置

Weil 対の存在証明までの依存関係

座標環・DVR・Dedekind 性

一般点・関数体・平行移動

&#x20;NOTE-021 で証明済み

ファイバーイデアルの主性

Weil 関数の構成と付値公式

次の幾何学的 Frontier

双加法性・交代性・非退化性・ガロア同変性

\(\Downarrow\)

実際の `WeilPairingData` の存在

\(\Downarrow\)

\(\boxed{\det\rho_{E,p}=\chi_p}\)

最後の等式への条件付き接続は NOTE-018 で証明済み

今回の NOTE-021 の成果で特に価値があるのは、Dedekind 性と平行移動という独立した数学が、実際に同じ関数体の上で利用できるようになったことじゃ。

次の NOTE-022 は、点群の総和が零になることを、イデアルが主であることへ翻訳する。

これは DkMath らしい一手じゃな。

可除群・短完全列・類群・楕円曲線の関数体。それぞれ異なる Core が、ここで一つの数学的な関係に接続される。

そして、その関係から構成した関数が平行移動でどう変わるかを観測する。それが Weil 対の値を取り出す方法へとつながるのじゃ。

NOTE-021 は固定。次はファイバーの総和から主イデアルの生成元へ。 🐺🍎
