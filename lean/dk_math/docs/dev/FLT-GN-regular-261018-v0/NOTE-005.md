# もう一つの戦略武器「判別式」DkMath 的に翻訳する

おお、ぬしよ。調べてみると、模範解答はわれらの想定とはかなり異なる方法で非正則素数を扱っておる。🐺🍎

結論から言うと、非正則素数の類群障害を GN–Kummer の内部で消去しているのではない。証明する対象を、円分整数環から楕円曲線とガロア表現へ移しているのじゃ。

今回参照したのは、一般 FLT の形式化である [Anthropic 版 PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md?utm_source=chatgpt.com) と、既存の [flt-regular](https://github.com/leanprover-community/flt-regular/tree/b8a5f23ab44a7be9fd49f6e3c831da54573c3c89?utm_source=chatgpt.com) じゃ。

## まず、模範解答の分岐点

| 対象                      | 模範解答が使用する証明                 |
| ------------------------- | -------------------------------------- |
| 3・5・7・11・13           | 小指数の降下法・正則素数 Kummer        |
| \(p\ge17\) のすべての素数 | Frey–Serre–Ribet–Wiles–Taylor–Wiles    |
| 37などの非正則素数        | 上記の \(p\ge17\) の一般経路に含まれる |

つまり非正則性を個別に分類して解決するのではなく、正則性を必要としない別の一般証明を採用するのじゃ。

その証明経路は、

\[ \boxed{ \begin{gathered} a^p+b^p=c^p\\ \Downarrow\\ \text{Frey 楕円曲線}\\ \Downarrow\\ \text{ガロア表現とモジュラー性}\\ \Downarrow\\ \text{Ribet のレベル降下}\\ \Downarrow\\ S_2(\Gamma_0(2))=0\\ \Downarrow\\ \bot \end{gathered} } \]

というもの。

ここで大切なのは、この経路には円分体の類群が自明であるという条件が要らないことじゃ。非正則素数を征するための模範解答の本質は、類群を強引に主イデアル化することではなく、別の不可能性へ反例を輸送することにある。

では DkMath では、それをどこまで GN の言語へ翻訳できるのか。ここが面白いところじゃ。

## DkMath 的に翻訳すると、最初の橋は「判別式」じゃ

ここで一つ、かなり直接的な接続が見える。

Frey 曲線は

\[ E:\quad Y^2=X(X-a^p)(X+b^p) \]

で定義される。

この右辺の三つの根は、

\[ 0,\qquad a^p,\qquad -b^p \]

じゃ。根同士の三つの差を見ると、

\[ a^p,\qquad b^p,\qquad a^p+b^p \]

が現れる。

つまり、FLT 方程式の三つの冪が、そのまま三つの根の間隔になっている。

三点の位置は概念図。重要なのは三つの根の差が \(a^p,b^p,c^p\) に対応すること。

この曲線の判別式は、上の簡単な三次式のモデルでは

\[ \boxed{ \Delta=16\bigl(a^p b^p(a^p+b^p)\bigr)^2 =16(abc)^{2p} } \]

となる。模範解答で用いる正規化された整係数 Weierstrass モデルでは、

\[ \boxed{ \Delta_{\mathrm{norm}}=2^{-8}(abc)^{2p} } \]

じゃ。

そして奇数 \(p\) における GN 恒等式、

\[ a^p+b^p=(a+b)GN_p(a+b,-b) \]

を代入すれば、

\[ \boxed{ \Delta_{\mathrm{norm}} = 2^{-8}(ab)^{2p} \bigl((a+b)GN_p(a+b,-b)\bigr)^2 } \]

となる。

これは GN と Frey 曲線を接続する厳密な代数恒等式として形式化できる。

さらに、正規化モデルの不変量 \(c_4\) も、

\[ \boxed{ c_4=a^{2p}+a^pb^p+b^{2p} =c^{2p}-(ab)^p } \]

となる。

ここが実に面白い。

- GN は、冪和 \(a^p+b^p\) の内部因子構造を観測する。
- Frey 曲線の判別式は、その冪和を含む三つの根の差の積を観測する。
- ガロア表現とレベル降下は、その判別式から得た素数ごとの局所情報を、別の大域的制約へ接続する。

ただし、判別式を GN で表示できることと、Ribet のレベル降下を GN から証明できることは別じゃ。この橋はまず代数的な入口であって、モジュラー性まで自動的に得られるわけではない。

## 模範解答では、可除性をどう使っているのか

重要な点は、こちらじゃ。

正規化された Frey 曲線に対して、奇素数 \(\ell\) なら、

\[ v_\ell(\Delta\_{\mathrm{norm}}) = 2p\,v_\ell(abc) \]

が成立する。

したがって、\(\ell\mid abc\) であれば判別式の付値は \(p\) の倍数になる。

一方、原始性と

\[ c_4=a^{2p}+a^pb^p+b^{2p} \]

を組み合わせると、奇素数 \(\ell\mid abc\) に対して \(\ell\nmid c_4\) が得られる。

この組み合わせが、Frey 曲線の局所的な還元の性質を制御する。

ここで模範解答は、局所的な可除性情報を mod-\(p\) ガロア表現

\[ \bar\rho_{E,p}: G_{\mathbb Q}\longrightarrow \operatorname{GL}_2(\mathbb F_p) \]

へ運び、Ribet のレベル降下を適用する。奇素数 \(\ell\ne p\) と \(\ell=p\) は別の補題で処理され、最終的にレベル2へ到達する。

結果は、

\[ \exists f\in S_2(\Gamma_0(2)),\quad f\ne0 \]

じゃ。

しかし、

\[ \boxed{S_2(\Gamma_0(2))=\{0\}} \]

なので矛盾する。

これはわれらが Kummer で行った「分岐深度を下げる降下」とは異なるが、可除性による状態の制限を、大域的な存在不可能性へ変換する点に共通した構造がある。

## ソースを読んで見つけた実装上の特徴

模範解答の実際の Lean では、次の四定理を最終矛盾で合成している。

| Lean 宣言                           | 担当                            |
| ----------------------------------- | ------------------------------- |
| `FreyPackage.Mazur_Frey`            | mod-\(p\) 表現の既約性          |
| `FreyPackage.frey_isModular`        | Frey 曲線のモジュラー性         |
| `FreyPackage.level_lowering_to_two` | 非零のレベル2尖点形式を構成     |
| `ModularForm.S2_Gamma0_2_eq_zero`   | その尖点形式が0になることを証明 |

これは [S_FreyPackage_no_frey_package.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_no_frey_package.lean?utm_source=chatgpt.com) で直接確認できる。

興味深い実装上の特徴もある。`level_lowering_to_two` はモジュラー性の証明を引数として受け取るが、内部で呼ぶ `modularRepOfConductorLevel` が必要なモジュラー性の情報を独自に再構成しているため、その引数は実際には使われていない。

この部分は将来 DkMath に輸送する際、定理の表向きの引数と、実際の証明依存を分けて整理すべき箇所じゃ。

## DkMath への翻訳案：まず五つの研究単位に分離する

ここから先は模範解答そのものではなく、わっちの提案じゃ。

| 研究単位                     | DkMath 側で固定する内容                  |
| ---------------------------- | ---------------------------------------- |
| `FreyGapCubic`               | 三根 \(0,a^p,-b^p\) と Gap の対応        |
| `GNFreyDiscriminant`         | GN による \(\Delta,c_4\) の厳密な表示    |
| `FreyPrimeValuation`         | 各素数での判別式付値・原始性・還元条件   |
| `FreyRepresentationContract` | mod-\(p\) 表現へ輸送するために必要な条件 |
| `ModularLevelObstruction`    | レベル降下から不存在へ至る証明契約       |

最初の三つは、既存の DkMath の `GN`・可除性・gcd ライブラリとの接続を中心に開発できる可能性が高い。

後ろ二つは大きな研究案件じゃ。ガロア表現・モジュラー性・レベル降下を伴うので、単なる多項式の恒等変形で代用することはできない。

そして、非正則素数を GN だけで征する独自の道も同時に残しておく。

それは前回提案した、

\[ (Q_i)=\mathfrak a_i^p \quad\Longrightarrow\quad [\mathfrak a_i]\in\operatorname{Cl}(R)[p] \]

の障害を追跡する経路じゃ。

こちらは模範解答の Wiles 型証明から直接得られるものではなく、DkMath 独自の研究課題として区別すべきじゃな。

## 最初に形式化するなら、この保存則

わっちが最も推したいのは、

\[ \boxed{ \begin{aligned} \Delta_{\mathrm{norm}} &=2^{-8}(abc)^{2p}\\ &=2^{-8}(ab)^{2p} \bigl((a+b)GN_p(a+b,-b)\bigr)^2 \end{aligned} } \]

を、正規化の条件も含めて Lean で固定することじゃ。

この一つの等式によって、DkMath の GN と模範解答の Frey 曲線の間に、曖昧な比喩ではない数学的な橋が架かる。

次に、

\[ \ell\mid abc \Longrightarrow p\mid v_\ell(\Delta\_{\mathrm{norm}}) \qquad(\ell\text{ は奇素数}) \]

を構成する。

この段階まで到達すれば、少なくとも FLT の原始反例が持つ可除性構造を、楕円曲線の判別式へ正確に輸送した ことになる。

ぬしよ、今回の模範解答から得られた一番大きなヒントはこれじゃ。

Kummer は、因子の素性と類群を調べて反例を排除した。Wiles 型証明は、同じ反例の冪構造を楕円曲線の判別式に移し、素数ごとの局所情報をガロア表現へ運び、レベル2の不存在に到達した。

片方は類群の障害、もう片方はモジュラー形式の不存在。

両者は同じ理論ではない。しかし、出発点には同じ整数の冪と可除性がある。

わっちには、この GN → 三根の Gap → Frey 判別式 → 局所付値 が、次に DkMath が調べるべき橋に見える。

そして今回の翻訳で得た最大の収穫は、模範解答が「非正則性をどう除去したか」ではなく、非正則性を要求しない観測空間へ移ったと分かったことじゃ。

くふふっ。🐺🍎

宇宙式の Core が別の Big の材料になる、あの入れ子の話を覚えておるか。今度は冪和が三根の間隔となり、判別式という別の保存量へ移る。ここには、研究してみるだけの確かな代数的接点があるぞ。
