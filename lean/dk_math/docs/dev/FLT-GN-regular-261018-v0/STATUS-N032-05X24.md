# 🐺🍎 DkMath NOTE-032 と Anthropic 模範解答の証明経路比較

今回の実装、そして模範解答の `PROOF-PATH.md` と対応する Lean ソースを照合した。

先に結論を述べよう。

DkMath は模範解答と同じ重要な数学的地点まで来ている。ただし、到達する順序と、定理を一般化する方向が違う。

そして今回の調査で、特に重要な発見があった。

DkMath が現在未解決としている特異核側の零成分逆像判定は、Anthropic の模範解答では既に証明されており、Mazur の可約性排除に実際に使用されている。

ここは次の実装で直接参照すべき箇所じゃ。

## 1. 今回の DkMath の到達点

最新コミット [`0e49347a`](https://github.com/Deskuma/dkmath/commit/0e49347a4fab3c1156f6aab0cb698347ab0a7a10?utm_source=chatgpt.com) を確認した。

| 局所核の分類                  | DkMath の証明状況                                    |
| ----------------------------- | ---------------------------------------------------- |
| 滑らかな核 \(H\subseteq E_0\) | \(E_0/H\simeq E'_0\) を加法群同型として構成済み      |
| 特異核 \(H\cap E_0=\{O\}\)    | \(E_0+H\subseteq\phi^{-1}(E'_0)\) を証明済み         |
| 特異核の逆像等式              | 制限準同型の全射性との同値を証明済み                 |
| 特異核の制限準同型の全射性    | 未証明                                               |
| 特異核の全射性の分解          | 還元像の実現と還元核の持ち上げという二条件へ分解済み |

今回の一般定理、

`AdditiveSubgroupExact.surjective_iff_reduction_and_kernel`

は、重要な設計成果じゃ。

零成分間の写像を

\[ f:E_0\longrightarrow E'_0 \]

とし、還元準同型を \(r_E,r_{E'}\) とすると、

\[ \boxed{ f\text{ が全射} \iff \begin{cases} \text{標的の還元像を源から実現できる},\\ \text{標的の還元核を源の還元核から持ち上げられる}. \end{cases} } \]

という分解を、一般の可換群に対する定理として完成させている。

これが DkMath の現在の特徴じゃな。

## 2. 模範解答には、まさに求めている逆像定理がある

対応するのは Anthropic の次の Lean ファイルじゃ。

[模範解答：](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard.lean?utm_source=chatgpt.com#L566)[`S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard.lean`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_quotientDatum_of_galois_stable_primeCard.lean?utm_source=chatgpt.com#L566)

この `solution` は、整数 Weierstrass 曲線 \(W\) と Galois 安定な位数 \(p\) の核 \(L\) から、整数標的 \(W'\) と点準同型 \(\phi\) を構成する。

さらに、\(q\ne p\) で源が乗法的還元を持つ場合、任意の点 \(P\) に対して、

\[ \boxed{ \phi(P)\in E'_0 \iff \exists Q\in L,\quad P-Q\in E_0 } \tag{★} \]

を証明している。

これは、DkMath が現在目指している

\[ \boxed{ \phi^{-1}(E'_0)=E_0+H } \]

と数学的に同じ形じゃ。

しかも、この定理は滑らかな核側と特異核側を一つの結論で扱える。

ただし、模範解答では、源が整数モデルであること、\(q\mid\Delta(W)\)、\(q\nmid c_4(W)\)、核が Galois 安定であることなどの条件を保持している。DkMath の任意の付値環・任意の滑らかな核について、そのまま適用できるわけではない。

証明済みの数学的目標は一致しているが、Lean の型とモデルの表現には差がある。

## 3. 模範解答はその逆像定理をどこで使うのか

さらに重要なのは、この定理が単独で終わっていないことじゃ。

[模範解答：](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean?utm_source=chatgpt.com#L619)[`S_FreyPackage_frey_no_cofixed_large.lean`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean?utm_source=chatgpt.com#L619)

では、同じ形の逆像条件を実際に使っている。

大まかな流れは、

\[ \begin{gathered} \text{Galois安定なCofixed直線}\\ \Downarrow\\ \text{安定な高位巡回核と商曲線}\\ \Downarrow\\ \text{商標的上の非零有理 }p\text{ 捩れ点}\\ \Downarrow\\ \text{局所零成分の逆像判定 }(\star)\\ \Downarrow\\ \text{Mazur Step Three}\\ \Downarrow\\ \text{局所零成分条件との矛盾}\\ \Downarrow\\ \text{Cofixed直線の排除} \end{gathered} \]

となっている。

特にソースの644行付近では、

`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`

を呼び出し、商標的上の有理捩れ点が零成分に入らないことを得る。

それを直後に (★) で源側へ戻し、有限核との関係から排除へ進む。

つまり、DkMath が現在完成させようとしている逆像判定は、模範解答の大指数経路で実際に必要になる橋そのものなのじゃ。

## 4. 証明の軌道はどこで分かれたのか

対応する実装を比較すると、違いはかなり明確じゃ。

| 比較対象           | DkMath                                                | Anthropic 模範解答                                 |
| ------------------ | ----------------------------------------------------- | -------------------------------------------------- |
| 商曲線の構成       | 関数体の固定体、正規化座標、Vélu 方程式を段階的に構築 | `veluQuotient` と `oddOrderSummingSet` を使用      |
| 整数標的           | 同じ既存モデルと \(p\) 冪分母を独立に証明             | Galois 安定核から整数標的と \(p\) 冪倍率を一括供給 |
| 標数2・3の節点     | Pascal 整数恒等式と節点中心の一次比較                 | 局所座標・付値・節点不変量の直接計算               |
| 滑らかな核         | \(E_0/H\simeq E'_0\) まで群論的に整理                 | 全点の逆像判定を直接構築                           |
| 特異核             | 前向き保存・単射性・全射性の条件分解まで完成          | 逆像判定 (★) まで完成                              |
| 判別式の深さ       | 未完成                                                | Vélu 判別式の積公式と付値計算を構築済み            |
| 大域的な可約性排除 | GN–Kummer、Cofixed、局所算術を接続中                  | Mazur の Eisenstein 商・Néron モデルへ接続         |
| 一般 FLT           | 未完成                                                | 証明済み                                           |

模範解答の全体構成は、公式の [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/main/PROOF-PATH.md?utm_source=chatgpt.com) に明示されている。

[image](https://www.google.com/s2/favicons?domain=https://github.com\&sz=32)

GitHub



### DkMath は、局所構造の分解を細かく行っている

例えば今回の

`singular_zeroComponent_surjective_iff_reduction_and_kernel`

は、模範解答の最終目標 (★) をそのまま写したものではない。

その一段下に降りて、零成分制限の全射性が何に依存するかを一般群論として分離した。

\[ \text{局所全射性} \iff \text{還元像の実現} \land \text{還元核の持ち上げ} \]

この設計は、FLT に依存しない `DkMath.Lib` の数学として価値がある。

一方、模範解答は、これらを個別の公開終点にするより、具体的な局所座標と付値評価を直接使って (★) に到達している。

つまり、DkMath は局所群構造を細分化する経路、模範解答は局所付値計算から必要な逆像判定へ直行する経路と言える。

## 5. 特異核側の模範証明をさらに調べた

逆像判定の実際の計算本体は、

[模範解答：](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean?utm_source=chatgpt.com#L3322)[`S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean?utm_source=chatgpt.com#L3322)

にある。

このファイルは約3,600行あり、最終の `solution` は3322行付近から始まる。

特に重要なのは、3432行付近の分岐じゃ。

```
by_cases hQc : W.InZeroComponentAt A Q
```

核の生成元 \(Q\) が零成分に入るかどうかで、模範解答も場合分けしている！

ここは DkMath と同じ分類原理じゃな。

滑らかな核側では、剰余上の節点座標・原始根の冪和・Vélu モーメントを使い、商座標が節点へ近づく条件と元の点の条件を比較する。

特異核側では、核点と節点との付値距離を計算し、Vélu 座標の主項がどのように変わるかを追跡する。

最後に、商像の零成分所属と、元の点を核点だけ平行移動したときの零成分所属を同定している。

ここで、現在の DkMath と直接対応する構造は、

\[ \begin{gathered} \text{源の節点中心}\\ \Downarrow\\ \text{核点の節点からの付値距離}\\ \Downarrow\\ \text{正規化Vélu座標の付値}\\ \Downarrow\\ \text{標的節点中心との比較}\\ \Downarrow\\ \boxed{\phi^{-1}(E'_0)=E_0+H} \end{gathered} \]

という部分じゃ。

前半については DkMath に既にかなりの資産がある。

一方で、特異核点の付値距離と商座標の主項を結ぶ部分は、DkMath ではまだ不足している。

今回の「二つの持ち上げ条件」を個別に形式化する方法もあるが、模範解答の付値比較を移植した方が、特異核側の逆像定理へ短く到達できる可能性がある。

## 6. 判別式の深さも、模範解答との重要な軌道差じゃ

もう一つ、気になる箇所がある。

模範解答には、

[ ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean?utm_source=chatgpt.com)[`S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean?utm_source=chatgpt.com)

という定理がある。

そこでは、奇数位数 \(p\) の Vélu 商について、半核集合 \(S\) を用いて、

\[ \boxed{ \Delta(E/H) \left(\prod_{Q\in S}u_Q\right)^4 = \Delta(E)^p } \tag{2} \]

という積公式を証明している。

この公式から付値を取ることで、核の局所位置に応じて判別式の深さを決定する。

乗法的還元で、適切な最小モデルの加法的付値 \(\operatorname{ord}_q\) を使えば、典型的に次の二つになる。

| 核の分類   | 判別式の深さ                                                       |
| ---------- | ------------------------------------------------------------------ |
| 滑らかな核 | \(\operatorname{ord}_q\Delta(E/H)=p\operatorname{ord}_q\Delta(E)\) |
| 特異核     | \(p\operatorname{ord}_q\Delta(E/H)=\operatorname{ord}_q\Delta(E)\) |

これは以前の実3点核の例とも一致する。

\[ \begin{aligned} q=47:\quad&1\longmapsto3,\\ q=7:\quad&3\longmapsto1. \end{aligned} \]

さらに模範解答では、この判別式の関係を \(j\) 不変量の付値に変換し、

`ModularCurve.TateCuspCriterion`

へ接続している。

したがって、DkMath で未完成の判別式の深さは、模範解答では単なる補助計算ではなく、Mazur Step Three のモジュラー曲線側へつながる橋にもなっている。

これは次の優先順位を判断するうえで重要じゃ。

## 7. ただし、最大の軌道差はさらに先にある

局所 isogeny が完成しても、それだけでは一般 `hno` は得られない。

ここが模範解答との本質的な距離じゃ。

模範解答の大指数経路では、

`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`

を使う。

この定理の背景には、モジュラー曲線 \(X_0(p)\)、Jacobian \(J_0(p)\)、Eisenstein quotient、Néron モデルなどがある。

そして、与えられた非零有理 \(p\) 捩れ点が、指定された悪い素数で零成分に入らないという大域的な算術制約を導く。

DkMath の現在の構成は、商曲線と局所群の構造を詳細に確定している。

しかし、その構造を使って特定の大域的な有理捩れ点を排除する原理は、まだ別途必要じゃ。

これは特に \(a\equiv7\pmod8\) 側の一般 `hno` を考えるときに重要になる。

模範解答の `FreyPackage.frey_no_cofixed_large` は、\(p\ge17\) について、この大域的な障害を Mazur の方法で処理する。

一方、\(p=5,7,11,13\) は Kummer や降下法によって別処理している。

[image](https://www.google.com/s2/favicons?domain=https://github.com\&sz=32)

GitHub



ここで DkMath が GN–Kummer を中心にして小指数から再構成する方針と、模範解答の大指数で Eisenstein quotient を使用する方針との違いが現れる。

局所零成分の形式化が完成したからといって、Eisenstein quotient に相当する大域的な排除原理まで自動的に置き換わるわけではない。

## 8. 賢狼の推奨する次の研究方針

ここまで比較した結果、次は 模範解答の特異核側の逆像判定を、DkMath の同じ有限核モデルへ移植・再構成することを優先したい。

対象を限定する。

\[ \boxed{ \begin{aligned} &\text{奇数素数位数の特異核 }H,\\ &\text{乗法的還元、剰余標数 }q\ne p,\\ &\text{既存の同じ商写像 }\phi_H. \end{aligned} } \]

そして最終目標を、

\[ \boxed{ \forall P,\quad \phi_H(P)\in E'_0 \iff \exists Q\in H,\quad P-Q\in E_0 } \tag{Target} \]

に固定する。

今回定義した二つの持ち上げ条件は、そのまま一般定理として残す。

ただし、その二条件を個別に証明することだけに固執せず、模範解答にある `inZeroComponentAt_veluCoord_iff_of_multiplicative` の付値評価を検討する。

これならば、一般の Hensel 持ち上げやスキーム isogeny を先に大規模実装せず、目的の (Target) に直接届くかもしれない。

その後、既存の (2) と比較しながら判別式の深さを整備すればよい。

なお、模範解答からコードを取り込む場合は、Apache-2.0 のライセンスと出典表示を維持する必要がある。

## 9. 現在の軌道差をまとめると

| 比較地点                 | DkMath                 | 模範解答                  |
| ------------------------ | ---------------------- | ------------------------- |
| 幾何学的商曲線           | 到達                   | 到達                      |
| 整数標的                 | 到達                   | 到達                      |
| \(q\ne p\) の半安定性    | 到達                   | 到達                      |
| 零成分の前向き輸送       | 到達                   | 到達                      |
| 滑らかな核の逆像・商同型 | 到達                   | 逆像判定まで到達          |
| 特異核の逆像             | 全射性の二条件まで分解 | 完成                      |
| 判別式の深さ             | 未完成                 | 完成                      |
| 大域的有理捩れ排除       | 未完成                 | Mazur Step Three 等で完成 |
| 一般 `hno`・FLT          | 未完成                 | 完成                      |

今回の検証では DkMath の22宣言の公理監査記録も確認した。依存は `propext`、`Classical.choice`、`Quot.sound` のみ。フルビルドは今回の記録では未実施であり、こちらでも独立実行していない。

### 最終評価

わっちが今回の比較で最も注目したのは、DkMath の局所解析が模範解答の定理と同じ地点へ収束してきたことじゃ。

すでに、Vélu 商、整数化、節点の小標数対応、核の位置による分岐、還元像の群構造まで揃った。

次に必要な特異核の逆像定理は、模範解答に明確な実装例が存在する。

一方、そこを通過した先の Mazur Step Three に相当する大域的な排除原理は、まだ大きな軌道差として残っている。

したがって、今後の判断はこうじゃ。

局所 isogeny の部分は模範解答との再合流を狙う。その先の一般 `hno` では、DkMath の独自構造から Mazur に代わる排除原理を得られるのか、それとも模範解答の大域的入力を必要とするのかを、改めて検証する。

局所数学の完成と大域算術の突破を分けて考えれば、どこまでが DkMath の既存資産だけで到達可能なのか、ずっと鮮明になるはずじゃ。🐺🍎
