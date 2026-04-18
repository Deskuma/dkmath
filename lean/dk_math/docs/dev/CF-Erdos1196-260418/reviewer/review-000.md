# `CosmicFormula-Erdos1196` の実装開始について

おお、ついに動き始めたかや。これは良い流れじゃ。

`CosmicFormula-Erdos1196` の実装は、完全に白紙からの着手ではなく、すでにかなり強い **設計済みの spine** の上に乗っておる。設計書では、初手の目標を「確率過程そのものの完全形式化」ではなく、まず

$$
\text{Big}=\text{Body}+\text{Gap},\qquad
\text{Body}=\text{Core}+\text{Beam}
$$

を **質量保存 API** として再編し、その上で primitive prime・(GN)・`padicValNat` を「下降 flow」の痕跡として束ね、最後に ABC 側へ薄い bridge を差す、という順に固定しておる。

しかも、この方針は会話整理資料とも一致しておる。そこでは、宇宙式族の Big/Body/Gap、2D トロミノ分解、(2^d \mid n) の整数化規格、さらに d/2 構造と反転を通じた調和側への写像候補までが、すでに Lean 設計の層として整理済みじゃ。つまり今回の実装開始は、単なる思いつきではなく、以前から積んでおった宇宙式族・トロミノ・調和写像の流れが、Erdős #1196 文脈で **質量保存 / 分岐 / valuation flow** に変換され始めた、ということじゃな。

いちばん大事なのは、今回の案件で **やることと、まだやらぬことがきれいに切れておる** 点じゃ。実装計画では、初回は

$$
\Lambda(q)/\log n
$$

の実数確率 kernel や

$$
1 + O!\left(\frac{1}{\log x}\right)
$$

の解析評価までは入れず、まず **保存則・子和が親を超えない・primitive により chain が衝突しない** という、代数的で再利用可能な骨組みを先に通すと明言しておる。これは実に賢い。Lean では、最初から解析まで抱え込むより、この順のほうがはるかに森が燃えにくい。

さらに強いのは、既存資産との接続先がすでに特定されていることじゃ。計画では既存利用候補として `CoreBeamGap`、`ResidualNat`、`ResidualInt`、`PrimitiveBeam`、`ZsigmondyCyclotomicSquarefree`、`ABC.PadicValNat`、`ABC.Rad` が挙がっており、新規理論をゼロから起こすのでなく、既存補題に wrapper と alias を与えて #1196 的文脈に再公開する方針になっておる。これは DkMath 全体の設計思想とも整合しておる。INDEX でも、CosmicFormula と NumberTheory と ABC は別柱として整理されており、橋は薄く保つ流儀が確認できる。

なので、現状を賢狼ふうに戦況整理するとこうじゃ。

第一に、 **実装開始の場所は正しい** 。
`CosmicFormula/Mass/*` から入る順序は自然で、ここで保存則 API を固定すれば、その後の `ValuationFlow` や ABC bridge は薄く済む。

第二に、 **今回の本当の主役は確率ではなく保存則** じゃ。
確率法は最終的な読み替えだが、Lean 上で先に固定すべきなのは

$$
\mu(\text{Big})=\mu(\text{Body})+\mu(\text{Gap}),
\qquad
\sum \mu(\text{children}) \le \mu(\text{parent})
$$

という骨組みじゃ。この路線は以前の API 設計メモでもすでに明文化されておる。

第三に、 **Erdős #1196 の“確率的斬新さ”を、DkMath ではそのまま写す必要はない** 。
まずは `Mass` と `ValuationFlow` を作り、後から必要ならจริงの sub-Markov / hitting mass を specialization として足せばよい。これは実装計画そのものがそう判断しておる。

第四に、 **ABC への接続は副産物ではなく、最初から狙われている** 。
会話記録でも、primitive set の確率視点を ABC の `rad`・`padicValNat`・primitive prime・squarefree/squarefull へ橋渡しする構想が明確に語られており、その結果がそのまま `MassBridge` と `ValuationFlowBridge` に落ちている。

ゆえに、今の段階での最も良い見方はこうじゃ。

**`CosmicFormula-Erdos1196` の実装開始とは、Erdős #1196 の証明を Lean へ直写する作業ではなく、宇宙式の保存則を数論 flow の言葉へ翻訳するための共通基盤を、DkMath 内で独立した API として立ち上げる作業である。**

これはかなり筋が良い。
しかもうまく行けば、#1196 の再現だけでなく、ABC・primitive prime・GN/Tail・valuation 上界まで、同じ言語で扱えるようになる。そこが本当の収穫じゃな。

いま次に注目すべき最初の関門は、`Phase A` の 4 本、

$$
\texttt{mass\_big\_eq\_mass\_body\_add\_mass\_gap},
\quad
\texttt{mass\_body\_eq\_mass\_core\_add\_mass\_beam},
$$
$$
\texttt{mass\_big\_eq\_mass\_core\_add\_mass\_beam\_add\_mass\_gap},
\quad
\texttt{mass\_residual\_eq\_mass\_gap}
$$

が、既存 `CoreBeamGap / ResidualNat / ResidualInt` の wrapper として綺麗に閉じるかどうかじゃ。ここが通れば、もう道はかなり見える。

よい開始じゃ。これは単発実装ではなく、宇宙式を **保存則の言語** に持ち上げる転換点になりうるぞい。
