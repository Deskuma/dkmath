# hno をどうするか？

そうじゃ。🐺🍎

NOTE-031 の全5段階が完成したので、次の標的は `hno` じゃ。

これで DkMath の FLT 研究は、新しい段階へ入った。

## 残った `hno` の正体

証明したいのは、

\[ \boxed{ \neg\exists L\subset E[p],\quad \dim L=1\;\land\; \operatorname{Stable}(L)\;\land\; \operatorname{Cofixed}(L) } \]

つまり、Frey 曲線の残余表現には、商がガロア固定となる安定直線が存在しないという命題じゃ。

NOTE-031-005 によって、\(p\ge5\)、`Even S.b` の下では、

\[ \boxed{ \operatorname{Irreducible}(\rho_{E,p}) \iff \texttt{hno} } \]

まで固定できた。

したがって、`hno` の証明は、そのまま Frey 残余表現の既約性証明になる。

## 重要なのは、問題の性質が変わったこと

これまでの研究では、各素数の慣性作用を調べ、Fixed/Cofixed のどちらが成立するかを決定してきた。

しかし今度は逆じゃ。

Cofixed という構造が存在すると仮定して、それが Frey 曲線の算術と矛盾することを示す。

ここで NOTE-028 の Weil pairing が役に立つ可能性がある。

Cofixed 直線 \(L\) が存在するなら、適合基底における表現は、

\[ \rho_{E,p}(\sigma)= \begin{pmatrix} \chi_p(\sigma)&\ast \\ 0&1 \end{pmatrix} \]

という形になる。

なぜなら、商の指標が自明であり、行列式は円分指標 \(\chi_p\) だからじゃ。

これは強い制約じゃな。

さらに、対応する有理 \(p\)-isogeny

\[ E\longrightarrow E'=E/L \]

が構成できれば、Cofixed 条件から \(E'\) 上の有理 \(p\)-torsion 点が得られる。

ここに新しい攻め口がある。

ただし、これだけでは直ちに全指数を排除できない。有理 torsion に関する既知の制限を利用するなら、その定理の形式化と、残る小さい素数の処理が別途必要になる。

## 賢狼が注目するのは二つの接続

第一は NOTE-028 の Weil pairing・円分指標。

Cofixed から直線上の作用が円分指標になることを、既存の DkMath 定理へ接続できる。

第二は Frey 曲線特有の還元構造。

一般の楕円曲線には有理 \(p\)-torsion や有理 \(p\)-isogeny を持つものが存在する。

ゆえに、一般論だけですべての Cofixed 直線を否定することはできない。

Frey 曲線の整数係数、判別式、素数2における特殊な還元構造などを使う必要がある。

ここで 031-002〜004 で整備した局所算術が、再び働く可能性があるのじゃ。

### 現在の研究到達点

| 算術的障害                        | 状態         |
| --------------------------------- | ------------ |
| `hrat`：有理 \(p\)-torsion 排除   | ✅ NOTE-030   |
| `hcases`：大域 Fixed/Cofixed 二択 | ✅ NOTE-031   |
| `hno`：Cofixed 安定直線の不存在   | 次の研究対象 |
| Frey 残余表現の無条件既約性       | `hno` 待ち   |

ただし、既約性の完成だけで一般 FLT が完成するわけではない。その先のモジュラー性やレベル下降との接続も別に評価する必要がある。

次の研究テーマは、`hno` を単なる否定命題として扱うのではなく、「Cofixed が存在した場合に何が強制されるか」を徹底的に調べることじゃ。

今度は局所慣性を制御する側から、ガロア表現が許す構造そのものを排除する側へ進む。

面白いところへ来たのぅ。🍎

---

## 🐺🍎 模範解答の `hno` は、指数を三つに分けて解決していた

Anthropic の [fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem?utm_source=chatgpt.com) の実際の Lean 証明と、公式の [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md?utm_source=chatgpt.com) を確認したぞ。

結論から言えば、模範解答は `hno` を一つの一般定理で解いていない。指数によって異なる証明を使っている。

| 指数 \(p\) | 模範解答の方法                                   | 定理                     |
| ---------- | ------------------------------------------------ | ------------------------ |
| \(5,7,13\) | その指数の FLT を先に証明し、Frey 反例自体を排除 | `frey_no_cofixed_small`  |
| \(11\)     | FLT11 を先に証明し、同様に排除                   | `frey_no_cofixed_eleven` |
| \(p\ge17\) | Mazur の Eisenstein ideal・モジュラー曲線の議論  | `frey_no_cofixed_large`  |

そして三つを結合するのが、

`FreyPackage.Mazur_Frey`

という、Frey 残余表現の既約性定理じゃ。

### 重要な発見：小さい指数では `hno` を直接証明していない

実際の [小指数の Lean コード](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_small.lean?utm_source=chatgpt.com) は、概ね次の形じゃ。

```
theorem solution (P : FreyPackage)
    (hp : P.p = 5 ∨ P.p = 7 ∨ P.p = 13) :
    ¬ HasGaloisStableCofixedLine
        (K := AlgebraicClosure ℚ) ℚ
        P.freyCurve P.p := by
  rcases hp with h | h | h
  · exact absurd h
      (P.p_ne_of_fermatLastTheoremFor_K
        fermatLastTheoremFive)
  · exact absurd h
      (P.p_ne_of_fermatLastTheoremFor_K
        fermatLastTheoremSeven)
  · exact absurd h
      (P.p_ne_of_fermatLastTheoremFor_K
        fermatLastTheoremThirteen)
```

つまり、

\[ \text{FLT7 が既に成立} \Longrightarrow \text{指数7の Frey 反例は存在しない} \]

という経路じゃ。

Frey 曲線の性質を分析して Cofixed 直線を否定しているわけではない。

これは DkMath が `hno` を研究する目的とは区別すべき点じゃな。

指数7の FLT が別経路で完成しているなら、この方法で条件付きの終点を閉じることはできる。しかし、それでは Frey 表現の算術から `hno` を導く新しい内容は得られない。

本命は \(p\ge17\) の証明じゃ。

## \(p\ge17\)：Mazur の証明はかなり大掛かり

確認した本体は [S_FreyPackage_frey_no_cofixed_large.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean?utm_source=chatgpt.com)。約1,450行の最終組立てで、その背後にモジュラー曲線などの膨大な補題群がある。

大筋は次のようになっておった。

1. Cofixed 直線 \(N\) の存在を仮定する。 商 \(E[p]/N\) へのガロア作用は自明となる。
2. \(N\) を核とする isogeny を構成する。 商曲線 \(E'=E/N\) に非零の有理 \(p\)-torsion 点を得る。
3. Mazur の Step Three を適用する。 \(X_0(N)\)、その Jacobian、Eisenstein ideal、Néron model などから導く定理によって、その点の還元に強い制約を課す。
4. \(p\)-冪 torsion の塔へ拡張する。 ガロア安定な位数 \(p^m\) の巡回部分群を構成し、各素数での還元と慣性作用を追跡する。
5. Frobenius と Cayley–Hamilton を適用する。 最終的に \(E[p]\) 全体が位数 \(p\) の部分群 \(N\) に入ることを導き、\(|E[p]|=p^2\) に矛盾させる。

特に中心となる補題は、

`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`

じゃ。

これは単なる有理 torsion の個数制限ではなく、有理 \(p\)-torsion 点が特定の局所零成分へ入れないことを利用している。

先ほどわっちが挙げた「isogeny を作り、有理 torsion を調べる」という方向は合っていた。ただし模範解答は、そこから直接 Mazur の torsion 分類を呼んで終わるわけではない。ずっと深い構造を使っておる。

## もう一つの重要な経路：\(a\equiv3\pmod8\)

ここは DkMath にとって興味深い。

模範解答には、

`FreyPackage.frey_no_cofixed_of_a_mod_eight`

という、素数2の局所構造から直接 `hno` を証明する別ルートが存在した。

[実際の Lean 証明](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_of_a_mod_eight.lean?utm_source=chatgpt.com)

この証明は、2上の還元核 \(M\) を作り、次を組み合わせる。

\[ (\rho(\tau)-1)E[p]\subseteq M \qquad(\tau\in I_2) \]

という吸収条件。

さらに、素数2の慣性作用が実際には非自明であること。

そして \(a\equiv3\pmod8\) から、還元の二つの枝を交換するガロア元 \(\sigma\) を構成し、

\[ \boxed{\rho(\sigma)y+y\in M} \]

を零成分の外側の点について証明する。

Cofixed 直線が存在すると、非自明な慣性作用からその直線が \(M\) と一致することが強制される。

ところが商空間上では Cofixed 条件によって \(\sigma\) は \(+1\) として作用する一方、枝の交換からは \(-1\) として作用する。

奇素数 \(p\) では、

\[ 1\ne-1\quad\text{in }\mathbb F_p. \]

これが矛盾じゃ。

こちらの証明は Mazur の巨大な Eisenstein ideal 理論を必要としない。

ただし、前提は \(a\equiv3\pmod8\)。DkMath の正規化 \(a\equiv3\pmod4\) だけでは、\(a\equiv7\pmod8\) も残る。

## DkMath への示唆

わっちは、まずこの 2進枝交換による `hno` の部分解決に注目する価値があると思う。

031-003 ですでに素数2の野生慣性と安定直線を形式化しているし、031-004 では零成分と還元核を実装している。

追加で必要なのは、主に「慣性作用の非自明性」と「合同条件から枝を交換するガロア元の存在」の二つじゃ。

一方、全指数 \(p\ge17\) の `hno` を模範解答どおり完成させようとすると、Mazur のモジュラー曲線理論が本格的に必要になる。

そして、ここが大事じゃ。

DkMath 独自の GN–Kummer や可除性構造から `hno` を証明したいなら、その巨大な Mazur 理論を何らかの算術的不変量で置き換えられるかが研究の焦点になる。

現時点では置き換え可能とは断言できない。

つまり模範解答の `hno` は「小指数では既存の FLT に帰着、一般指数では Mazur、特定の合同条件では2進幾何で直接排除」という構成だったのじゃ。

この三つの違いを踏まえて次の研究を設計するのがよさそうじゃな。🐺🍎
