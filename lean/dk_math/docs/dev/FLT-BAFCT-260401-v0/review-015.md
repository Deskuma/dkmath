# review-015: `RealizationSeedTarget` の核は `hzEq` であることの意味と今後の攻略

うむ、**概ねこれで良い**。
しかも、かなり筋が良い。
ただし賢狼なら、結論をもう半歩だけ sharpen する。

## A. 判定

ぬしの結論

$$
\text{`RealizationSeedTarget` の hard kernel は } \texttt{hzEq}
$$

これは **本質的に正しい**。
添付の分析でも、`RealizationSeed` の各 field のうち genuinely hard なのは

$$
\texttt{hzEq} : x'^p + y'^p = z'^p
$$

であり、`hxMul`, `hyEq` などは provenance / bookkeeping 側であると整理されておる。さらに `BranchAQAdicDescentData` から

$$
x' = p \cdot (t \cdot s')
$$

の形まで見えているので、問題は結局

$$
\exists z' \in \mathbb{N},\quad x'^p + y^p = z'^p
$$

という **p 乗根の実在** に縮んでいる、という見立てになる。ここは正しい。

## B. sharpen すべき点

わっちなら、結論をこう言い換える。

$$
\boxed{
\begin{array}{l}
\text{真の open kernel は `RealizationSeedTarget` 全体ではなく、} \\
\texttt{hzEq}\text{ を供給する } \texttt{PthRootTarget}\text{ である}
\end{array}
}
$$

つまり、

* `RealizationSeedTarget` をそのまま「最後の敵」と呼ぶのは、少し大きすぎる
* 本当に孤立させるべきは、その中の
  $$
  x'^p + y'^p = z'^p
  $$
  を作る核だけ

じゃ。

ぬしの添付分析でも、戦略 C として

* quotient side は trivial / concrete 化可能
* p-th root side だけを axiom / target として隔離

という二分構造化が最善だ、と整理されておる。わっちもこれに賛成じゃ。

## C. どこが良い推論だったか

良い点は 3 つある。

### C1. `Nat.root` 不在を「道具不足」と見なさなかったこと

これは大事じゃ。
本質は「root 関数がない」ではない。

本質は、

$$
x'^p + y'^p
$$

が **完全 p 乗であるという定理が、まだ無い** ことじゃ。
関数の有無ではなく、存在定理の有無を見ている。ここは鋭い。

### C2. Kummer descent の重さを正しく見積もったこと

添付分析では、

* Kummer / \(\mathbb{Z}[\zeta_p]\) 路線は重すぎる
* q-adic / GN 路線は研究継続中
* だからまず kernel isolate が最善

と整理されておる。
これは設計として正しい。DkMath 全体でも「強い一般論より、まず局所核を固定する」という方針が繰り返されておるからの。

### C3. `hzEq` を chain 全体から切り離して見たこと

これが一番よい。
`RealizationSeedTarget` の残り 5 割以上は、実は already concrete になっておる。
だから「全部 hard」と見ず、hard part を 1 行へ圧縮したのは勝ち筋じゃ。

## D. どこを少し修正すべきか

一点だけ、慎重にしてよい部分がある。

添付分析では、

$$
x'^p + y^p = z'^p
$$

の存在を「Kummer descent の核心」とほぼ同一視しておる。
これは大筋では良いが、実務的には少し広すぎる。

なぜなら、今の PrimeProvider 文脈では欲しいのは **full Kummer theory** ではなく、

$$
\boxed{
\text{今の Branch A restore chain に必要な最小限の p-th power realization}
}
$$

だけだからじゃ。

つまり、目標は

* 「一般に (a^p+b^p) が p 乗になる条件」
  ではなく
* 「今の descent data から生じる特殊形についてのみ (z') を取れるか」

へ絞るべきじゃ。

これを忘れると、必要以上に大砲を持ち出すことになる。

## E. わっちの最終結論

だから、結論はこう整理すると最も良い。

$$
\boxed{
\text{結論の方向は正しい。}
}
$$

ただし、最終形はこうじゃ。

$$
\boxed{
\text{`RealizationSeedTarget` を二分せよ。}
}
$$

すなわち、

### E1. quotient side

* `x'`
* `y'`
* `hxMul : x = q*x'`
* `hyEq : y' = y`

これは concrete / bookkeeping 層。

### E2. p-th root side

* `hzEq : x'^p + y'^p = z'^p`

これだけを

$$
\texttt{PrimeGe5BranchAPrimitiveRestorePthRootTarget}
$$

のような形で isolate する。

そしてその上で、

$$
\text{RealizationSeedTarget} =
\text{QuotientSide} +
\text{PthRootTarget}
$$

として再構成する。
これが最も綺麗で、次の一手も明確になる。

## F. 次の戦略

わっちなら次はこうする。

1. `RealizationSeedTarget` を二分する
2. `PthRootTarget` を新しい genuine kernel として明示する
3. `RealizationSeed_of_pthRoot` の橋 theorem を置く
4. その後にだけ q-adic / GN / Kummer 的攻略を始める

つまり、

$$
\boxed{
\text{まず kernel isolate、次に攻略}
}
$$

じゃ。
ゆえに、ぬしの結論は **方向として正しい**。
そして賢狼の判定では、**そのまま進めてよいが、名前と責務をさらに 1 段だけ細く切ると最善** じゃよ。
