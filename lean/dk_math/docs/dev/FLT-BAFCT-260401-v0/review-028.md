# review-028: GNReducedGap の構造分析のまとめと戦況判断

うむ、かなり良い前進じゃ。
慎重に読むと、今回の戦況は **「入口の q-adic 層はほぼ制圧、真の本丸は依然として局所-大域ギャップ」** という形に整理された、と見るのが正確じゃ。特に `gnGeomSum₂Representation`、`geomSum_zero_imp_pow_eq_one`、`descentSizeReduction`、`gnAtZero` が埋まり、`qAdicResidue` も実質的に **`pow_eq_one_imp_eq_omega_pow` ただ 1 本** に依存する形まで削れたのは大きい。

## 1. 現状の判定

いまの最も正確な判定は、**DescentChain の局所 q-adic 入口はほぼ clean、しかし GNReducedGap の核心はまだ untouched に近い** じゃ。
ログ上も、残る独立 `sorry` は `pow_eq_one_imp_eq_omega_pow` 1 件で、これは「有限体で (r^p=1) なら (r=\omega^j)」という巡回群論の接続問題として孤立しておる。したがって、形式化の難所はもはや sprawling ではなく、**非常に局所化された代数補題 1 本** と言ってよい。

ただし注意点もある。報告文には「ビルドは成功、全てクリーン」とある一方で、同じ報告の表では `qAdicResidue` が依存 `sorry` 1 を持つと明記されておる。ゆえに、ここは **「ファイルはビルド成功、独立 `sorry` は 1 件」** と読むのが正しい。完全 clean とまではまだ言わぬ方が誠実じゃ。

## 2. 今回ほんとうに固まったところ

今回いちばん価値が高いのは、`QAdicResidue` の論理が **ZMod q 上の直接算術だけでほぼ閉じる** と実証できた点じゃ。
証明戦略は、

$$
q \mid x \Rightarrow z^p \equiv y^p \pmod q
$$

から (r:=z y^{-1}) を作り、

$$
r^p=1,\qquad r\neq 1
$$

を出して、最後に (r=\omega^j) に落とす、という極めて素直な流れになっておる。つまり Level 0 の `QAdicResidue` は、もはや「何をやるか不明」ではなく、**最後の有限体巡回群補題を差し込めば終わる** 段階じゃ。

さらに `gnGeomSum₂Representation` が完全証明されたのも大きい。これで

$$
GN(p,z-y,y)=\sum_{i=0}^{p-1} z^i y^{p-1-i}
$$

が Lean 上で正式な橋になり、Cosmic Formula 側の恒等式と Mathlib の `geom_sum₂` を往復できるようになった。これは今後、cyclotomic product と自然数多項式をつなぐときの共通地盤になる。

## 3. 数値実験が教えたこと

ここも大きい。
数値実験の結論は、**単一素数 (q) の mod (q) 局所条件だけでは GNReducedGap は落ちない**、ということじゃ。報告では、Kummer 型の p 乗剰余制約を調べると、単数群 coset を掛ける自由度のせいで

$$
{\text{unit} \cdot p\text{乗冪}} = (\mathbb{Z}/q\mathbb{Z})^\times
$$

となり、**局所 residue obstruction が完全に自明化** すると整理されておる。これはかなり重大じゃ。つまり「mod (q) の根の位置」や「((\omega^{j_0}-\omega^j)) が p 乗剰余か」を見るだけでは、本丸には届かぬ。

この結論は、ぬしが少し前から観測しておった「GNReducedGap は LOCAL 構造では証明できず、GLOBAL 構造が必要」という見立てとよく整合しておる。
つまり今回の数値実験は、単なる探索ではなく、**局所合同論だけで押し切る路線が筋悪だと確認した** のじゃ。これは撤退線の確認ではなく、敵の城門の材質が分かったという意味で立派な前進じゃよ。

## 4. いまの open kernel の読み方

したがって、いまの層構造はかなり明快じゃ。

* Level 0: `QAdicResidue`
* Level 1: `SuperWieferichCongruence`
* Level 2: `QAdicDescentExistence`

という三層分解は、戦況図として正しい。しかも Level 0 はほぼ陥落、Level 1 は Hensel lifting の技術問題、Level 2 だけが **局所から整数解への existence** という大域問題として残っておる。報告自身も、ここを「代数的整数論が本質的に必要」と総括している。

ここで重要なのは、**Level 2 の open は形式化不足ではなく、数学そのものの重さ** だということじゃ。
サイズ縮小 `z' < z` はすでに theorem 化されており、また整除条件から商が整数になることも整理済みじゃ。残っているのは

$$
z'^p=(x/q)^p+y^p
$$

を満たす **整数** (z') の存在だけで、これは局所合同や valuation だけでは埋まらぬ。ここを見誤らなければ、戦線の優先順位はぶれぬ。

## 5. 戦況の解説

ゆえに、今の局面はこう読むのがいちばん筋が良い。

第一に、**Lean 実装としては良い地固め** じゃ。
`gnGeomSum₂Representation` と `geomSum_zero_imp_pow_eq_one` が入ったことで、`QAdicResidue` までの路線は非常に clean になった。ここは「証明可能なところを本当に証明し、open kernel を露出させる」という理想的な進み方をしておる。

第二に、**数学的には Kummer の “unit 部分” が本丸らしい** と見えてきた。
valuation の集中や residue root-of-unity だけならもうかなり見えておる。しかし、それらは全部 local information であって、descent existence を決めるには足りぬ。報告の「Kummer の証明が実際に使うのは mod (q) の局所情報ではなく (\mathbb{Z}[\zeta_p]) の大域構造」という判断は、かなり重い。ここは過大評価せず、そのまま受け取るのがよい。

第三に、ぬしの戦線分離も正しい。
いまは `pow_eq_one_imp_eq_omega_pow` を潰して Level 0 を完全 clean 化する路線と、Level 2 の大域的 obstruction を別筋で掘る路線を分けてよい。前者は **局所的で実装寄り**、後者は **本丸の数学** じゃ。混ぜると視界が曇る。

## 6. 次の一手

わっちなら、次は二段構えで行く。

まずは `pow_eq_one_imp_eq_omega_pow` を潰して `QAdicResidue` を完全 clean にする。
これは数学の新発見というより **実装の仕上げ** じゃが、Level 0 を閉じ切る意義は大きい。ここが閉じれば、以後は「局所 q-adic 入口は完了」と胸を張って言える。

そのうえで本命は、Level 2 を **unit / residue ではなく “element-level p-th power decomposition” の必要条件** として再定式化することじゃ。
つまり

$$
z-\zeta^{j_0}y
$$

の valuation だけではなく、その先頭係数や unit 部分にどんな p-th power 条件がかかるかを、elementary に extraction できるかを探る。いまの数値実験は、その必要性をかなり強く示しておる。

## 7. 一文でまとめると

**今回の状況は、Level 0 の `QAdicResidue` がほぼ手中に入り、Level 2 の GNReducedGap / QAdicDescentExistence は mod (q) の局所情報だけでは絶対に足りず、Kummer の unit・大域構造が真の本丸だと見えてきた段階** じゃ。
これはかなり良い戦況整理じゃよ。
