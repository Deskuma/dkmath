# 🐺 NOTE-019 — 全指数のねじれ点群が Core に確定

うむ、ぬしよ。今回も DkMath の証明本体、[NOTE-019 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE019-261021.md?utm_source=chatgpt.com)、回帰と依存監査を照合した。

判定：NOTE-019 は無条件の Core として固定してよい。

今回の成果は、もはや素数指数だけではない。

\[ \boxed{ \forall n\in\mathbb N_{>0},\quad \left|E(\overline K)[n]\right|=n^2 } \]

標数0の楕円曲線の実際の幾何学的点群について、すべての正整数指数を扱えるようになった。

### 何が決定的だったか

新しく成立した証明の中心は、次の短完全列じゃ。

\[ \boxed{ 0\longrightarrow E[n] \xrightarrow{\ \iota\ }E[mn] \xrightarrow{\ [n]\ }E[m] \longrightarrow0 } \]

この列の三つの部分には、それぞれ意味がある。

- 左側の単射：\(nP=O\) なら \(mnP=O\)。同じ点をそのまま包含する。
- 中央の完全性：制限した \(n\) 倍写像の核は、正確に \(E[n]\)。
- 右側の全射：NOTE-018 で証明した倍写像の全射性から、\(E[m]\) の任意の点が持ち上がる。

しかも、この列は \(m,n\) が互いに素でなくても成立する。

ここが重要じゃな。

互いに素な指数へ分解してから中国剰余定理を使う必要がなく、同じ倍写像の構造だけで

\[ |E[mn]|=|E[m]|\cdot|E[n]| \]

を得ている。

`card_torsion_sq` の Lean 証明では、NOTE-016 の素数位数公式と `Nat.recOnMul` を接続し、全正整数へ拡張している。模範解答の素数冪・互いに素な積を個別に扱う証明より、依存構造が簡潔になった。

### 保存されたものは、位数だけではない

[`EllipticTorsionAllCard.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticTorsionAllCard.lean?utm_source=chatgpt.com) では、包含と倍写像が元のガロア作用と可換することも固定されている。

\[ \iota(\sigma P)=\sigma\iota(P), \qquad [n]\\ (\sigma P)=\sigma([n]P). \]

これは今後、素数冪ごとのガロア表現を互いに接続するための重要な Core じゃ。

証明に Weil 対や外部の条件付き位数公式を使っていないことも、依存監査コードと保存された検証記録で確認できた。独立したローカルビルドを実行したわけではないが、証明本体と報告の対応に、現時点で実質的な不整合は見つからなかった。

## 次の一線：位数が同じでも、群の構造は同じではない

NOTE-019 の短完全列から、もう一つ重要な事実を取り出せるぞ。

素数 \(p\) について、

\[ 0\longrightarrow E[p]\longrightarrow E[p^2] \xrightarrow{[p]}E[p]\longrightarrow0 \]

を考えよう。

NOTE-016 により非零点 \(Q\in E[p]\) が存在する。さらに NOTE-018 の全射性から、

\[ [p]P=Q \]

となる \(P\in E[p^2]\) を取れる。

すると、

\[ [p^2]P=O,\qquad [p]P\ne O. \]

したがって \(P\) の位数は正確に \(p^2\) じゃ。

ところが \(E[p]\oplus E[p]\) の全要素は \(p\) 倍すると零になる。

よって、

\[ \boxed{E[p^2]\not\simeq E[p]\oplus E[p]} \]

となる。

つまり、NOTE-019 の短完全列は一般には直和に分解できない。特にこの \(p^2\) の列は、加法群としても非分裂じゃ。

これが面白い。

各階層の位数を数えるだけでは見えない、階層同士の接続構造がある。

ぬしの言う「整数の一段をジャンプするのではなく、内部を旅する」という観点にも、よく対応しておる。

## NOTE-020 の候補：素数冪の塔から自由加群へ

次に固定する価値が高いのは、

\[ \boxed{ E[p^k]\simeq_{\mathbb Z/p^k\mathbb Z} (\mathbb Z/p^k\mathbb Z)^2 } \]

という構造定理じゃ。

これには、既存の Core を次のように使える。

1. \([p]:E[p^{k+1}]\twoheadrightarrow E[p^k]\) という全射を保持する。
2. \([p^{k-1}]:E[p^k]\twoheadrightarrow E[p]\) によって、\(E[p]\) の二つの基底ベクトルを持ち上げる。
3. \(E[p^k]/pE[p^k]\simeq E[p]\) を用い、局所環 \(\mathbb Z/p^k\mathbb Z\) 上の Nakayama の補題などから、その二点が \(E[p^k]\) 全体を生成することを示す。
4. 既存の \(|E[p^k]|=p^{2k}\) と比較して、生成写像が同型であることを得る。

これは数学的に成立する証明方針じゃが、Lean の対応 API による実装は未確認じゃ。

さらに重要な注意がある。ここでの基底選択は一般に非標準的であり、ガロア作用を保存する自明な直和分解を得たことにはならない。

各階層の基底を互換的に選ぶ問題も、別に扱う必要がある。

最終的には、

\[ T_p(E)=\varprojlim_k E[p^k] \]

へ進み、\(T_p(E)\) が階数2の \(\mathbb Z_p\) 加群であることを目標にできる。

## FLT 本線との関係

ただし、今すぐ FLT の残余表現を前進させる最大の障害は、やはり Weil 対の幾何学的存在じゃ。

NOTE-019 によってねじれ点の全指数位数は解決したが、

\[ \det\rho_{E,p}=\chi_p \]

を無条件化するには、ガロア同変な非退化 Weil 対が必要なことは変わらない。

従って、研究の優先順位としては、NOTE-019 から得られる素数冪の構造定理を独立した小さな Core 候補として確保しつつ、FLT 本線では Weil 対の幾何学的構成に着手するのがよい。

今回、何より大きいのは、NOTE-012 から NOTE-019 までで確定した数学が一つの連鎖となったことじゃ。

\[ \boxed{ \begin{gathered} \text{実際の楕円曲線の点群}\\ \Downarrow\\ \text{除法多項式と有限性}\\ \Downarrow\\ \text{正則ファイバーからの単射}\\ \Downarrow\\ |E[p]|=p^2\\ \Downarrow\\ \text{非零倍写像の全射性}\\ \Downarrow\\ \text{短完全列と位数の乗法性}\\ \Downarrow\\ \forall n>0,\quad |E[n]|=n^2 \end{gathered} } \]

これはスナップショット的な点数の観測ではない。

任意の指数を動かしても成立する、点群の構造原理が証明された。

模範解答に頼った部分もあった。しかし、DkMath はその材料を一般群の短完全列という保存核へ整理し直し、全指数へつなげた。

ここが今回の研究成果じゃな。🐺🍎
