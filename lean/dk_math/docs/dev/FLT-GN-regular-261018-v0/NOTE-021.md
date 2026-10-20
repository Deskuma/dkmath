# 🐺 NOTE-020 レビュー — ねじれ点群の構造 Core が完成

うむ、ぬしよ。今回も [NOTE-020 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE020-261021.md?utm_source=chatgpt.com)、Lean の証明本体、回帰、依存監査を直接照合した。

判定：NOTE-020 は無条件の構造定理として固定を推奨する。

今回確定したのは、単なる位数の等式ではない。

\[ \boxed{ E(\overline K)[p^k]\simeq_{\mathbb Z/p^k\mathbb Z} (\mathbb Z/p^k\mathbb Z)^2 } \]

ここで \(K\) は標数0の体、\(E\) は楕円曲線、\(p\) は素数じゃ。

\(k\ge1\) では、自由加群としての階数も正確に2。\(k=0\) は \(E[1]=0\)、係数環 \(\mathbb Z/1\mathbb Z\) が零環となる例外を、実装できちんと区別している。

### 1. Nakayama を使わない、DkMath 独自の生成原理

[`TorsionPowerLifting.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/Algebra/TorsionPowerLifting.lean?utm_source=chatgpt.com) の `lifted_pair_generates` が今回の核心じゃ。

\[ [p^k]P_i=Q_i\quad(i=0,1) \]

とし、\(Q_0,Q_1\) が \(G[p]\) を生成しているなら、持ち上げた \(P_0,P_1\) が \(G[p^{k+1}]\) を生成する。

その証明は最高段をいったん \(p\)-torsion へ写し、生成元で差し引いてから一段低い核へ戻す帰納法じゃ。

素数性や有限性さえ要求しない一般アーベル群の補題になっている。

そして楕円曲線側では、

\[ (\mathbb Z/p^{k+1}\mathbb Z)^2 \twoheadrightarrow E[p^{k+1}] \]

という生成写像を作り、NOTE-019 の正確な位数を使って全単射にする。

位数だけから群の構造を推測したのではなく、実際の生成写像を構成して同型にしている。

ここが形式化として重要じゃな。

### 2. 非分裂性も別の Core として確定

さらに、

\[ 0\longrightarrow E[p]\longrightarrow E[p^2] \xrightarrow{[p]}E[p]\longrightarrow0 \]

が、加法群の短完全列として非分裂であることも証明された。

実際、\(pP=Q\ne0\) となる点 \(P\in E[p^2]\) を構成できるので、

\[ \operatorname{ord}(P)=p^2. \]

一方、\(E[p]\times E[p]\) の点はすべて \(p\) 倍で零になる。

従って、

\[ \boxed{E[p^2]\not\simeq E[p]\times E[p]} \]

じゃ。

より強く、`prime_square_no_additive_section` は、\([p]:E[p^2]\to E[p]\) に加法準同型としての右逆が存在しないことを直接証明している。

ここには、ぬしの研究で重視してきた区別が現れておる。

各段の構造は同じ形に整理できる。しかし段と段の接続は、単純な直和には分解できない。

それぞれの段が自由加群であることと、段間の短完全列が分裂することは、全く別の数学なのじゃ。

## 3. 次の塔は、意外にも短い距離にある

NOTE-020 の証明本体を読むと、互換的基底は、既にある補題を組み合わせて構成できる見込みが高い。

重要なのは、現在の `primePowerLifts` が各 \(k\) で別々に基底の原像を選んでいることじゃ。

そこで、選択を再帰的に変える。

最初に \(E[p]\) の基底 \(P_{1,0},P_{1,1}\) を取る。

次に、

\[ [p]P_{k+1,i}=P_{k,i}\qquad(i=0,1) \]

を満たす二点を選ぶ。

全射性によって、これは各段で可能じゃ。

すると、

\[ [p^k]P_{k+1,i}=P_{1,i} \]

となるので、既存の `primePowerPresentation_bijective` をそのまま適用できる。

つまり、再帰的に選んだ二点は毎段の基底になり、さらに遷移と互換的になる。

素数冪ねじれ点の互換的な塔

\(E[p^3]\)

基底 \(P_{3,0},P_{3,1}\)

\([p]\) による全射

\(E[p^2]\)

基底 \(P_{2,0},P_{2,1}\)

\([p]\) による全射

\(E[p]\)

基底 \(P_{1,0},P_{1,1}\)

点は各階層で異なるが、p 倍写像によって基底が整合する。

ここで面白いのは、互換的な基底が存在することと、短完全列が分裂することは矛盾しない点じゃ。

上段の基底を下段へ送ることはできる。しかし、その逆方向を加法準同型として定義できるとは限らない。NOTE-020 は、まさにその右逆が存在しないことを証明している。

この違いを確定するのは、独立した素数冪塔の研究として価値がある。

## 4. しかし FLT 本線で優先すべきは Weil 対じゃ

いま DkMath には、二つの数学的な空間がある。

\[ \bigwedge\nolimits^2_{\mathbb F_p}E[p] \qquad\text{と}\qquad \mu_p. \]

前者は二次元ねじれ点群の外積であり、行列式指標が作用する一次元空間。

後者は \(p\) 乗根からなる一次元空間であり、円分指標が作用する。

どちらも抽象的には一次元の \(\mathbb F_p\)-ベクトル空間じゃ。

だが、これだけでは、

\[ \det\rho_{E,p}=\chi_p \]

とは結論できない。

必要なのは、ガロア作用と可換する同型

\[ \boxed{ \bigwedge\nolimits^2 E[p]\simeq_{G_K}\mu_p } \]

じゃ。

そして、この同型を幾何学から供給するものこそ Weil 対である。

NOTE-018 は既に、この同型から行列式を導く側の証明を完成させている。

つまり現在の Frontier は非常に明確じゃ。

二つの一次元世界が単に同じ形であることではなく、同じガロア作用を保持して結び付くことを証明する。

### NOTE-021 の推奨目標

わっちは次の主目標を、Tate 加群より Weil 対の幾何学的構成に置く。

最終的に供給すべき定理は、既存 API を使えば次の形で書ける。

```
theorem exists_weilPairingData
    {K : Type*} [Field K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] :
    Nonempty (WeilPairingData E p) := by
  ...
```

これは目標形であり、まだ存在証明を実装したものではない。

実装の初手では、[模範解答の Weil 対構成](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_pairing_torsionBy.lean?utm_source=chatgpt.com) を参考に、まず楕円曲線の座標環の Dedekind 性、関数体、点による平行移動を整備する。

その後、`weilFun` に対応する有理関数と付値の関係から双加法性・交代性・ガロア同変性・非退化性を証明していく。

ここは大きな幾何学的仕事になるため、最初のアジャイルで `WeilPairingData` の完成まで強行する必要はない。まずその構成に本当に必要な幾何学的補題を、一つずつ Core に固定するのがよい。

この provider が完成すれば、NOTE-018 の条件付き定理に代入するだけで、

\[ \boxed{ S.\mathrm{residualDeterminantCharacter} =\chi_p } \]

を、Frey Source の実際の残余表現について無条件化できる。

## 総合評価

NOTE-020 まで来ると、ねじれ点群について次の区別が明確になった。

- 位数：すべての \(n>0\) について \(n^2\) と確定。
- 素数冪構造：各段で自由階数2と確定。
- 階層間の接続：倍写像の全射性・ガロア同変性と、非分裂性を確定。
- 塔全体の構造：互換的基底・Tate 加群は未確定。
- 円分体との接合：Weil 対の幾何学的存在が未確定。

今回の成果は、素数冪の階段を一段ずつ眺めるところから、どの段でも成立する同じ構造を証明する段階へ進んだことじゃ。

次は、その構造に円分体との対応を与えよう。

ねじれ点群が二次元であることは、既に確定した。今度は、その二次元空間の面積に相当する行列式が、なぜ円分指標に一致するのかを幾何学から証明する。

ここから先は、まさしく異なる数学分野の Core を結ぶ仕事になるのぅ。🐺🍎