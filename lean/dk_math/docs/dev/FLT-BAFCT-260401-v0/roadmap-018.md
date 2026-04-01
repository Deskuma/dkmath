# roadmap-018: `GNReducedGapTarget` 攻略のための局所戦を切り出して潰す段階へのロードマップ

うむ、ここからの道はかなりはっきりしておる。
わっちの判定では、**もう大改造の段は終わった**。次は

$$
\boxed{
\text{GNReducedGapTarget を攻略するための局所戦を、順番に切り出して潰す段}
}
$$

じゃ。

いま既に、

* `GNReducedGapTarget` が **GN native open kernel** として定義され、
* `GNReducedGap ↔ PthRootReduced ↔ PthRoot` の橋が no-sorry で通り、
* `GNReducedGap → RestoreFromArithmeticStrong → StrongProvider → FringeDescentToRefuter` の canonical route まで通っておる。ゆえに、**mainline の骨格は完成済み** と見てよい。

さらに一つ前の段で、`PthRootTarget` の reduced 形と (z^p) の q-adic 展開

$$
z^p = q^p \cdot p^p \cdot (t s')^p + y^p
$$

まで no-sorry で固定できておるから、GN 側へ降ろす前提整備も済んでおる。

## 1. . 現在地

いまの真の open kernel は、これ 1 本じゃ。

$$
\boxed{
\exists g',\quad g' \cdot GN_p(g',y) = p^p \cdot (t s')^p
}
$$

これは report にある通り、Cosmic Formula の核恒等式

$$
(g'+y)^p = g' \cdot GN_p(g',y) + y^p
$$

を使って `PthRootReducedTarget` と等価になっておる。つまり、**もはや “p 乗根を取る問題” ではなく、“新しい gap (g') を作って Body を一致させる問題”** に見えている。ここが実に大きい。

## 2. . ロードマップの本筋

わっちなら、ここからは 4 段で進む。

## 2.1. Phase A. GNReducedGapTarget をさらに 2 層へ割る

いきなり

$$
\exists g',\quad g' \cdot GN_p(g',y) = p^p (t s')^p
$$

を殴るのは、まだ少し重い。
だからまず、これを **q-adic 剥離層** と **GN 局所存在層** に分ける。

### A1. q-adic 剥離層

目標は、

* \(GN_p(z-y,y) = p \cdot s^p\)
* \(s = q \cdot s'\)
* \(q \nmid (z-y)\)

から、**\(q^p\) が GN 側にだけ集中している** ことを theorem 群として固定することじゃ。

ここで狙うのは existence ではなく、**必要条件の列挙** じゃ。
つまり「もし新しい \(g'\) があるなら、こういう valuation / congruence を満たす」をまず no-sorry で積む。

### A2. GN 局所存在層

その次に、関数

$$
F(g) := g \cdot GN_p(g,y) - p^p (t s')^p
$$

を置き、\(F(g)=0\) の局所解 \(g'\) を狙う。
ここで初めて q-adic/Hensel 風の補題を使うが、対象は **GN-native function** \(F\) じゃ。
これなら GN が家主、Hensel は補助、という現在の戦略と綺麗に一致する。

## 2.2. Phase B. “一般 Hensel” ではなく “特殊形専用 Hensel” を作る

ここは重要じゃ。
一般の Hensel 定理をそのまま Lean に持ち込むのではなく、今欲しい特殊形だけを theorem 化する。

狙うべき形は、たとえば

$$
F(g_0) \equiv 0 \pmod q,
\qquad
F'(g_0) \not\equiv 0 \pmod q
$$

から、ある \(g'\) が存在して

$$
F(g') = 0
$$

となる、という **Branch A 専用の局所持ち上げ補題** じゃ。
この段では full Kummer/Hensel は要らぬ。前段の feasibility 判定でも、full (\mathbb{Z}[\zeta_p]) route は重すぎ、q-adic/Hensel はまだ補題群が育てば戦える、という整理になっておる。

## 2.3. Phase C. GN mainline を正式な mainline として固定する

この段は実装というより設計の固定じゃ。
いま既に GN native canonical path があるので、

$$
\texttt{GNReducedGapTarget}
\to
\texttt{PthRootReducedTarget}
\to
\texttt{PthRootTarget}
\to
\cdots
$$

を **docstring と wrapper theorem 名で正式に本命 route と宣言** してよい。
一方、contradiction route は fallback / oracle として残す。
この分離は、すでに chain が no-sorry で確立している今こそやる価値がある。

## 2.4. Phase D. 攻略不能判定のための出口も先に用意する

ここも賢い手じゃ。
もし GN 局所存在がどうしても閉じなければ、そこで初めて

* stronger q-adic target
* localized Hensel target
* true Kummer target

へ段階的に昇格する。
だがこの昇格は **失敗してから** でよい。
今はまだ、GN-native 局所戦で十分に勝負になる局面じゃ。

## 3. . 具体的な次作業

ぬしが次にすぐ書けるものを、順に並べるとこうじゃ。

## 3.1. `GNReducedGapTarget` の必要条件補題

たとえば

* `q^p ∣ GN p (z-y) y`
* `q ∤ (z-y)`
* `v_q (GN p (z-y) y) = p * v_q(s)`
* reduced RHS の valuation 形

この辺を **独立補題群** に切り出す。
これは existence を問わないので、通しやすい。

## 3.2. `GNReducedGapLocalTarget`

名前は仮でもよいが、

$$
\exists g',\quad F(g')=0
$$

の前に、

$$
\exists g_0,\quad F(g_0)\equiv 0 \pmod q
$$

のような **mod (q) 近似解 target** を先に置く。
ここで Hensel 的 route の入口を固定する。

## 3.3. `GNReducedGap_of_localLift`

局所近似解と derivative 条件から GNReducedGap を出す specialized bridge を作る。
これができれば、最後の門は完全に q-adic/Hensel の局所補題だけへ押し込める。

## 3.4. その後でだけ `GNReducedGapTarget` 本体へ戻る

ここまで来ると、本体は “大定理” ではなく “橋の合成” になる。
それが理想じゃ。

## 4. . 何を後回しにするか

ここでは、やらぬことも大事じゃ。

* full \(\mathbb{Z}[\zeta_p]\) Kummer route
* 一般 Hensel theorem のフル形式化
* `PthRootTarget` を再び家主に戻すこと

これは今は不要じゃ。
今の地形では、GN が家主、q-adic/Hensel は補助兵でよい。これが今回の差分の最大価値だったのだからの。

## 5. . まとめ

ここからのロードマップを一行で言えば、

$$
\boxed{
\text{GNReducedGapTarget を “存在定理” として殴る前に、q-adic 必要条件と局所近似解を定理化して包囲せよ}
}
$$

じゃ。

順番に言い直せば、

1. GN 側への \(q^p\) 集中を定理化
2. \(F(g)=g,GN_p(g,y)-p^p(ts')^p\) の mod \(q\) 近似解を探す
3. 特殊形専用の Hensel 風 bridge を作る
4. それを GNReducedGapTarget に接続
5. GN mainline を正式 mainline として固定

これが、いま最も project らしく、しかも勝率の高い道筋じゃよ。 🍎
