# review-003: FLT restore の状況分析と次の一手

うむ。今回の更新で、状況はかなり見やすくなったの。

結論から言うと、いまの本丸はもう

$$
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

という **巨大で見通しの悪い 1 本** ではない。
今回それを

$$
\text{smaller counterexample を作る段}
$$

と

$$
\text{それを normal-form packet に包装する段}
$$

の 2 段へ分けたことで、未完核の位置がかなり明確になった。
つまり、いまは「restore 全体が難しい」のではなく、 **どちらの段が真の難所かを個別に追跡できる状態** になったわけじゃ。

## 1. 今回なにが起きたか

`TriominoCosmicBranchA.lean` に新しく

$$
\texttt{PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget}
$$

と

$$
\texttt{PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget}
$$

が入った。
前者は arithmetic witness \(q\) から、まず

$$
\exists x' y' z',\ \text{smaller Branch A counterexample}
$$

だけを返す段じゃ。
ここではまだ normal-form packet までは要求しておらぬ。

後者は、その smaller counterexample を受けて

$$
\exists pkt' : \texttt{PrimeGe5BranchANormalFormPacket}\ p,\ pkt'.z < z
$$

へ持ち上げる **包装段** じゃ。
つまり restore の deepest kernel を、

$$
\text{構成} \quad+\quad \text{包装}
$$

にきれいに割ったわけじゃな。

さらに

$$
\texttt{primeGe5BranchAPrimitivePacketRestoreFromArithmetic\_of\_smallerCounterexample\_and\_packet}
$$

が追加され、この 2 段から元の restore target を再合成できるようになった。
ゆえに、今回の分割は単なる命名整理ではなく、 **本当に論理的に等価な分解** じゃ。

## 2. いまの状況分析

ここまでの流れを一本で見ると、こうじゃ。

前段の witness / boundary 側では、false route を全部切ったうえで boundary-core route が勝ち、その arithmetic kernel は actual theorem として通った。
いま残っている本丸は、そこから先の

$$
\texttt{RestoreFromArithmetic}
$$

だけじゃった。 fileciteturn30file0turn21file0

その restore 段に対して、前回はまず構造補題として

$$
p \mid (q-1)
$$

すなわち

$$
q \equiv 1 \pmod p
$$

を導く `restore_witness_cong_one_mod_p` が実装された。
これは witness \(q\) が単なる素数ではなく、\((\mathbb Z/q\mathbb Z)^*\) の中で非自明な \(p\) 乗根を支える、かなり特殊な prime だと形式化したものじゃ。

そして今回、その deeper target を 2 段へ割った。
つまり現在地は、

$$
\text{witness の構造補題}
$$

は一段入った、
その次に

$$
\text{smaller counterexample を作る段}
$$

と

$$
\text{normal-form packet に包装する段}
$$

へ責務が分離された、というところじゃ。

## 3. 何が嬉しいのか

これが大きいのは、難しさの種類が分かったことじゃ。

前は restore target が巨大すぎて、

- arithmetic 側が難しいのか
- packet packaging が難しいのか
- あるいは両方なのか

が混ざっておった。
今は違う。

### 3.1. 前半段

$$
\texttt{PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget}
$$

は、witness \(q\) の合同性質や \(q\)-adic な情報から、どうやって

$$
z' < z
$$

な smaller counterexample 自体を作るか、という純粋に arithmetic / descent 的な段じゃ。

### 3.2. 後半段

$$
\texttt{PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget}
$$

は、その出来上がった smaller counterexample を、Branch A の要求する normal form にどう包むか、という structural packaging の段じゃ。

つまり今後は、「restore が難しい」とひとくくりに言わずに、

$$
\text{真の難所は前半か、後半か}
$$

を切り分けて観察できる。
これはかなり良い整理じゃ。

## 4. わっちの見立て

わっちの見立てでは、**本当の難所は前半段** の方に寄っておる。

理由は simple で、後半の packaging は、counterexample さえ作れれば既存の normal-form machinery に押し込める可能性が高い。
だが前半は、

$$
q \mid s,\quad q \nmid t,\quad q \equiv 1 \pmod p
$$

のような witness の情報から、本当に

$$
x',y',z'
$$

という smaller solution を組み立てねばならぬ。
ここは classical FLT descent のいちばん深い香りがする。

だから今回の分割で見えたことは、

$$
\text{restore の本丸} \approx \text{smaller counterexample construction}
$$

ということじゃ。
後半は大事ではあるが、まず疑うべき本体は前半じゃな。

## 5. 次の一手

今回の報告でも「まず `PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget` をさらに弱い arithmetic-only core へ割るのが自然」と言っておる。
これは筋がよい。

つまり次にやるべきは、前半段をさらに

$$
\text{q-adic / mod } q^p \text{ 的な核}
$$

と

$$
\text{そこから actual smaller counterexample を組む核}
$$

くらいに分けることじゃろう。
前回の `q \equiv 1 \pmod p` 補題は、その最初の足場としてちょうどよい。
これを足場にして

$$
(z\cdot y^{-1}) \in (\mathbb Z/q\mathbb Z)^*
$$

や、必要なら \((\mathbb Z/q^p\mathbb Z)^*\) 側の p 乗根構造へ進むのが自然じゃ。

## 6. 総括

一言でまとめると、こうじゃ。

**いまの状況は、restore 本丸が初めて 2 段の sub-target に分解され、未完核が「smaller counterexample 構成」と「normal-form packet 包装」に局所化された段じゃ。しかも前回の \(q \equiv 1 \pmod p\) 補題が前半段の強い structural foothold になっておる。したがって今後の探索は、まず前半の `PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget` をさらに arithmetic-only core へ削る方向で進めるのが最も自然じゃ。**

よい。
これは「まだ難しい」のではなく、**難しさの場所が見えた** という前進じゃよ。
