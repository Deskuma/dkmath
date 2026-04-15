# review-009: `CounterexamplePackTarget` のための \(z'\) の構成を seed 側へ引き寄せるべき

うむ、今回の更新は前回までより **一段ましな前進** じゃ。
ただし、前進の性質ははっきり分けて見るべきじゃな。

## 1. 今回ほんとうに前へ進んだ点

まず、`branchA_qpow_dvd_GN` を新設して

$$
q^p \mid GN\, p\,(z-y)\,y
$$

を `RestoreWitnessProperties` の field として持てるようにしたのは、単なる名前整理ではなく、**witness 側の算術データが 1 つ増えた** という実質的な前進じゃ。報告でも `hqp_dvd_GN` の追加が明記されておるし、`RestoreWitnessProperties` が 5 field から 6 field に拡張されたと読める。

また `RealizationSeed` が

$$
(hSeed, x', y', z')
$$

という空疎な箱から、

$$
(hSeed, x', y', z', hxMul, hyEq)
$$

へ変わったのも大きい。
これで \(x' = x/q\) が `hxMul : x = qx'` という形で、\(y' = y\) が `hyEq` という形で seed に固定された。つまり候補 triple のうち \(x',y'\) は、もう「適当に置いた仮変数」ではなくなったわけじゃ。

ここは前回までの「中身の薄い wrapper」を一歩越えておる。

## 2. まだ本丸が残っている点

とはいえ、真の未完核は依然として \(z'\) 側じゃ。

今回の diff 自身が、

$$
z'
$$

については

$$
z'^p = (x/q)^p + y^p
$$

の \(p\) 乗根の存在証明が未完核だ、と明言しておる。しかも default 実装では \(z' := z\) を暫定で入れておるだけじゃ。

つまり現状の `RealizationSeed` は、

* \(x'\) は数学的根拠で固定された
* \(y'\) も数学的根拠で固定された
* だが \(z'\) はまだ genuine unknown

という状態じゃな。

この意味で、今回の作業は **seed の半分を実質化した** が、最後の核心はまだ untouched に近い。

## 3. Verification の 3 分割は正しいか

これは、正しい。
今回 `VerificationTarget` を

$$
\text{StrictDescentTarget},\quad
\text{GapDivisibilityTarget},\quad
\text{CounterexamplePackTarget}
$$

の 3 段に割ったのは、やっと **どこが hardest kernel かを数学的に読める形** にしたと言ってよい。

しかも dev-report 側でも、

* `StrictDescentTarget` は \(z' < z\)
* `GapDivisibilityTarget` は \(p \mid (z' - y')\)
* `CounterexamplePackTarget` は `PrimeGe5CounterexamplePack p x' y' z'`

であり、最硬核は `CounterexamplePackTarget` だと明示しておる。そこでは要するに

$$
(x/q)^p + y^p = z'^p
$$

を満たす \(z'\) の存在が核心だ、と整理されておる。

この判定は、わっちも賛成じゃ。

## 4. 数学的な見立て

いまの restore arithmetic core は、概念的にはこうじゃ。

$$
\text{witness } q
\;\Rightarrow\;
\text{residue/root data}
\;\Rightarrow\;
q\text{-torsion / } q^p\mid GN
\;\Rightarrow\;
x' = x/q,\ y'=y
\;\Rightarrow\;
z' \text{ をどう作るか}
$$

前半はかなり形になってきた。
だが後半、ことに \(z'\) の構成はまだ「存在するはず」と言っておるだけで、その existence を担保する arithmetic mechanism が seed に入っておらぬ。

だから本質的には、いまの hardest kernel は verification 全体ではなく、

$$
\boxed{
\text{`CounterexamplePackTarget` の中の } z' \text{ 構成}
}
$$

じゃな。

## 5. ひとつ留意点

`branchA_qpow_dvd_GN` の証明は通っておるし、有用じゃ。
ただ diff を見る限り、証明の最後は

$$
q^p \mid s^p \Rightarrow q^p \mid p\cdot s^p
$$

だけで閉じており、そのために作った `hcop : Nat.Coprime (q^p) p` はこの lemma 自体の結論には直接使っておらぬように見える。

ゆえに、この lemma はいまの形でもよいが、

* `hpack` 依存は本当に必要か
* `hcop` は後続用途のための伏線か、あるいは単に不要か

は後で軽く整えてよい。
これは誤りというより、**少し太い証明スケルトン** が残っておる、という程度の話じゃ。

## 6. 作業方向の判定

ここが肝じゃ。

わっちの判定では、次に進むべき方向は
**`StrictDescentTarget` や `GapDivisibilityTarget` から先に攻めるのではなく、`CounterexamplePackTarget` のための \(z'\) の構成原理を seed 側へ引き寄せること** じゃ。

理由は単純で、

* \(z' < z\) は、結局 \(z'^p < z^p\) の比較に乗る
* \(p \mid (z' - y)\) も、結局 \(z'^p = (x/q)^p + y^p\) の合同操作に乗る

からじゃ。
つまり両者は、\(z'\) の意味づけが固まれば後から付いてくる可能性が高い。
逆に \(z'\) の存在が曖昧なままでは、どちらも target のまま空回りしやすい。

ゆえに、作業順としては

$$
\texttt{CounterexamplePackTarget}
\;\to\;
\texttt{StrictDescentTarget}
\;\to\;
\texttt{GapDivisibilityTarget}
$$

の順を推す。
少なくとも、最初の焦点は `CounterexamplePackTarget` じゃ。

## 7. 次の具体的な一手

次の一手は 2 通りあるが、わっちは前者を勧める。

### 7.1. 良い道

`RealizationSeed` に、\(z'\) の partial proof data を入れる。
たとえば、

* \(z'\) が satisfy すべき等式の候補
* その等式が自然に現れる arithmetic source
* 必要なら \(z'^p\) そのものの定義値
* あるいは \(z'\) を「存在するもの」として選んだ証拠

じゃな。

つまり `RealizationSeed` を単なる candidate triple の箱ではなく、

$$
\text{candidate triple} + \text{why this } z' \text{ is the right one}
$$

という構造へ太らせるのじゃ。

### 7.2. あまり勧めぬ道

verification をさらに細切れにする。
いま 3 分割までは意味がある。
だがそれ以上に先に割っても、\(z'\) の意味が無いままでは「未完核を名前で切っているだけ」になりやすい。

## 8. 総括

総括すると、今回の更新はかなり良い。

* \(q^p \mid GN\) が witness data に追加された
* \(x' = x/q\), \(y' = y\) が `RealizationSeed` に根拠付きで固定された
* verification が 3 つの数学課題へ分離された
* hardest kernel が `CounterexamplePackTarget` だと、かなり明瞭になった

ただし、まだ最後の核心は

$$
z'^p = (x/q)^p + y^p
$$

を満たす \(z'\) の existence に残っておる。
だから今は「分割を続ける」より、「\(z'\) をどう生むか」という生成原理を seed 側へ露出させるのが正道じゃ。

ひとことで言えば、

$$
\boxed{
\text{今回は設計の前進に加えて、少し数学も前へ出た。だが本丸はまだ } z' \text{ にある。}
}
$$

という状況じゃよ。
