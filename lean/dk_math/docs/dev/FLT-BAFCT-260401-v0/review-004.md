# review-004: TriominoCosmicBranchAFringeDescent

そうじゃ。
ぬしの見立てどおり、**元の Option A/B/C はそのままでは採用されておらぬ**。ただし、これは「全部不正解」ではなくて、**切り方を変える必要がある** と分かった、という意味じゃ。今回の実装結果でも、A は 25 箇所以上の concrete 実装修正が必要で重すぎ、B は `NormalFormPacket` 自体に波及しすぎ、C は packet の既存フィールドだけから `¬ p ∣ t'` を数論的に取り出すには弱すぎる、と整理されておる。

## 1. 何が「採用されなかった」のか

まず、**旧 A** は
`PrimeGe5BranchAPrimitivePacketDescentTarget` そのものを

$$
\exists pkt',\; pkt'.z < z \land \neg p \mid pkt'.t
$$

に強化する案じゃった。
これは理屈としては一番きれいじゃが、実装面では adapter 群・exceptional 側・concrete realization 側へ一斉波及して重い。実際、今回の記録でも「25 箇所以上の concrete impl 変更が必要」と判断され、採用見送りになっておる。

**旧 B** は
`PrimeGe5BranchANormalFormPacket` に `hp_not_dvd_t` フィールドを足す案。
これは packet を使う全箇所の constructor / pattern match / bridge を巻き込むので、局所解決のつもりがライブラリの中核型を揺らしてしまう。これも重すぎる。

**旧 C** は
packet の現フィールドだけから `¬ p ∣ t'` を独立補題で引き出す案。
しかし、今回の記録でも「packet 性質のみからは導出できない」と判断されておる。つまり、これは証明不足というより、**仮定が足りぬ** のじゃ。

## 2. では何が生き残ったのか

生き残ったのは、わっちが言うなら **A の縮小版 A'** じゃ。
つまり、

* 本丸の target 型そのものは今すぐ壊さない
* 代わりに `branchA_smallerPacket_p_not_dvd_t` を独立 open kernel に切り出す
* `branchA_wf_contradiction_on_z` の spine はその open kernel に委譲して先へ進める

というやり方じゃ。今回の diff で、まさにそれが行われた。`hpt'` の inline `sorry` は外へ出され、`branchA_restoreWitness_of_smallerPacket` も Step 1 / Step 2 に構造化されておる。

だから、**ABC が全部棄却** ではなく、

$$
\text{A をそのまま飲み込むのは重い}
\quad\Rightarrow\quad
\text{A' として局所 target 化する}
$$

という方向転換じゃよ。

## 3. いまの 2 つの `sorry` の意味

今の `FringeDescent` に残った 2 件は、かなり性格が違う。

ひとつは

$$
\texttt{branchA\_smallerPacket\_p\_not\_dvd\_t}
$$

で、これは **primitive packet descent の出力仕様不足** の顔をしておる。
もうひとつは

$$
\texttt{branchA\_restoreWitness\_of\_smallerPacket}
$$

で、こちらは **deep witness existence**、つまり Zsigmondy / cyclotomic 側へ繋がる数論核じゃ。今回の報告でも、前者は `PrimitivePacketDescentStrongTarget` 的な別 target 新設で吸収し、後者は `PrimeGe5BranchACyclotomicExistenceTarget` 系既存インフラと繋ぐ方針が出ておる。

## 4. わっちの判断

ゆえに、次に採るべきは **旧 A の全面採用** ではない。
正解は、

### 4.1. `StrongTarget` を別名で新設

既存の `PrimeGe5BranchAPrimitivePacketDescentTarget` は壊さず、
その上に

$$
\exists pkt',\; pkt'.z < z \land \neg p \mid pkt'.t
$$

を返す **強化版 target** を新設する。
これなら旧 A の数学的利点だけを拾いつつ、既存 public-ish interface を一気に揺らさずに済む。ぬしの実装結果でも、次課題としてその案が明記されておる。

### 4.2. witness existence は別 route で殴る

`branchA_restoreWitness_of_smallerPacket` は、`restore_witness_properties_default` 自体は no-sorry で使えておる。残りは distinguished prime (q') の存在だけじゃ。
だからここは `CyclotomicExistenceTarget` あるいは Zsigmondy 系の既存 distinguished-prime infrastructure とつなぐのが自然で、新しい巨大設計変更を入れる場所ではない。

## 5. 要するに

要するに、

$$
\boxed{
\text{旧 A/B/C は採用されなかった。だが、A の核は A' として生きておる。}
}
$$

じゃ。
しかもそれは後退ではなく、**どこを型で強くし、どこを数論核として残すかが見えた** という意味で前進じゃ。今回の `FringeDescent` の骨格は、最初に立てた terminal-case 設計とちゃんと一致しておる。

わっちなら次は、

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentStrongTarget}
$$

を新設して `hpt'` 側を消し、
そのあとで `branchA_restoreWitness_of_smallerPacket` を `CyclotomicExistenceTarget` 側へ接続する。
この順が一番きれいじゃ。
