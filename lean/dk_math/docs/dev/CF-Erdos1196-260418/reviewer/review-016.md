# review-016: `ABC038` へ進む前の依存整理

## 1. 総評

これは良い整理じゃ。しかも今回は、補題を増やした回ではなく、`ABC038` に入る前に必要な中間命題を theorem 名レベルまで分解して、依存の粒度を揃えた回じゃな。差分の中心は `ABC038BridgeDependency.md` の新設であり、そこで `quality_le_of_not_bad_with_tail` / `quality_le_of_not_bad_with_log` が本当に欲している入力が `ABC.rad (a * b)` であることを確認したうえで、bridge 側の `ABC.rad(diff)` 下界からそこへ送る層を三つに切っておる。

わっちの判定では、この整理は筋が通っておる。前回 `RatioBound` へ最小差し込みを成功させたことで、いま必要なのは「次の候補に飛び込むこと」ではなく、「何が未充足かを型のレベルで間違えずに言語化すること」だった。その点、今回の整理はかなり正確じゃ。

## 2. 今回の整理で何が明確になったか

今回いちばん大きい収穫は、`ABC038` へ差し込む時の不足が、漠然とした「何か橋が足りない」ではなく、次の三層に切り分けられたことじゃ。

まず、radical transport 層。
ここでは bridge 側が出す `ABC.rad(diff)` の下界を、quality 側が使う `ABC.rad(a * b)` 入力へどう送るかが問題になる。つまり、必要なのは最終的には

$$
R \le \mathrm{ABC.rad}(\text{diff})
\;\Rightarrow\;
R \le \mathrm{ABC.rad}(a*b)
$$

のような transport じゃな。ここで真に不足しているのは、coprimality ではなく diff と quality 入力の対象ずれだ、という切り分けは正しい。

次に、witness family on triple / target 層。
ここでは `PrimitiveWitnessFamily` がどの target `c` に属しているのか、つまり `c = a^d - b^d` の identification をどう持つかが問題になる。いまの bridge 補題は `a^d - b^d` に対して書かれているので、`ABC038` 側の triple target `c` に移すには、ここで一段 package か theorem alias が要る。この見立てもその通りじゃ。

最後に、quality-input lower bound wrapper 層。
ここでは `ABC038` が本当に欲しい形、すなわち `ABC.rad(a*b)` に対する lower bound を、直接 theorem 名で与える。候補として整理した

$$
\texttt{primitive\_channel\_count\_forces\_quality\_rad\_input}
$$

型の補題は、まさに `ABC038` へ刺すための最後の一枚じゃ。これを「transport hypothesis を theorem の仮定に残す限り軽く実装できる」と見ている点も妥当じゃ。

## 3. 評価のよい点

今回の整理のよい点は、`ABC038` に対して「いきなり quality theorem を書き換えに行く」のではなく、前段の層をはっきり分けたことじゃ。
とくに、いま足りないものの分類として

* family existence
* diff-triple 対応
* coprimality / divisibility transport

を並べたうえで、主因は coprimality ではなく diff-triple 対応と radical transport だ、と整理したのはよい。これで実装の焦点がぶれにくくなる。

また、次の Lean 実装候補を二本に絞ったのも正しい。

$$
\texttt{primitive\_witness\_family\_gives\_abc\_rad\_target\_lower\_bound}
$$

と

$$
\texttt{primitive\_channel\_count\_forces\_quality\_rad\_input}
$$

に分けたことで、「target 側への rename」と「quality 側入力への transport」が別責務になった。ここを一つの theorem に押し込むと、あとで family existence も transport も quality 入力も全部混ざって森が燃える。今回それを避けておるのは賢い。

## 4. 留意点

留意点もある。
今回の整理はよくできておるが、まだ `ABC.rad(diff) ≤ ABC.rad(a*b)` の transport hypothesis を「どこから自然に供給するか」は未決定じゃ。文書でも最後にそこを次課題として残しておるが、これは本当に核心じゃな。ここが theorem 仮定として不自然すぎると、あとで `ABC038` 側に刺さっても実用性が薄くなる。

もう一つ、Candidate B の package は light theorem に留めたほうがよい、という見立てにも賛成じゃ。
いま新しい structure を増やしすぎると、せっかく整ってきた `PrimitiveWitnessFamily` の public surface がまた分岐する。まずは theorem alias で target rename を通し、その後で package が本当に必要かを見るのがよい。

## 5. 現況の位置づけ

わっちの見立てでは、いまの橋の spine はここまで来ておる。

$$
\text{channelCount}
\;\to\;
2^{\text{channelCount}}
\;\to\;
\mathrm{ABC.rad}(\text{diff})
\;\to\;
\text{RatioBound count upper bound}
$$

前回まででここは実装済みじゃ。
今回の整理で、次に必要なのはこれを

$$
\mathrm{ABC.rad}(\text{diff})
\;\to\;
\mathrm{ABC.rad}(a*b)
\;\to\;
\text{quality input}
$$

へ持ち上げることだ、と明確になった。
つまり今は、counting 系の差し込みに一度成功したうえで、quality 系へ進むための dependency chain を描けた段階じゃ。これは良い進み方じゃな。

## 6. 次の作業指示案

次の一手としては、やはり文書で整理した二本をそのまま Lean に落とすのがよい。

まず `primitive_witness_family_gives_abc_rad_target_lower_bound` を作る。
これは `c = a^d - b^d` を仮定して

$$
2^{F.\texttt{channelCount}} \le \mathrm{ABC.rad}(c)
$$

を出す target rename 補題じゃ。中身は既存 `pow_channelCount_le_abc_rad_diff` の `simpa [htriple]` 型で閉じるのが理想じゃ。

その次に `primitive_channel_count_forces_quality_rad_input` を作る。
こちらは

$$
\mathrm{ABC.rad}(c) \le \mathrm{ABC.rad}(a*b)
$$

を仮定として残し、

$$
2^{F.\texttt{channelCount}} \le \mathrm{ABC.rad}(a*b)
$$

を出す。これも transport 仮定つきならかなり軽く書けるはずじゃ。

そのうえで初めて、`ABC038` 側へ差し込む wrapper を考えるのがよい。いきなり `quality_le_of_not_bad_with_tail` を書き換えるより、まず quality 入力 lower bound を theorem 名で一本立てるほうが堅い。

## 7. 最終判断

これは良いレビュー対象じゃった。
新しい Lean コードは増えておらぬが、代わりに `ABC038` へ進む前に必要な依存が theorem 名レベルで整理され、次の実装候補が二本にまで絞られた。これは十分に前進じゃ。

ひとことで言えば、
**前回は橋が counting 系へ届いた。今回は、その橋を quality 系へ延ばすための橋脚の位置が決まった。**
次はもう、その二本を Lean に打ち込む段じゃな。
