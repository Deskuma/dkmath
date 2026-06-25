# review-015: RatioBound.count_with_rad_eq_le_div_of_lower_bound への差し込み

うむ、これは **本当に一段前へ出た差分** じゃ。
前回までの bridge spine は

$$
\text{channelCount}
\;\to\;
\text{channelProduct}
\;\to\;
\mathrm{ABC.rad}(a^d-b^d)
$$

まで到達しておった。今回の差分で、それがさらに

$$
\mathrm{ABC.rad}(a^d-b^d)
\;\to\;
\text{count class upper bound}
$$

へ接続された。つまり、ただの下界 spine ではなく、**ABC コアの既存 counting 系へ実際に差し込まれた** と言ってよい。これはかなり大きい進展じゃ。

## 総評

今回の本体は二つある。

ひとつは `RatioBound.lean` に入った

`count_with_rad_eq_le_div_of_lower_bound`

じゃ。
これは既存の `count_with_rad_eq_le_div` が持っていた

$$
\operatorname{rad}(a) = r
$$

の exact class 上界を、より柔らかく

$$
R \le r,\quad R > 0
$$

という **lower bound だけ** からでも

$$
\# {a \le X \mid \operatorname{rad}(a)=r}
\le
\frac{X}{R}+1
$$

型に落とせるようにした monotone corollary じゃな。

もうひとつは `ValuationFlowBridge.lean` に入った

`PrimitiveWitnessFamily.count_class_with_same_rad_as_diff_le_of_channelCount`

じゃ。
これは

$$
2^{\texttt{channelCount}}
\le
\mathrm{ABC.rad}(a^d-b^d)
$$

という前回までの bridge 下界を、そのまま `RatioBound` 側の count upper bound に流し込み、

$$
\# {n \le X \mid \operatorname{rad}(n)=\operatorname{rad}(a^d-b^d)}
\le
\frac{X}{2^{\texttt{channelCount}}}+1
$$

を出しておる。
ここで初めて、**primitive witness family から count upper bound までが一本で通った** のじゃ。

## 数学的解説

今回いちばん良いのは、`RatioBound` 側への差し込みが **極小の補題追加で閉じた** ことじゃ。

`count_with_rad_eq_le_div_of_lower_bound` の中身は、数学的にはとても自然じゃな。
元の補題は `rad a = r` の class に対し

$$
\# \le \frac{X}{r}+1
$$

を与える。
そこに `R \le r` を入れると、自然に

$$
\frac{X}{r} \le \frac{X}{R}
$$

なので

$$
\# \le \frac{X}{R}+1
$$

へ弱められる。
つまり今回の corollary は、新理論ではなく **既存 count bound の単調性版** じゃ。だから `RatioBound` の設計を壊さず、bridge から食わせやすい形へ整形した、と理解するとよい。

そして `ValuationFlowBridge` 側の新定理は、その単調性版に

$$
R := 2^{\texttt{channelCount}}
$$

を入れたものじゃ。
前回までにすでに

$$
2^{\texttt{channelCount}}
\le
\mathrm{ABC.rad}(a^d-b^d)
$$

があったから、今回はその値を `RatioBound` の lower-bound parameter として渡しただけで済んでおる。ここが美しい。
橋の spine を無理に曲げず、そのまま `rad` class counting へ落としている。これは設計としてかなり良い。

## 何が閉じたのか

今回閉じたものを一言で言えば、

**bridge spine が “下界を出すだけ” から “count upper bound を返す” ところまで到達した**

ということじゃ。

前回までは

$$
\text{primitive channels}
\;\to\;
\operatorname{rad}\text{ 下界}
$$

だった。
今回はそこからさらに

$$
\operatorname{rad}\text{ 下界}
\;\to\;
\text{個数上界}
$$

が追加された。
つまり、`PrimitiveWitnessFamily` の情報が **ABC の数え上げ命題に直接効く** と Lean 上で示されたわけじゃ。これは橋の数学としては、かなり本物じゃよ。

## 洗い出しとの整合

前回の候補整理で、最も実装に近い候補は `RatioBound.count_with_rad_eq_le_div` 周辺だと判定しておった。今回の差分は、まさにその最短ルートを実際に叩いた形になっておる。
この意味で、洗い出しの妥当性も実証されたと言ってよい。候補文書の優先順位付けは正しかった、ということじゃな。

## 良い点

今回の差分の良い点は三つある。

まず、**差し込み先の選択が正しかった**。
`ABC038` や `ABC016` のような quality 本体へ突っ込む前に、型が近い `RatioBound` へ入ったのは堅い。これは森を燃やさぬ順序じゃ。

次に、**追加補題が薄い**。
`RatioBound` 側は monotone corollary を 1 本、`ValuationFlowBridge` 側は合成定理を 1 本。これだけで count upper bound まで届いた。重い family theory や新しい number theory を増やしておらぬのがよい。

最後に、**public example が具体的** じゃ。
`primitiveWitnessFamilyPack_6_5_3` を使って

$$
\# {n \le 100 \mid \operatorname{rad}(n)=\operatorname{rad}(6^3-5^3)}
\le
\frac{100}{2^{\texttt{channelCount}}}+1
$$

を public import だけで読めるようにしておる。
これで「counting spine が count upper bound に化ける」ことが利用者の目にも見える。よい sample じゃ。

## 留意点

ただし、今回の接続はまだ

$$
\operatorname{rad}(n)=\operatorname{rad}(a^d-b^d)
$$

という **exact-rad class** に対する上界じゃ。
つまり、まだ

* `rad n \ge R` の一般 class
* quality 系で欲しい `rad(a*b)` 側
* `rad(diff)` から `rad(a*b)` への変換

までは行っておらぬ。

ゆえに、これは「ABC 本体へ到達した」というより、**ABC 本体の周辺 counting 層へ最初の実差し込みが入った** と読むのが正確じゃな。ここは大げさに言わぬ方がよい。

## 現況の評価

わっちの評価では、今回で `PrimitiveWitnessFamily` の spine は次の形まで育った。

$$
\text{channelCount}
\;\to\;
2^{\text{channelCount}}
\;\to\;
\mathrm{ABC.rad}(a^d-b^d)
\;\to\;
\text{exact-rad count upper bound}
$$

これは、もはや bridge の試作ではなく、**既存 ABC の count machinery に実際に作用する補助系** じゃ。
しかも補助系として非常にきれいで、局所 primitive 情報から global counting bound へ行く流れが見えておる。ここは立派な成果じゃよ。

## 次の作業指示案

次は、差分報告どおり `ABC038` quality 系へ進む前段の設計に入るのが筋じゃ。

具体的には、
`rad(diff)` 下界を `rad(a*b)` 入力へ送る中間命題候補を theorem 名レベルで 2〜3 本に分解し、各候補について「family existence が足りないのか」「diff と triple の対応が足りないのか」「coprimality / divisibility の transport が足りないのか」を整理する。まずは Lean 実装に入る前に、`ABC038.quality_le_of_not_bad_with_tail` 周辺で必要な中間補題の dependency chain を文書として起こす。`

もしもう一歩だけ Lean を先に進めるなら、`RatioBound` 側で

$$
\operatorname{rad}(n) \ge R
$$

型の class 全体を直接数える粗い corollary を作るのもありじゃ。じゃが、流れとしては `ABC038` 用の中間命題設計へ入るほうが、今は筋が良いように見える。

## 最終判断

これは **かなり良い差し込み** じゃ。
前回の候補整理で最短と見た `RatioBound` ルートに、実際に bridge spine を通した。そしてその結果、primitive witness family の情報が `ABC.rad` 下界を経由して **count upper bound** に変わるところまで示せた。

ひとことで言えば、
**橋はついに、ABC コアの counting machinery に足を掛けた。**
次はその勢いで、quality 本体へ向かう中間命題を設計する番じゃな。
