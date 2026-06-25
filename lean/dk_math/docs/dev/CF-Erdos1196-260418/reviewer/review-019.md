# review-019: `ABC038` 接続の中間 landing point として `rad(c)` budget を theorem 名で固定したこと

## 1. 総評

今回は、かなり良い進み方じゃ。
前回までに見えていた

\[
\text{channelCount}
\;\to\;
\mathrm{ABC.rad}(c)
\;\to\;
\mathrm{ABC.rad}(u*v)
\;\to\;
\mathrm{TailBound}
\]

という流れのうち、いちばん不安定だった真ん中を、いったん二段に分けて整理し直したのが本体じゃ。具体的には `ABC038Bridge.lean` に

- `targetRadTailBound_of_channelCount_tail`
- `tailBound_of_targetRadTail_transport`
- `quality_le_of_not_bad_with_targetRadTail_transport`

を入れ、`twoTail c ≤ (2 ^ channelCount)^γ` からまず

\[
\text{twoTail}(c) \le (\mathrm{rad}(c))^\gamma
\]

へ landing して、その後に必要なら

\[
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
\]

で運ぶ形へ変えた。これは実装としても数学としても、かなり筋が良い整理じゃ。

## 2. 状況分析

前回の review で見えていたことは、divisibility route

\[
c \mid u*v
\Rightarrow
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
\]

は theorem としては正しいが、自然な `u+v=c` の nontrivial triple にそのまま刺さるには細すぎる、という点じゃった。今回の差分は、その観察を正面から受けて、「ならば `rad(u*v)` に一気に飛ぶ前に、まず `rad(c)` 側に一回着地しよう」という input-refactoring route を入れたものじゃ。これは方針転換ではなく、前回の分析を踏まえた自然な深化と見てよい。

しかも `tailBound_of_channelCount_tail_transport` も、直接 `2 ^ channelCount` から `rad(u*v)` へ飛ばす形をやめて、

\[
2^{\text{channelCount}}
\;\to\;
\mathrm{rad}(c)
\;\to\;
\mathrm{rad}(u*v)
\]

という二段構成で読むように整理されておる。ここが大事じゃ。
いったん中間 landing point を theorem 名で固定したことで、今後 transport route を差し替えたり比較したりしやすくなった。これは橋の設計として、とてもよい。

## 3. 数学的解説

今回の数学的な核心は、`PrimitiveWitnessFamily` から得られる counting spine を

\[
2^{F.\text{channelCount}} \le \mathrm{ABC.rad}(c)
\]

としてまず target 自身の radical 下界に読む、という一点じゃ。
前回までは、この下界を「quality 側が欲しい `rad(u*v)` 入力へどう運ぶか」が主役になっておった。じゃが今回は、その前に

\[
\text{twoTail}(c) \le (2^{F.\text{channelCount}})^\gamma
\]

という budget を

\[
\text{twoTail}(c) \le (\mathrm{rad}(c))^\gamma
\]

へ持ち上げる定理 `targetRadTailBound_of_channelCount_tail` を作った。これで counting 情報そのものが、target \(c\) の内部にある radical 量へ直結するようになったわけじゃ。

この一手は大きい。
なぜなら、`rad(c)` は `c` 自身の情報なので、`u*v` のような外部入力へ運ぶ前に、まず target の内部で budget を完結できるからじゃ。数学的に言えば、これは

\[
\text{external transport}
\]

より前に

\[
\text{intrinsic target budget}
\]

を確立した、ということになる。
この順のほうが自然じゃし、後でどの transport が使えるかを比較する時にも有利じゃ。

さらに `tailBound_of_targetRadTail_transport` を別定理として切り出したのも非常に良い。ここでは

\[
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
\]

という transport 仮定と

\[
\text{twoTail}(c) \le (\mathrm{rad}(c))^\gamma
\]

という target-rad budget とを分離して扱っておる。すると `TailBound` への変換は、もはや counting spine 特有の話ではなく、

\[
\text{target-rad budget}
\;\to\;
\text{TailBound}
\]

という独立した bridge になる。これは theorem の責務分離としてとても美しい。

## 4. 具体例の意味

`ABC038BridgeExamples.lean` の更新も良い。
`6^3 - 5^3 = 91` の two-channel sample について、前回は直接 `TailBound 1 91 1 91` を読んでいたが、今回はまず

\[
\text{twoTail}(91) \le (\mathrm{rad}(91))^1
\]

を example として置き、そのあとで `tailBound_of_targetRadTail_transport` に流して `TailBound 1 91 1 91` を読む形に変えておる。
これで、今どこまでが counting spine の出力で、どこからが transport の役目かが、具体例の上でもはっきり見えるようになった。これは教育的にも実装的にも良い改善じゃ。

## 5. 今回閉じたもの

今回閉じたのは、

**`ABC038` 接続の中間 landing point として `rad(c)` budget を theorem 名で固定したこと**

じゃ。
前回までは

\[
\text{channelCount}
\;\to\;
\mathrm{ABC.rad}(u*v)
\]

へ直接運ぶ話が前面に出ていた。今回はそれを

\[
\text{channelCount}
\;\to\;
\mathrm{ABC.rad}(c)
\;\to\;
\mathrm{ABC.rad}(u*v)
\]

へ分解した。
この分解により、今後は

- divisibility route
- generic transport route
- さらに別の transport route

を、同じ `rad(c)` budget を起点に比較できる。ここが今回の本当の収穫じゃ。

## 6. 良い点

今回の差分で特に良いのは、橋の中間点を発見したというより、**中間点を theorem として固定した** ことじゃ。
設計だけでなく、実際に Lean 上で

\[
\text{targetRadTailBound\_of\_channelCount\_tail}
\]

という名が立ったので、今後の議論が一気にしやすくなる。

もう一つ良いのは、失敗事例が無かったことじゃ。
前回の divisibility route ではいくつか型や sample の不安定さが出ておったが、今回は追加した theorem 群がそのまま build を通っておる。これは設計の方向がかなり自然だった証でもある。

## 7. 留意点

ただし、ここでまだ本丸に届いたわけではない。
今回の target-rad route は、`rad(c)` 側の budget を整理しただけであって、`ABC038` の full quality sample を自然に閉じるところまでは行っておらぬ。差分報告にもある通り、依然として課題は

\[
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
\]

を自然な `u+v=c` triple でどう供給するか、あるいは逆に `rad(c)` 側の budget のまま quality 側へ入る route がないか、の比較じゃ。ここはまだ未決着じゃな。

## 8. 現況の位置づけ

いまの spine は、かなり整理されてきておる。

\[
\text{channelCount}
\;\to\;
2^{\text{channelCount}}
\;\to\;
\mathrm{ABC.rad}(c)
\;\to\;
\text{twoTail}(c) \le (\mathrm{rad}(c))^\gamma
\]

ここまでは bridge 側の “自然な出力” として見えるようになった。
その先に

\[
\mathrm{rad}(c) \le \mathrm{rad}(u*v)
\]

を足せば `TailBound` へ入り、さらに quality へ行ける。
つまり今は、quality 本体へ入る直前で必要な構造が、一段ずつ分離されて見える段階じゃ。これは非常に良い状態じゃよ。

## 9. 次の一手

わっちの見立てでは、次は二択ではなく優先順位が少し見えた。

まず第一に、**`rad(c)` budget のまま quality 側へどこまで入れるか** を洗うほうがよい。
理由は、divisibility route が自然 triple には細すぎる可能性が高いからじゃ。いま `rad(c)` 側に綺麗な landing point が出来たのだから、これをわざわざ `rad(u*v)` に運ばずに済む route があるかどうかを先に見るべきじゃろう。

第二に、それでも `ABC038` 本体が `rad(u*v)` 固定でしか動かぬなら、その時点で初めて自然な transport 供給元を本格的に探る。順序としてはこのほうが筋が良い。

## 10. 最終判断

これは **かなり良い差分** じゃ。
前回の divisibility route を補強するというより、むしろその限界を踏まえて、より自然な中間 landing point を theorem 名で確立した。これにより `ABC038` 接続は

\[
\text{counting spine}
\;\to\;
\text{target-rad budget}
\;\to\;
\text{TailBound}
\]

という二段構成として読めるようになった。

ひとことで言えば、
**橋の先端を無理に本丸へ押し込むのではなく、前庭の中に足場を組み直した回** じゃ。
この組み直しは、かなり賢いぞい。
