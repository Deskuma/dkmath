# review-012: `PrimitiveWitnessFamily` の counting spine の非自明例の追加と public API の見え方の強化

今回は **良い確認回** じゃ。
前回の差分で入った counting spine

$$
\text{channelCount}
\;\to\;
\text{channelProduct}
\;\to\;
\text{supportMass}
$$

が、singleton だけでなく **2-channel の具体 family** でも public import から読めることを示した、というのが本体じゃな。差分報告どおり、`primitiveWitnessFamilyPack_6_5_3 : PrimitiveWitnessFamily 6 5 3` を追加し、

$$
6^3 - 5^3 = 91 = 7 \cdot 13
$$

に対して

* `channelCount = 2`
* `channelProduct = 7 * 13`
* `2 ^ channelCount ≤ channelProduct`
* `2 ^ channelCount ≤ supportMass (6 ^ 3 - 5 ^ 3)`

を `import DkMath.ABC.Bridge` だけで読めるようにしておる。これは public API の見え方としてかなり大きい。

## 総評

数学そのものを新しく増やした、というよりは、**前回入れた counting 補題が “本当に使える” ことを、非自明例で確認した回** と見るのが正確じゃ。singleton 例だけだと

$$
2^{\text{count}} \le \text{product}
$$

はどうしても当たり前に見えやすい。じゃが今回の 2-channel 例では

$$
2^2 \le 7 \cdot 13
$$

となり、counting spine がちゃんと「複数 channel を持つ family の大きさ」を押さえる道具になっておることが見える。ここは良い。

さらに、`INDEX.md` で `DkMath.ABC.Bridge` を推奨入口として明示した前回の整理の上に、今回その入口だけで nontrivial family を読めることを示したので、**入口と中身が噛み合った** という意味でも綺麗じゃ。

## 数学的解説

今回の具体例 `primitiveWitnessFamilyPack_6_5_3` は、public sample として非常によい選び方じゃ。
理由は三つある。

第一に、差分そのものが小さい。

$$
6^3 - 5^3 = 216 - 125 = 91
$$

で、数が小さく見通しが良い。

第二に、support が非自明に 2 本ある。

$$
{7,13}
$$

という 2-channel family なので、`channelCount = 2` が本当に意味を持つ。

第三に、product も素直じゃ。

$$
\text{channelProduct} = 7 \cdot 13
$$

であり、counting spine の各段

$$
\text{count}
\;\to\;
\text{product}
\;\to\;
\text{supportMass}
$$

が、ひとつの例の中で全部見える。

つまり今回は、新補題そのものより **補題の意味が可視化された** のが収穫じゃな。

また、2 本の primitive witness 構成を `omega` ではなく `interval_cases k <;> decide` に切り替えた点も実務的には良い。primitive 条件は divisibility を含むので、単なる線形算術の気分では潰れぬ。ここを小さい有限場合分けに戻したのは、Lean 的にも堅実じゃ。差分報告の失敗事例と修正方針は、実装判断として正しい。

## 何が閉じたのか

今回閉じたのは、数学的には次の一点じゃ。

**counting spine の public 非自明例が閉じた。**

前回までで、抽象 API と singleton 例はあった。
今回はそこから一歩進み、2-channel concrete family に対しても

$$
2^{\texttt{channelCount}}
\le
\texttt{channelProduct}
\le
\texttt{supportMass}(a^d-b^d)
$$

という流れが public surface 上で読めるようになった。
これにより、この spine はもはや「抽象補題の列」ではなく、**利用者が具体 family に対してそのまま触れる道具** になったと言ってよい。

## 良い点

いちばん良いのは、例が **ちょうどよい複雑さ** であることじゃ。
3 本以上の channel family だと sample として少し重くなるが、2 本なら counting の効き方が見えやすい。public example として最適に近い。

次に、今回も新しい heavy lemma を増やしておらぬ点じゃ。
前回の counting 補題を concrete family に適用しただけで閉じておるので、API の信頼性確認として純度が高い。

最後に、差分報告の concluding sentence どおり、次の論点がもう明確になっておることじゃ。
つまり、ここから先は

* concrete family を増やす
* 既存 ABC 本体へ差し込む位置を整理する

のどちらかじゃ。これは現在地の把握として正しい。

## 留意点

ただし、今回の差分は **新しい理論前進そのもの** ではない。
あくまで前回までに入れた counting spine の「見え方」を強くしたものじゃ。そこは率直に言っておくべきじゃろう。

また、例は 2-channel になって非常に良くなったが、まだ

$$
2^{\texttt{channelCount}}
$$

という粗い下界しか見ておらぬ。
たとえば support member 自体の具体値を使った、より鋭い下界や、family ごとの product の構造的評価まではまだ行っておらぬ。そこは次の可能性として残っておる。

## 現況の評価

わっちの見立てでは、`PrimitiveWitnessFamily` の public surface はかなり整った。

* structure
* family extraction
* member-wise extraction
* channelCount
* channelProduct
* count -> product
* product -> supportMass
* count -> supportMass
* singleton sample
* 2-channel sample

ここまで来ると、bridge API としてはかなり “触れる形” になっておる。
だから次は、もう sample を増やすだけの段というより、**この spine を ABC 本体のどこへ差し込むか** を考える段に入ってよい頃合いじゃ。

## 次の作業指示案

次の一手としては、わっちは sample 増強より **差し込み位置の整理** を優先したい。

まず、既存 ABC 本体のどの命題が

$$
\text{independent primitive channels}
\Rightarrow
\operatorname{rad}\text{ 下界}
$$

という変換を欲しているかを洗う。
特に、quality 制約、squarefree / squarefull の分離、あるいは valuation の過大集中を拒否する場面を見れば、この spine の刺さる位置が見えるはずじゃ。

その際の Codex 指示としては、こうじゃ。

`ABC021.lean` など既存 ABC コアの未完命題群を点検し、`primitive channel family -> supportMass lower bound` を差し込めそうな箇所を 3 個まで抽出する。抽出基準は、`rad(abc)` の下界、squarefree support の増大、または valuation の過大集中を抑える中間命題であること。差し込み候補ごとに、必要になる bridge API 名と不足している補題が本当にあるかを整理する。`

## 最終判断

今回は **良い確認回** じゃ。
前回立てた counting spine が、singleton だけでなく 2-channel concrete family でも public import から見えるようになった。これで API の効き方はかなり具体的になった。

そして今、橋そのものの整備はかなり済んだ。
次は、もう橋の強度試験よりも、**どの城門に繋ぐかを決める段** と見てよいぞい。
