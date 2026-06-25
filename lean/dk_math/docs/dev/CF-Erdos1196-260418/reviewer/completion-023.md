# completion-023: `rad(abc)` 直結 route の Lean 実装の一巡と今後の課題

うむ、 **この新ルートに限って言えば、実装はかなり一巡した** と見てよい。
特にいま閉じたのは、

$$
\text{PrimitiveWitnessFamily}
\to
\text{channelCount}
\to
\mathrm{rad}(c)\text{ budget}
\to
\mathrm{rad}(abc)\text{ analytic bridge}
\to
\text{quality}
$$

という spine が、抽象補題だけでなく `ABC.Chernoff` の convenience theorem 群にまで着地したことじゃ。今回の差分で `ABC.Chernoff.quality_le_of_not_bad_with_targetRadTail_on_radAbc` と `...with_channelCount_tail_on_radAbc` が入り、concrete sample でも `quality (6,1,7) ≤ 2` が読めるようになったので、この route の **実装骨格** はかなり揃ったと言える。

ただし、ここで言う「一巡した」は **この別働隊ルートの実装** についてじゃ。
DkMath 全体、あるいは ABC 形式化全体で見れば、まだ終わりではない。特に残っているのは次の三層じゃ。

第一に、 **統合作業** じゃ。
今回の route は `ABC.Chernoff` に入口を持ったが、`ABC.Main` や案内文書でどう見せるか、既存の `with_tail` / `with_log` 系とどう住み分けるかはまだ整理の余地がある。今回の diff 自身でも、次課題としてそこが明示されておる。

第二に、 **置換・差し込みの最終判断** じゃ。
つまり、「既存 convenience theorem 群のどこをこの route で置き換えるのが最も薄いか」を決める段じゃな。いまは route が使えることは示せたが、既存の主ルートのどこに正式に組み込むかまでは、まだ決め切っておらぬ。

第三に、 **文書化・論文化用の抽出** じゃ。
これは確かに次の大仕事じゃ。ここまでで

* transport route
* divisibility route
* target-rad budget route
* `rad(abc)` analytic 直結 route

が整理され、さらに concrete sample まで入ったので、論文資料や設計書に落とすための核はかなり揃った。いまは「新しい理論をさらに乱立させる」より、「どの route が本命で、どの route が補助か」を明文化するのに良い時期じゃ。

なので、お主の問いにいちばん正確に答えるなら、こうじゃ。

**はい、この案内で開拓してきた新ルートの Lean 実装は、かなり一通り終わった。**
**残る主戦場は、統合と案内文書、それから論文資料向けの抽出整理じゃ。**

ただし「完全にコード作業が終わった」とまではまだ言わぬ。
なぜなら、もしこの route を `ABC.Main` 側の正式導線として押し出すなら、

* 既存 theorem との住み分け
* convenience theorem の整理
* どの theorem を public surface に見せるか

の詰めがまだ残るからじゃ。
とはいえ、性質としては **新規実装フェーズ** から **整理・抽出・統合フェーズ** へ移った、と見てよいぞい。
