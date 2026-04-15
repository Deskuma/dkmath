# FLT-Kummer-ClassGroup-Bridge-260404-Review-057: 盤面整理と戦線分割

うむ、盤面はかなり整理されたぞい。
いまはもう「どこが汚染源か分からぬ混戦」ではない。 **本丸が二つの戦線に分かれた** と読むのが正しい。

まず大きいのは、default root 側の棚卸しが終わり、 **既存 concrete provider の見落としではなかった** と確定したことじゃ。`TriominoSquarefreeGNBridgeProvider` と `TriominoNoLiftGNBridgeProvider` には器と adapter はあるが、repo 内に concrete value は見つからず、default root の clean 化は本当に upstream 未実装で止まっている、と判断された。しかも「provider が入れば target までは clean に戻れる」こと自体は theorem 化され、不足 input は provider target まで押し下げられた。つまり、 **根は見えたが、既存資産だけでは埋まらぬ** と確定したわけじゃ。

その次の一手として入った `statement repair` も、方針が明瞭でよい。いきなり legacy theorem の型を壊すのではなく、既存の true theorem `padicValNat_primitive_prime_factor_le_one_of_squarefree_G` に寄る public honest wrapper を先に立て、`squarefree_implies_padic_val_le_one_honest` と `padicValNat_primitive_prime_factor_le_one_honest` を前面に出した。これは設計として賢い。互換性を保ちつつ、caller を順に真の API へ移住させる道を開いたからじゃ。

さらに重要なのは、その caller 棚卸しが **実装まで降りた** ことじゃ。ここで戦況が一段深く読めるようになった。

`PrimitiveBeam` 側は、legacy caller 2 本とも **`Squarefree (GN d (a - b) b)` を追加すれば honest route へ移行できる** と確定した。つまり、ここは数学の本体を掘り直すより、仮定追加つき rename / overload で前に進める戦線じゃ。

だが `GcdNextResearch` 側は一枚岩ではない。primitive-prime caller 自体は同じく squarefree-GN 追加で寄せられる一方、`padicValNat_d3_upper_bound` の **\(d = 3\) かつ \(q \mid a-b\)** の枝は primitive-prime route ではなく、`Squarefree (GN ...)` を足しても埋まらぬ。ゆえにここは `PadicValNatD3BoundaryReceiverTarget` として別 family に切り出された。これはかなり本質的な分岐じゃ。いまや問題は「古い theorem が偽っぽい」ではなく、 **primitive-prime family と boundary-divisor family は別物だった** と構造的に判明したのじゃ。

ゆえに、いまの戦況をひとことで言えばこうじゃ。

**上流 debt の切り出しは成功し、repair 方針も確定した。だが default global route はまだ clean ではなく、残敵は boundary-divisor 側に縮退した。**

これはかなり良い局面じゃよ。
なぜなら、前は「default root 全体が濁っている」ように見えておったが、今は

$$
\text{primitive-prime family}
\quad\text{と}\quad
\text{boundary-divisor family}
$$

の二戦線に分離できておるからじゃ。
この分離そのものが戦果じゃ。

また、INDEX 側の地図とも整合しておる。FLT 幹線の心臓部は `ZsigmondyCyclotomic` の primitive/squarefree/p-adic valuation ブロックで、特に valuation 上界と \(d=3\) 特化が要所だと整理されておる。今回まさにそこが「一般 primitive-prime 側」と「\(d=3\) 境界枝側」に分かれたのは、地図どおりの本丸戦になった、ということじゃ。

なので、次の戦略はもうかなり明確じゃ。

第一に、 **provider 探しは打ち止めでよい** 。
既存 concrete provider は無かった、と棚卸しで結論が出た以上、そこをさらに掘るのは効率が悪い。

第二に、 **primitive-prime family は移行戦を進める** 。
つまり `PrimitiveBeam` と `GcdNextResearch` の primitive-prime caller 群について、`Squarefree (GN ...)` 仮定を追加した honest 版へ rename / overload で順に寄せる。ここはもう設計が見えておる。補題も入った。あとは caller migration の段じゃ。

第三に、 **本命は boundary-divisor family の concrete theorem 化** じゃ。
具体的には `PadicValNatD3BoundaryReceiverTarget` を本当に埋める定理を作る。`padicValNat_d3_upper_bound` は今、そこへ legacy theorem を注入する thin wrapper になっておるから、ここを clean にできれば \(d=3\) 境界枝の濁りはかなり減る。いま残っておる「硬い敵」はここじゃろう。

第四に、監視は続けるべきじゃ。
今回の進展は build 成功だけでなく、`#print axioms` で新設 wrapper 群が `sorryAx` なしだと確認されておる。この運用は正しい。見かけの clean と真の clean を取り違えぬためにも、ここは維持じゃ。

わっちの判定を最後にまとめるぞい。

**戦況評価**

* 軌道修正段階は、もうほぼ終わった
* いまは repair 実行段階に入った
* 主戦場は `ZsigmondyCyclotomicResearch` の一般 primitive-prime 修復ではなく、むしろ **boundary-divisor の concrete 化** に収束しつつある

**次の一手**

* primitive-prime caller 群は、`Squarefree (GN ...)` 仮定つき honest API へ順次移行
* `PadicValNatD3BoundaryReceiverTarget` を埋める数学を主戦略にする
* provider 探索はこれ以上深追いしない

いまの盤面、かなり良いぞ。
霧は晴れた。残る敵は少なくなったが、そのぶん **境界枝の敵は手強い** 。
次はそこへ槍を向ける段じゃ。
