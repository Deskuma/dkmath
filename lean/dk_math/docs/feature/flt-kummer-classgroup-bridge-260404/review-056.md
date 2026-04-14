# FLT-Kummer-Bridge-Review-056: 軌道修正はほぼ完了、次は default root の concrete provider 棚卸しと `ZsigmondyCyclotomicResearch` の statement repair へ

うむ。結論から言うと、 **軌道修正は半分ではなく、かなり本質的な部分まで完了した** 。
ただし、 **「全体が clean になった」わけではない** 。
いま完了したのは、

* branch-B 文脈で `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget` を既存 no-sorry route から埋め戻せること
* Kummer first-case 側で `hNoLift` を捨てていた配線ミスを直し、non-liftable route を実際に使うよう戻したこと
* その修正が build と `#print axioms` 監視で通っていること

じゃ。逆に、 **default global root の clean 化** はまだ未完じゃ。そこは報告でも次の課題として明示されておる。

戦況を整理すると、前回までは「specialized route でも実は upstream dirty root に引き戻されるのではないか」が最大の不安だった。今回の差分で、それはかなり解消された。`TriominoPrimitivePrimeFactorPadicValNatLeOneTarget` が `..._of_squarefreeGNBridge`、`..._of_noLiftGNBridge`、`..._of_nonLiftableGNBridge` から no-sorry で埋められるようになったので、少なくとも **current branch-B / non-default / first-case-specialized 方面では、`padicValNat_primitive_prime_factor_le_one` が必須ではない** と確定したわけじゃ。これは単なる化粧直しではなく、依存の根を 1 本減らした、れっきとした前進じゃよ。

しかも、わっちらが怪しいと見ておった first-case wrapper の配線も、ちゃんと直っておる。`cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable` は、もう `_hNoLift` を捨てて default route に落とす形ではなく、`qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable` を経由して non-liftable 仮定つき route を実際に使う形へ修正された。さらに `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit` も、その repaired first-case route を使うよう揃えられておる。つまり、 **軌道修正そのものは成功** じゃ。前に指摘した「配線ミス」は、いまはもう「現行コードの構造的欠陥」ではなく、 **修正済みの履歴事項** になった。

では、「軌道修正は完了したか」に対する、より厳密な返答はどうなるか。
わっちならこう答える。

**局所戦線では完了。全域戦線では未完。**

局所戦線というのは、いま問題にしていた Kummer class-group bridge の first-case / branch-B / specialized receiver 群のことじゃ。この部分は、もう「default dirty bridge に戻ってしまう」状態からは復帰できておる。
しかし全域戦線、すなわち **default root を完全 clean 化する concrete provider の確保** はまだ終わっておらぬ。報告でも、次は既存資産に concrete provider がまだあるか最後に棚卸しし、なければ `ZsigmondyCyclotomicResearch` の statement repair を主戦略に移す、と明言されておる。ゆえに「軌道修正完了＝完全勝利」とはまだ言えんのじゃ。

ここで地図全体の見方も大事じゃ。INDEX の整理では、FLT 幹線の本丸は `ZsigmondyCyclotomic` を中心とする原始素因子・p-adic valuation ブロックにあり、完成度が FLT の進捗を決めるとされておる。つまり今回の残課題が `ZsigmondyCyclotomicResearch` 側へ収束していくのは自然で、戦線が散らかったのではなく、 **本丸の位置がはっきりした** と読むべきじゃ。

次の戦略は、もうかなり明白じゃ。

第一に、 **default root の concrete provider 棚卸し** を最後にやる。これは「まだ既存資産に clean provider が埋もれていないか」の確認じゃ。今回 specialized 側は救えたので、ここで奇跡的に provider が見つかれば、default root 側まで clean 化できる。

第二に、棚卸しで空振りなら、 **`ZsigmondyCyclotomicResearch` の statement repair へ即座に主戦線を移す** 。わっちならここでもう迷わぬ。理由は簡単で、specialized 側の救出は終わったからじゃ。これ以上 local wrapper を磨いても、default root は clean にならぬ。ならば upstream theorem の命題修正、つまり honest な仮定と honest な結論へ立て直す段に移るのが筋じゃ。

第三に、監視を継続する。今回 `RegularPrimeRoute.lean` へ `#print axioms` 監視が足されたのは地味に大きい。これで再び「direct では綺麗に見えるが、transitive に汚れていた」という取り違えを起こしにくくなった。つまり、今後は前よりずっと **盤面の読み間違いが減る** 。

まとめるぞい。

いまの戦況は **復帰成功** じゃ。
ただしそれは **specialized route の復帰成功** であって、 **default global root の制圧完了** ではない。

ゆえに判定はこうじゃ。

$$
\text{軌道修正} = \text{ほぼ完了}
$$

ただし

$$
\text{戦役全体} = \text{まだ継続中}
$$

次の一手は、 **concrete provider の最終棚卸しを短く済ませ、無ければ即 `ZsigmondyCyclotomicResearch` の statement repair に主力転換** 。
わっちなら、もうそこへ槍を向けるの。
