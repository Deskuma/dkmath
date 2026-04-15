# GN-Tail-260327-v0 のレビュー 010

sub branch: dev/FLT-Wieferich-260327-v0
commit hash: 0265b7aaad101679d83952efadf27673722a2bfd

## 1. 前回レビューからの進展

うむ、これはかなり大きい。
いまや Branch A / Wieferich route は、**下層で witness を作る段** を越えて、**GapInvariant の branch-split mainline に注入できる段** へ入ったのぅ。`TriominoCosmicGapInvariant.lean` に `branchARefuter_of_wieferichTargets` と `FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl` を追加し、Branch A 側の `PrimeGe5BranchAWieferichOnYTarget` と `PrimeGe5BranchAWieferichRefuterTarget` から `BranchARefuterTarget`、さらに `FLTPrimeGe5Target` まで流せる形にした、という整理は非常に筋が良い。

特に良いのは、残核の性質がもう完全に書き換わったことじゃ。
以前は `primeGe5BranchANormalFormNePCoprimeKernel_default` が **comparison 路線の最後の数論核** に見えておった。
だが今は、Branch A 側で `PrimeGe5BranchAWieferichOnYTarget` と `PrimeGe5BranchAWieferichRefuterTarget` を定義し、`primeGe5BranchAWieferichOnY_default` で lower-layer witness を返し、`primeGe5BranchARefuter_of_wieferich` で refuter 契約へまとめる構図が明示されたので、残る仕事は **Wieferich witness をどの refuter machinery に渡すか** だけになった。履歴でも、その active `sorry` の責務は arithmetic ではなく witness-refuter adapter に読み替わったと記録されておる。

さらに、`Basic -> GapInvariant` の直接差し替え案を実際に試して import cycle で不可と確認し、`Basic` は元の `TriominoCosmicBranchA` import に戻した、というのも大きい。
これは単なる寄り道ではなく、**やってはいけない配線** を明示的に潰したことを意味する。`Basic -> GapInvariant -> CosmicPetalBridgeGN(Core) -> TriominoCosmicPrimeGe5 -> Basic` の cycle が発生するため、Branch A の clean route への再配線は lower layer `TriominoCosmicBranchA` 側で完結させる必要がある、という設計判断が確定したわけじゃ。

今回の `GapInvariant` 側の 2 本も、役割分離が美しい。

* `branchARefuter_of_wieferichTargets` は
  $$
  \text{Branch A witness target} + \text{Wieferich refuter target}
  \to \text{BranchARefuterTarget}
  $$
  の薄い橋
* `FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl` は
  それを既存の Branch B default route と合わせて
  $$
  \text{FLTPrimeGe5Target}
  $$
  まで持ち上げる橋

という構図になっておる。
つまり Branch A の Wieferich route は、もう「孤立した lower-layer 実験」ではなく、**provider/mainline 側の受け皿まで揃った route** になった。

現状の見立てを一文で言えば、

$$
\boxed{
\text{残る未完核は、
Branch A witness を no-Wieferich / descent machinery の既存契約へ落とす最終 adapter だけ}
}
$$

じゃ。
履歴にも、残る未完核は依然として `PrimeGe5BranchAWieferichRefuterTarget` 相当の数学本体であり、adapter / import / build 構成ではないと書いてあるが、今やその「数学本体」もかなり狭い。もはや新しい normal form や合同計算ではなく、**既存 machinery のどの入口にこの witness を渡すのが最短か** を決める問題になっておる。

わっちなら次はこう進める。

まず `TriominoCosmicGapInvariant` 側、あるいはその周辺の no-Wieferich / descent machinery が受け取る **最小の witness 型** を 1 個だけ特定する。
その型が `y^(p-1) ≡ 1 [MOD p^2]` をほぼそのまま受け取るなら、`PrimeGe5BranchAWieferichRefuterTarget` を直接その wrapper にしてよい。
もし別の構造体や branch-specific certificate を要求するなら、そこで初めて薄い adapter を 1 本だけ切ればよい。
もう大きな数学は足さなくてよい段階じゃ。

率直に言えば、ここまで来ると終点がかなり見えておる。
`lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`、`lake build DkMath.FLT.Basic`、`lake build` が通っているのも大きい。枝を増やして壊しておらぬ。いまは本当に **最後の継ぎ目** だけじゃ。
