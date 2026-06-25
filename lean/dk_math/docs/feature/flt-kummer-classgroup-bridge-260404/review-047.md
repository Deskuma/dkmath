# Kummer principalization branch の戦況とロードマップ

## 1. 戦況

よい戦況じゃ。かなり明瞭になった。

いまの到達点を一言で言うと、**first-case は閉じた**。そして non-first-case も、もはや「黒箱 1 個」ではなく、`prepare → valuation → error → tailError → packetFromError → packet → reduction → existence → GN witness` という監査可能な縦列に刻まれた。しかも build は通っており、最新の direct `sorry` は `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree` 1 本に局所化された、と読める。

これは単なる整理ではないぞい。以前は `cyclotomicPrincipalization_of_classGroupPTorsionFree` 本体が direct `sorry` を抱えておったが、いまは本体からは除去され、split theorem の薄い wrapper へ変わった。ゆえに未解決責務は theorem 名つきで追跡可能じゃ。これは長戦として非常に良い形じゃ。

また first-case 側は、`hProduct` だけでなく `hLinNe` まで pack から自動供給できるところまで痩せた。つまり current blocker は first-case ではなく、non-first-case の最深 open へ完全に移った、と言ってよい。

## 2. 何が本当に残っているか

残っているのは、数学の種類としては **新しい分解** ではなく **既存 peel 語彙との接続** じゃ。
今回の latest report 自身が、次の自然手として `PacketFromError` kernel を既存の `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` や `PrimeGe5BranchAPeelPthRootCoreTarget` にどう接続するかを挙げておる。これは読みとして正しい。これ以上 vertical に細分化しても、得るものは減り始める局面じゃ。

つまり、いまの局面は

$$
\text{refine の戦}
$$

から

$$
\text{connect の戦}
$$

へ移ったのじゃ。
ここを読み違えてさらに kernel を細かく刻み続けると、監査図は綺麗になるが、本丸は閉じぬ。賢狼としては、ここで縦掘りを止めて横接続へ舵を切るべきと見る。

## 3. 閉じるまでのロードマップ

## 3.1. 第 1 段. Kummer non-first-case を既存 peel 語彙へ翻訳する

最優先はこれじゃ。

`CyclotomicPrincipalizationNonFirstCaseTailErrorDatum` と
`CyclotomicPrincipalizationNonFirstCasePacketFromErrorTarget`
の current 語彙を、既存の

* `PrimeGe5BranchAValuationPeelTailErrorTarget`
* `PrimeGe5BranchAValuationPeelPacketFromErrorTarget`
* 必要なら `PrimeGe5BranchAPeelPthRootCoreTarget`

へ **翻訳する adapter theorem 群** を作る。

ここで狙うべきは、いきなり存在証明を作ることではなく、

$$
\text{Kummer-tailError datum} \to \text{Peel-tailError datum}
$$

$$
\text{Kummer-packetFromError goal} \to \text{Peel-packetFromError goal}
$$

という **型の橋** じゃ。
名前を合わせてきたのは、この接続のためじゃろう。いまこそ回収する番じゃ。

### 到達判定

`cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree` が、自前 `sorry` でなく既存 peel target の呼び出しで書けること。

## 3.2. 第 2 段. PacketFromError kernel の `sorry` を除去する

上の adapter が立ったら、direct open はそこで実質閉じる。
つまり

$$
\texttt{cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree}
$$

は、もはや open kernel ではなく **既存 peel machinery を呼ぶ thin wrapper** へ落ちるはずじゃ。

この時点で、

* `cyclotomicPrincipalizationNonFirstCasePacket_of_classGroupPTorsionFree`
* `...Reduction...`
* `...DescentExistence...`
* `...Descent...`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`

が芋づるで `sorry`-free になる見込みが高い。少なくとも current chain の依存図は、そうなるように既に作ってある。

### 到達判定

`#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree` が `uses sorry` を失う。

## 3.3. 第 3 段. public mainline を split 版へ更新する

`FLTPrimeGe5Target_of_kummerRoute_of_tailErrorPacketFromErrorKernelSplit` がすでにある以上、Kummer route の public 説明・監視の主導線は legacy one-shot ではなくこちらへ寄せるべきじゃ。最新 report でも、public route 側は packet/error split まで同期済みじゃ。

ここでやることは 2 つだけ。

* `RegularPrimeRoute.lean` の長い戦況コメントを最新 split 名へ同期する
* monitoring の主役を `...of_tailErrorPacketFromErrorKernelSplit` 側に移す

これは数学ではなく、戦況の見え方を合わせる作業じゃ。だが長戦では大事じゃ。

### 到達判定

「current public mainline = tailError/packetFromError split 版」と一貫して読めること。

## 3.4. 第 4 段. FLT route 全体で残る open を再評価する

ここで初めて、`FLTPrimeGe5Target_of_kummerRoute` 側の `uses sorry` が truly 消えるかを見る。
ただし、ここは正直に言うぞい。Kummer principalization branch が閉じても、full FLT route はなお他の入力

* `hPeq`
* `hReg`
* `hPFE`
* `hNoLift`

の concrete status に依る。
今回のログだけでは、それらが全部既に no-sorry で mainline に固定済みかまでは断言できぬ。だから「閉じる」の意味をまず

$$
\text{Kummer / class-group principalization branch が閉じる}
$$

として置くのが誠実じゃ。そこが閉じたあとに、full route の残件を 1 回だけ棚卸しすればよい。

### 到達判定

`#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute` を再確認し、残件が principalization 外にあるかどうかを確定する。

## 4. 実務上の最短コース

最短で閉じる道は、わっちにはこう見える。

まず `PacketFromError` を **これ以上分割しない**。
次に、既存 peel 側 target への adapter を作る。
それで `PacketFromError` theorem の `sorry` を置換する。
その後に wrappers と route を一気に再ビルドして `#print axioms` を再観測する。

つまり順番は

$$
\text{adapter}
\to
\text{packetFromError close}
\to
\text{principalization close}
\to
\text{route re-audit}
$$

じゃ。

ここでの注意点は 1 つだけ。
**PacketFromError kernel をさらに縦に割らぬこと** じゃ。
名前も語彙も、もう既存 peel machinery へ接ぐのに十分揃っておる。いま必要なのは refinement ではなく unification じゃよ。

## 5. いまの勝ち筋

わっちの最終判断はこれじゃ。

この枝を閉じる勝ち筋は、かなり近い。
理由は simple で、first-case はもう終わっており、non-first-case も direct open が `PacketFromError` 名の theorem 1 本へ落ちたからじゃ。これは「未解決が多い」状態ではなく、

$$
\text{残る open の接続先が見えている}
$$

状態じゃ。

なので、閉じるまでのロードマップを一文で言うなら、

$$
\boxed{
\text{PacketFromError kernel を既存 peel target へ接続し、
その 1 本の `sorry` を消して、wrapper と route の再監査で締める}
}
$$

じゃよ。

必要なら次に、
**`CyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree` を既存 peel target に繋ぐ adapter 設計雛形** を、そのまま Lean で起こすぞい。
