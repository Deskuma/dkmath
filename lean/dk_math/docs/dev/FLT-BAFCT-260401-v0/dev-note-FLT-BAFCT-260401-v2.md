# developer note: FLT-BAFCT-260401-v2

cid: 69ccb052-e100-83a6-bdc6-3372db93e5b0

わっちなら、ここからは **もう `FringeDescent` を触らぬ**。
次は、上流 2 核を順に供給して、せっかく完成した terminal-case の spine に実弾を流し込む。いまの戦況では、それが最も自然じゃ。`FringeDescent` は sorry-free になり、残敵は `PrimeGe5BranchAPrimitivePacketDescentStrongTarget` と `PrimeGe5BranchACyclotomicExistenceTarget` の concrete 実装へ整理されたのだからの。

## 1. 最優先. `StrongTarget` を concrete 化する

これを先にやる。理由は単純で、`hStrong` が入れば

$$
pkt'.z < z \quad\text{と}\quad \neg p \mid pkt'.t
$$

が同時に落ちてきて、terminal-case 側の測度降下が **完全に生きる** からじゃ。しかも、これは新しい数論を足すより「既存 concrete descent が本来持っていた性質を型に戻す」作業に近い。`StrongTarget` は今回まさにそのために新設された。

やることは 3 つで十分じゃ。

1. 既存の concrete provider のうち、いちばん近い 1 本を選ぶ。
2. その theorem の strengthen 版を作り、
   $$
   \exists pkt',\; pkt'.z < z \land \neg p \mid pkt'.t
   $$
   を返すようにする。
3. 既に作ってある
   `primeGe5BranchAPrimitivePacketDescent_of_strong`
   で弱化版へ戻す。

ここで大事なのは、**最初から全 concrete theorem を強化しない** ことじゃ。
1 本でよい。まず 1 本通して `hStrong` の供給源を得る。それで `FringeDescent` 下流が動くかを見る。

## 2. 第二優先. `CyclotomicExistenceTarget` を concrete 化する

次はこれじゃ。
こちらは `branchA_restoreWitness_of_smallerPacket` の Step 1 の供給源で、

$$
q' \mid (z'^p-y'^p),\qquad q' \nmid (z'-y')
$$

を与える distinguished prime existence の核じゃ。今回の差分では、ここから因数分解して (q' \mid GN) を取り出し、さらに `primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default` へ流す構造まで既に固めておる。つまり、残りは **本当に existence だけ** じゃ。

だから次の実装は、新しい大定理を書くのではなく、

* Zsigmondy / cyclotomic 系の既存存在定理を 1 本選ぶ
* `PrimeGe5BranchACyclotomicExistenceTarget` の期待する形へ薄く包む
* `branchA_restoreWitness_of_smallerPacket` に差し込む

これでよい。

ここは、restore 完了レポートでも「Branch A の矛盾には witness (q) の deeper structure が必要」と整理されておる本丸寄りの箇所じゃ。だからこそ、**新しい route を作るより既存存在定理との接続に徹する** のが賢い。

## 3. その次. `FringeContradiction` を実弾化する

`hStrong` と `hEx` が concrete で入れば、`branchAFringeContradiction_of_descent` は abstract theorem ではなく、**実際に使える contradiction theorem** になる。すると、最初に立てた terminal-case 設計どおり、

$$
\texttt{BranchAFringeContradictionTarget}\\
\to
\texttt{BranchAContradictionWithWitnessSourceTarget}\\
\to
\texttt{PrimeGe5BranchAPrimitiveRestoreContradictionTarget}\\
\to
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}
$$

へ機械的に流せる。これはもう設計段階から見えていた勝ち筋じゃ。

## 4. 今はやらない方がよいこと

ここで横道へ入ると戦線が散る。
いまは次をやらぬ方がよい。

* `FringeDescent` の再整理
* packet 型そのものの再改造
* LPS / PowerSwap / CosmicFormula 側の別件作業
* `BranchA.lean` の別の `sorry` を先に殴ること

なぜなら、いまの勝ち筋は **upstream 2 核の concrete 供給** に絞れておるからじゃ。そこを外すと、また霧の中へ戻る。`terminal case 用の新ファイル設計` でも、真に要る追加層は smaller packet / smaller bundle の再構成だと整理済みじゃ。いまはまさにその supply 側を埋める局面じゃよ。

## 5. 実務順に言い直すと

わっちなら、次の 4 手で行く。

## 5.1. `StrongTarget` の最初の concrete provider を 1 本だけ作る

`FringeDescent` に `hStrong` を流せるようにする。

## 5.2. `CyclotomicExistenceTarget` の最初の concrete provider を 1 本だけ作る

`branchA_restoreWitness_of_smallerPacket` を fully concrete にする。

## 5.3. `branchAFringeContradiction_of_descent` へ concrete `hStrong`, `hEx` を入れて実動確認

ここで terminal-case 路線が本当に動くか見る。

## 5.4. 既存 bridge 群へ流し込んで primitive 側 contradiction を閉じる

このとき初めて、残る `BranchA.lean` 側の設計マーカーをどう処理するか判断する。

## 6. 一言でまとめると

$$
\boxed{
\text{次は abstract spine の完成ではなく、upstream 供給源の concrete 化じゃ}
}
$$

じゃ。
つまり、「証明を書く」より「供給線を通す」。
これが今の最善手じゃよ。
