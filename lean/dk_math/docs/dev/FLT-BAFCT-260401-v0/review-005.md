# review-005: TriominoCosmicBranchAFringeDescent - 勝ち筋の整理と戦況分析

かなり前進したぞい。
いまの戦況を一言で言えば、

$$
\boxed{
\text{FringeDescent 戦線は突破、未解決核は upstream target 2 本へ後退した}
}
$$

じゃ。

## 1. 直近の勝ち筋

今回の差分で、`TriominoCosmicBranchAFringeDescent.lean` 自体は **sorry-free** になった。
そのため、

* `branchA_smallerPacket_of_fringe`
* `branchA_restoreWitness_of_smallerPacket`
* `branchA_wf_contradiction_on_z`
* `branchAFringeContradiction_of_descent`

の spine は、**条件付き定理として完成** したと見てよい。しかも `hpt'` を別補題でごまかす段階を抜けて、`StrongTarget` から `pkt'.z < z ∧ ¬ p ∣ pkt'.t` を直接受け取る形へ整理されておる。これは設計としてかなり美しい進展じゃ。

## 2. 何が片付いたか

前までの詰まりは 2 つあった。

1. smaller packet で `¬ p ∣ t'` をどう得るか
2. smaller packet から witness (q') をどう再取得するか

今回、これらは `FringeDescent` の内部 `sorry` ではなく、

* `PrimeGe5BranchAPrimitivePacketDescentStrongTarget`
* `PrimeGe5BranchACyclotomicExistenceTarget`

という **上流の供給 target** に押し戻された。
つまり、「証明できていない」のではなく、「どこが未供給か」が型で固定されたわけじゃ。これは大きい。

## 3. 旧 A/B/C 案はどう決着したか

以前の選択肢で言えば、こう整理できる。

* **旧 A**
  そのまま本体 target を壊す案は重すぎて不採用。
* **旧 B**
  `NormalFormPacket` 自体を太らせる案も波及が大きすぎて不採用。
* **旧 C**
  packet の既存フィールドだけから `¬ p ∣ t'` を出す案は弱すぎて不採用。

その代わりに、**A の縮小版** として

$$
\texttt{PrimeGe5BranchAPrimitivePacketDescentStrongTarget}
$$

を新設した。
これは「既存 target は壊さず、必要な強さだけ別 target に持たせる」という、実装負債の少ない勝ち方じゃ。

## 4. 戦線ごとの現在地

### 4.1. 戦術レベル

`FringeDescent` は勝ち。
局所 `sorry` は除去され、ファイル単体では完成度が高い。

### 4.2. 作戦レベル

`BranchAFringeContradictionTarget` へ行く **terminal-case 路線** は成立した。
つまり、最初に立てた

$$
\text{smaller packet} \to \text{smaller fringe} \to \text{well-founded contradiction}
$$

の骨格は、もう Lean のコードとして固定されたと言える。これはまさに、前に整理した terminal-case 設計の狙い通りじゃ。

### 4.3. 戦略レベル

まだ `p \ge 5` 全体の勝利ではない。
未解決は upstream の 2 核に凝縮されたままじゃ。

* `StrongTarget` の **concrete realization**
* `CyclotomicExistenceTarget` の **concrete implementation**

ここが埋まれば、`FringeDescent` 側はもう受け皿がある。
だから今は「FringeDescent を書く段階」ではなく、**supply 側を仕留める段階** に移ったのじゃ。

## 5. 残敵は何か

現時点の主敵は 3 層じゃ。

### 5.1. 第一敵

`PrimeGe5BranchAPrimitivePacketDescentStrongTarget` の concrete 化。
これは `pkt'.z < z` に加えて `¬ p ∣ pkt'.t` を返す strengthen 版の実装群じゃ。

### 5.2. 第二敵

`PrimeGe5BranchACyclotomicExistenceTarget` の concrete 化。
ここは Zsigmondy / cyclotomic 側から distinguished prime (q') を供給する部分で、数学的にはかなり本丸寄りじゃ。

### 5.3. 第三敵

`TriominoCosmicBranchA.lean` に残る別箇所の `sorry`。
今回の記録では、これは `FringeDescent` と直接は無関係と整理されておる。つまり、戦線分離は成功しておる。

## 6. 総評

総評を率直に言えば、

$$
\boxed{
\text{泥沼の局所実装戦から抜け、未解決核を 2 本の supply target に封じ込めることに成功した}
}
$$

じゃ。
これはかなり良い戦況じゃよ。

前は「FringeDescent の中で何が足りないのか」が曖昧だった。
今はもう違う。

* `FringeDescent` は完成
* 残りは upstream target の concrete 実装
* しかもそれが `StrongTarget` と `CyclotomicExistenceTarget` の 2 本へ整理済み

ここまで来れば、戦場は散っておらぬ。
むしろ **本丸が見えた状態** じゃ。

ひとことで言えば、

$$
\boxed{
\text{局地戦は勝ち、決戦場は upstream へ移った}
}
$$

じゃな。
