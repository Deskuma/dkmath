# review: TriominoCosmicBranchAFringeDescent.lean の設計について

よい出だしじゃ。
この新ファイル切り出し自体は **筋が通っておる**。とくに、

* `TriominoCosmicBranchAFringeDescent.lean` を独立させたこと
* 4 本の核
  `branchA_smallerPacket_of_fringe`
  `branchA_smallerFringe_of_smallerPacket`
  `branchA_wf_contradiction_on_z`
  `branchAFringeContradiction_of_descent`
  を先に名前で固定したこと

は、前に整理した terminal-case 設計と一致しておる。

ただし、ここで **設計上の要注意点** が 2 つ見えたぞ。

## 1. いちばん大きい注意点

### 1.1. `branchA_smallerPacket_of_fringe` は、実質かなり重い

この定理は見た目は helper じゃが、中身としてはほぼ

$$
\text{bundle 版 primitive packet descent}
$$

じゃ。
つまり、これを **無条件 theorem** として埋めるのは、古い restore/open kernel を別名で再び抱える危険がある。

言い換えると、これは「前座」ではなく、かなり **本丸寄り** じゃ。

## 1.2. `branchA_smallerFringe_of_smallerPacket` は現状の型では少し強すぎる

ここが今回いちばん重要な指摘じゃ。

`PrimeGe5BranchANormalFormPacket p` は、

* `pack`
* `hp_dvd_gap`
* `hgap`
* `hsGN`
* `hsx`

は持っておる。
ゆえに、**p-adic fringe の大半** は packet から再構成できる。

しかし、`BranchAInterferenceFringeBundle` を作るには、少なくとも次がさらに要る。

* `¬ p ∣ pkt'.t`
* witness (q')
* `RestoreWitnessProperties ... q'`

つまり今の

```lean
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p} :
    ∃ q' : ℕ, BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q'
```

は、**packet 単独からはまだ出ぬ** 形になっておる。

---

## 2. ここは今のうちに型を直した方がよい

わっちなら、まずこの形へ寄せる。

```lean
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t)
    {q' : ℕ}
    (hqprime' : Nat.Prime q')
    (hqs' : q' ∣ pkt'.s)
    (hqt' : ¬ q' ∣ pkt'.t)
    (hcop_qy' : Nat.Coprime q' pkt'.y)
    (hq_ne_p' : q' ≠ p)
    (hData' : RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q') :
    BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  exact branchAInterferenceFringeBundle_default
    pkt'.pack
    pkt'.hp_dvd_gap
    pkt'.hgap
    pkt'.hsGN
    pkt'.hsx
    hp_not_dvd_t'
    hqprime'
    hqs'
    hqt'
    hcop_qy'
    hq_ne_p'
    hData'
```

これは **すぐ no-sorry にできる薄い橋** じゃ。
しかも、何が本当の不足物かが綺麗に露出する。

不足物は packet ではなく、

$$
\boxed{
¬ p \mid t' \quad \text{と} \quad \text{new witness / restore properties}
}
$$

じゃと明確になる。

---

## 3. `branchA_wf_contradiction_on_z` の証明スタイル

diff のコメントでは `Nat.lt_wfRel` による無限降下を考えておるが、
実際の Lean 実装では **最小 (z) の反例を取る形** のほうがだいぶ書きやすい。

つまり方針は

1. `hEx : ∃ x y z t s q, BranchAInterferenceFringeBundle ...`
2. その中で (z) 最小の bundle を `Nat.find` 的に取る
3. そこから smaller packet / smaller fringe を作る
4. (z' < z) で最小性に矛盾

じゃ。

これは意味としては well-founded descent そのものじゃが、Lean の項としては
**無限列を直接持ち出すより軽い**。

---

## 4. 今すぐ進む順番

いまの状況だと、次はこの順がよい。
restore 側の open kernel がまだ重い、という全体状況とも整合する。

### 4.1. まず埋めるべきもの

最初に埋めるのは `branchAFringeContradiction_of_descent` ではない。
先に **薄い橋** を増やす。

#### A. `branchA_smallerFringe_of_smallerPacket` を上の強化版へ修正

これは即座に no-sorry 候補じゃ。

#### B. `branchA_smallerPacket_of_fringe` を bridge 版として 1 本切る

つまり、いきなり concrete theorem にせず、

```lean
theorem branchA_smallerPacket_of_primitivePacketDescent
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    ∀ {p x y z t s q},
      BranchAInterferenceFringeBundle p x y z t s q →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

のような **unbundle theorem** を先に置く。
これは現在のライブラリ構造と相性がよい。

### 4.2. その次

そのあとで、真に重いものを 2 択で攻める。

#### route 1. 既存 mainline を使って smaller packet を取る

これは restore/open kernel 側を本当に進める道。

#### route 2. minimal-(z) contradiction を新 target に切る

こちらは terminal-case 路線に寄せる道。

---

## 5. わっちの見立て

今回のコミットでよかったのは、
**「何を置くべきか」が名前として固定された** ことじゃ。

一方で、今のまま進むと

$$
\texttt{branchA_smallerPacket_of_fringe}
$$

に重さが集中しすぎて、結局 restore の open kernel を別の顔で再訪する可能性がある。
だから、次の一手は

$$
\text{まず薄い橋を no-sorry 化して、}
\text{本当に不足している入力を型で露出させる}
$$

これが正解じゃ。

ひとことでまとめると、

$$
\boxed{
\text{新ファイル化は正解。だが次は theorem を埋めるより、まず型を sharpen するべし。}
}
$$

必要なら次に、そのまま貼れる形で
`branchA_smallerFringe_of_smallerPacket` の **修正版 Lean コード** を起こすぞい。
