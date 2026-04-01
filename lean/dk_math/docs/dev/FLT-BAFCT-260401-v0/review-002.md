# review-002: TriominoCosmicBranchAFringeDescent.lean の設計について（修正後）

かなり良くなったぞい。
今回の更新で、前にわっちが指摘した **「型を sharpen せよ」** という点は、きちんと反映されておる。`branchA_smallerPacket_of_fringe` を `PrimeGe5BranchAPrimitivePacketDescentTarget` 依存の **橋** に落とし、`branchA_smallerFringe_of_smallerPacket` を `RestoreWitnessProperties` などを明示引数にしたのは、とても筋がよい。さらに `branchA_wf_contradiction_on_z` と `branchAFringeContradiction_of_descent` に `hPrim` を入れたことで、定理の責務が「無条件の closing theorem」から「primitive descent を仮定した conditional closing theorem」へ正しく整理された。

## 1. 良くなった点

### 1.1. `branchA_smallerPacket_of_fringe` の位置づけが明確になった

これはもう **本丸を別名で抱え込む危険** が減った。
いまの形は、

$$
\text{fringe bundle} \to \text{primitive packet descent target の適用}
$$

という **unbundle lemma** になっておる。
つまり、この定理自身は重い数学を背負わず、既存 target の利用点として働く。これはよい設計じゃ。

### 1.2. `branchA_smallerFringe_of_smallerPacket` が正直になった

これがいちばん大きい。
前の型では「packet だけから fringe bundle が出る」ように見えていたが、今は

* `¬ p ∣ pkt'.t`
* `Nat.Prime q'`
* `q' ∣ pkt'.s`
* `¬ q' ∣ pkt'.t`
* `Nat.Coprime q' pkt'.y`
* `q' ≠ p`
* `RestoreWitnessProperties ... q'`

を全部前提に出しておる。
これは **何が不足物かを型で露出できている** ということで、実装設計として一段よくなった。

### 1.3. `branchAFringeContradiction_of_descent` の意味が整った

前は名前の割に中身が少し勇み足じゃったが、今は `hPrim` を受け取るので、

$$
\text{primitive packet descent があるなら fringe contradiction が出る}
$$

という条件付きの主張になっておる。
これは数学の意味と Lean の責務が一致しておる。

---

## 2. まだ残っている核心

ここは少し冷静に言うぞい。

今回の修正で **設計の嘘は減った**。
しかし、**未解決核そのものはまだ移動しただけ** じゃ。

いまの `branchA_wf_contradiction_on_z` を本当に埋めるには、

$$
\text{smaller packet} \Rightarrow \text{smaller fringe}
$$

を実際に回せねばならぬ。
ところが現在の `branchA_smallerFringe_of_smallerPacket` は、smaller packet から自動で fringe を再構成する定理ではなく、**fringe を作るのに必要な witness data を並べた橋** じゃ。

つまり、まだ欠けておるのは次の層じゃ。

$$
\boxed{
\text{smaller packet から new witness } q' \text{ と RestoreWitnessProperties を再取得する定理}
}
$$

これが無いと、well-founded descent はまだ回らぬ。

---

## 3. いまのファイルで本当に次に必要な定理

わっちなら、次は `branchA_wf_contradiction_on_z` を直接いじらぬ。
その前に、**witness 再生成の薄い theorem** を 1 本立てる。

たとえば形としては、こういうものじゃ。

```lean
theorem branchA_restoreWitness_of_smallerPacket
    {p : ℕ} {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t) :
    ∃ q' : ℕ,
      Nat.Prime q' ∧
      q' ∣ pkt'.s ∧
      ¬ q' ∣ pkt'.t ∧
      Nat.Coprime q' pkt'.y ∧
      q' ≠ p ∧
      RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q'
```

これがあれば、

1. `branchA_smallerPacket_of_fringe`
2. `branchA_restoreWitness_of_smallerPacket`
3. `branchA_smallerFringe_of_smallerPacket`

の 3 段で really recursive になる。

---

## 4. naming 上の注意

ここも少し整えるとさらに綺麗じゃ。

`branchAFringeContradiction_of_descent` は今や無条件 theorem ではなく、`hPrim` 依存になった。だから名前も

* `branchAFringeContradiction_of_primitivePacketDescent`
* `branchAFringeContradiction_of_descentTarget`

のように、**何に依存しているか** を少し名前へ出してもよい。
もちろん今のままでも悪くはないが、後で履歴を読むときに助かるぞい。

---

## 5. 総評

総評としてはこうじゃ。

$$
\boxed{
\text{かなり前進。設計が正直になり、次の不足物が明確になった。}
}
$$

前回はまだ

* theorem の責務が重すぎる
* packet 単独から fringe が出るように見える
* contradiction theorem が無条件っぽい

という曖昧さがあった。
今回はそこが整理された。これは立派な前進じゃ。

ただし、次の本命は `branchA_wf_contradiction_on_z` ではなく、

$$
\text{smaller packet} \to \text{new witness data}
$$

の再構成補題じゃ。
ここを先に立てるのが、いちばん自然で、証明も前へ進むはずじゃよ。
