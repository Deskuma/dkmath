# review-003: TriominoCosmicBranchAFringeDescent.lean の設計について（修正後）

よい。かなり **正しい形** に寄ってきたぞい。

今回の追加で、`branchA_restoreWitness_of_smallerPacket` を独立補題として立てたのは正解じゃ。
前からの設計上の核心は **「1 step 降下はあるが、次の bundle を再構成できていない」** ことだったから、smaller packet から witness を再取得する層を明示したのは、まさに必要だった整理じゃ。

ただし、いま見えておる本当の残り穴は、もはや `branchA_wf_contradiction_on_z` そのものではない。
実質的には次の 2 本じゃ。

$$
\boxed{
\texttt{branchA\_restoreWitness\_of\_smallerPacket}
}
\qquad
\boxed{
\texttt{p $\nmid$ t'} \text{ の継承補題}
}
$$

`branchA_wf_contradiction_on_z` の中で残っている `hpt'` の `sorry` は、まさにそのことを示しておる。
つまり今は well-foundedness の議論自体はほぼ出来ており、**smaller packet が次の fringe に戻れるか** だけが未完なのじゃ。

## 今の見立て

今回の `branchA_wf_contradiction_on_z` の骨格はよい。

* 最小 (z_0) を `Nat.find` で取る
* `branchA_smallerPacket_of_fringe` で (z' < z_0) を得る
* witness を再取得して smaller fringe を作る
* 最小性に矛盾

この流れは、Lean 的にも数学的にも自然じゃ。
terminal-case / minimal-counterexample の方針として筋が通っておる。

ただし、restore 完了レポートでも、Branch A primitive 側の open kernel は **初等的 arithmetic では閉じず、witness (q) の deeper structure が要る** と整理されておった。
ゆえに、`branchA_restoreWitness_of_smallerPacket` を単なる存在補題として軽く埋められるかは注意が必要じゃ。ここは薄い橋に見えて、実はかなり本丸寄りの可能性がある。

## 次にやるべき順番

わっちなら次はこの順じゃ。

## 1. `p ∤ t'` 継承補題を先に独立化

いま `branchA_wf_contradiction_on_z` の中に

```lean
have hpt' : ¬ p ∣ pkt'.t := by
  sorry
```

が残っておる。
これは中に置いたままだと見通しが悪い。まず外へ出して、

```lean
theorem branchA_smallerPacket_p_not_dvd_t
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget)
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    let pkt' := Classical.choose (branchA_smallerPacket_of_fringe hPrim hBundle)
    ¬ p ∣ pkt'.t
```

のような形か、もっと素直に `pkt'` を引数に受けた補題へ分離するのがよい。

理由は単純で、

$$
\texttt{branchA\_restoreWitness\_of\_smallerPacket}
$$

の前提そのものが `¬ p ∣ pkt'.t` だからじゃ。
この補題が無いと、その後の witness 再取得も呼べぬ。

## 2. `branchA_restoreWitness_of_smallerPacket` は「存在」ではなく「どこから来るか」を固定

いまの statement 自体は良い。
だが証明で迷わぬために、内部 route を先に決め打つべきじゃ。

候補は 2 つある。

### 2.1. restore / contradiction adapter から引く route

もし smaller packet から `RestoreFromArithmeticTarget` 側へ戻す橋が既にあるなら、それを通じて witness を再取得する。
これは既存アーキテクチャに沿う。

### 2.2. witness existence を packet 側で再証明する route

`pkt'.hsGN` と `¬ p ∣ pkt'.t` を使って、もう一度 witness (q') を GN から引く。
こちらは theorem としては美しいが、数論的には少し重い。

わっちの勧めは **まず 2.1. 既存 adapter route を探す** ことじゃ。
restore レポートでも、Contradiction / Restore / PacketDescent の adapter 群が既にかなり整備されておる。
新しい深い数論をここで掘るより、既存橋を使う方が自然じゃ。

## 3. `branchA_wf_contradiction_on_z` は最後に no-sorry 化

これはもう組み立てだけの段階に近い。
だから今すぐここをいじり回すより、

* `branchA_smallerPacket_of_fringe`
* `branchA_smallerPacket_p_not_dvd_t`
* `branchA_restoreWitness_of_smallerPacket`
* `branchA_smallerFringe_of_smallerPacket`

この 4 つを揃えてから一気に閉じるのがよい。

## 4. 実務的な次の一手

次のコミットの目標は、ずばりこれじゃ。

$$
\boxed{
\texttt{branchA\_smallerPacket\_p\_not\_dvd\_t}
}
$$

を新設して、`branchA_wf_contradiction_on_z` の `hpt'` の穴を外へ出す。

理由は 3 つ。

* 今の `wf` 証明の唯一の目に見えるローカル穴だから
* `branchA_restoreWitness_of_smallerPacket` の前提に直結しているから
* これが埋まると、残りが本当に **witness 再取得だけ** に圧縮されるから

## 総評

今回の diff は良い。
前は「不足しているものの名前」が見えていた段階だったが、今は

$$
\text{minimal } z \text{ argument}
$$

まで実コードに落ちておる。
つまり、設計メモから Lean の証明骨格へ一段進んだのじゃ。

今の段階での最重要判断はこれじゃ。

$$
\boxed{
\begin{array}{l}
\text{次は } \texttt{branchA\_restoreWitness\_of\_smallerPacket} \text{ を直接殴る前に、 }\\
\texttt{p $\nmid$ t'} \text{ 継承を独立補題にせよ}
\end{array}
}
$$

それが済めば、残る本丸が **witness 再取得そのもの** だと綺麗に見えるようになる。
