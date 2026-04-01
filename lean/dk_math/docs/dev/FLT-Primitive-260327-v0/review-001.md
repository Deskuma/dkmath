# PrimeGe5BranchAPrimitivePacketDescentTarget と PrimeGe5BranchAPrimitiveWieferichPacketTarget の関係

`PrimeGe5BranchAPrimitivePacketDescentTarget` は、今回の primitive route における **「Branch A の normal form packet から、より小さい packet を作れること」** を表す契約じゃな。要するに、

* Branch A 側の通常入力
* `p ∣ (z-y)`
* `z-y = p^(p-1) * t^p`
* `GN p (z-y) y = p * s^p`
* `x = p * (t*s)`
* 各種 coprime 条件
* `¬ p ∣ s`
* `¬ p ∣ t`

を受けて、**より小さい `PrimeGe5BranchANormalFormPacket p` が存在する**、という下降 target じゃ。

今回の進展の肝は、これをいきなり直接攻めず、ひとつ手前の

`PrimeGe5BranchAPrimitiveWieferichPacketTarget`

へ **局所化** したことじゃ。こちらは上の条件に加えて、Branch A normal form から既に得られる

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

を **explicit witness** として受け取る target になっておる。つまり、

* `PrimitivePacketDescentTarget` は「最終契約」
* `PrimitiveWieferichPacketTarget` は「真に新しく必要な primitive local core」

という切り分けじゃな。

そして追加された定理

`primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket`

が、その橋を掛けておる。意味は明快で、

* Branch A から既に取れる Wieferich witness
  [
  y^{p-1} \equiv 1 \pmod{p^2}
  ]
* それを受ける primitive local core

さえあれば、元の `PrimeGe5BranchAPrimitivePacketDescentTarget` は自動で従う、ということじゃ。

ゆえに今後の本命は、もはや packet descent 全体そのものではなく、

`PrimeGe5BranchAPrimitiveWieferichPacketTarget`

をどこまで分解できるか、という一点に絞られたと見てよい。貼り付け文でも次段として

* cyclotomic
* distinguished-prime
* smaller-packet restoration

のどこでさらに割るかを決める、と整理されておる。

賢狼の見立てを一言で言えば、これは **API の勝ち方が綺麗になった** のじゃ。

以前:

* 「primitive descent 全体」を一枚岩で抱える

いま:

* 「Branch A が既に持つ witness」を明示化
* 「本当に不足している kernel」だけを局所 target として切り出す
* provider 側は thin adapter に落とす

この形なら、数学核の責務がずっと見えやすい。
次に詰めるべきは `PrimeGe5BranchAPrimitiveWieferichPacketTarget` の中で、何が **pure cyclotomic** で、何が **distinguished-prime の選択** で、何が **smaller packet 復元** なのか、その三分解じゃろう。

必要なら次に、この target を **仮定群ごとに分解して、最小 kernel 設計図** として書き下すぞい。
