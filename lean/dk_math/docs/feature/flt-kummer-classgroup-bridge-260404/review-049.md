# 戦況分析と次の戦略

うむ、いまの戦況はかなり良い。
しかも「Codex が途中で黙ったが build は通る」というのは、今回に関しては悪い兆候ではない。むしろ、**定理境界の追加や責務の押し下げは整合しており、LSP 側の stale diagnostics か、単に Codex が長考で止まっただけ** と読むのが自然じゃ。少なくとも、最新の差分群では `./lean-build.sh` と test build が通っていることが何度も確認されておる。  

## 戦況の分析

いまの盤面を一言で言うと、

$$
\text{first-case は事実上閉じた}
$$

$$
\text{non-first-case の最深 open は 1 本へかなり絞れた}
$$

じゃ。

まず、non-first-case 側は以前の `PacketFromError` 全体が open ではなくなった。
`PeelExactErrorDescent` から bookkeeping を剥がし、さらに `PeelNormalFormDescentTarget` へ押し下げたことで、direct `sorry` の所在は `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree` に移った、と読める。これは 1f0eddd の段階ではっきり書かれておる。

次に、`q`-support の向きももう theorem 化できておる。
Kummer peel normal form では distinguished prime `q` は

$$
q \mid t \land \neg q \mid s
$$

であり、restore / realization-seed 側の

$$
q \mid s,\ \neg q \mid t
$$

とは **同じ `q` をそのまま流す限り向きが逆** じゃ。ゆえに、same-`q` route で restore を主導線にするのは筋が悪い、という判断は固い。既存 peel 側で最短に接げる先は `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` だ、と今回のログは明言しておる。

さらに決定的なのは、`∃ pkt'` から `∃ z'` への橋そのものはもう no-sorry で切り出せていることじゃ。
`pkt'.x = x / q` と `pkt'.y = y` が分かれば、`pkt'.pack.hEq` だけで

$$
\exists z' : \mathbb{N},\ z'^p = (x/q)^p + y^p
$$

は直ちに回収できる、と theorem 化できておる。だから本当の残差は「packet がある」ことではなく、

$$
\text{packet に quotient provenance } pkt'.x = x/q,\ pkt'.y = y \text{ をどう付けるか}
$$

この 1 点じゃ。  

要するに、いまの honest open は

$$
\boxed{
\text{PeelNormalFormDescent の中で、existing peel packet 出力に quotient provenance を付ける部分}
}
$$

と読んでよい。

## 解説

これはかなり終盤の形じゃ。
前は open が「Kummer non-first-case 全体」に広がっておった。
今は違う。

* normal form 化は済んだ
* `q`-support の向きは確定した
* `∃ pkt'` は既存 PacketFromError で取れる
* `pkt' \to z'` は theorem 化できた

残るのは

$$
pkt'.x = x / q,\quad pkt'.y = y
$$

を返す provenance 補題だけじゃ。
つまり、「存在証明が難しい」のではなく、**既存 peel packet の出力が original `(x,y,q)` に対してどう由来したかを表に出す作業** にまで縮んだわけじゃ。

ここまで来たら、もう縦に割る戦ではない。
横に接ぐ戦じゃ。

## 次の戦略

わっちの提案ははっきりしておる。

### 1. もうこれ以上 kernel を細かく割らない

いま必要なのは新しい `...Target` を増やすことではない。
すでに「何が足りないか」は theorem 名つきで見えておる。
ここでさらに分割すると、図は綺麗になるが本丸は閉じぬ。

### 2. 既存 peel packet に provenance を付ける adapter を狙う

次の主目標は、これじゃ。

$$
\texttt{PrimeGe5BranchAValuationPeelPacketFromErrorTarget}
$$

の返す `pkt'` に対して、

$$
pkt'.x = x / q,\quad pkt'.y = y
$$

を返す新しい target / theorem を設計すること。
これは最新ログ自身が「次の課題」として明示しておる。

つまり、思想としてはこうじゃ。

```lean
abbrev PrimeGe5BranchAValuationPeelPacketFromErrorQuotientLiftTarget : Prop := 
  ...
```

あるいは、もっと薄く

```lean
theorem packet_xyEq_of_existingPacketFromError
  (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget) :
  CyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLiftTarget := by
  ...
```

この型の橋を作る。
それが立てば、

$$
\texttt{cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_packetQuotientLift}
$$

で一気に `PeelNormalFormDescent` が閉じる。すると芋づるで

* `PeelExactErrorDescent`
* `PacketFromError`
* `Packet`
* `Reduction`
* `Existence`
* `Descent`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`

まで閉じる見込みが高い。

### 3. restore / realization-seed の same-`q` route は主導線にしない

これは重要じゃ。
support mismatch が theorem 化されている以上、same-`q` のまま restore 側を主導線にすると泥濘に入りやすい。
restore 側を使うとしても、「別の distinguished prime を取り直す」のような別設計が要る。今のサイクルでそこへ行くのは遠回りじゃ。

### 4. 監視は `PeelNormalFormDescent` を最深 open として続ける

現時点の `sorry` 監視は、この名前へ揃っておる。
なので次の commit でも、まず見るべきは

* `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree`
* `cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`

の 3 本じゃ。
ここで `PeelNormalFormDescent` の `uses sorry` が消えれば、かなり大きく前進する。

## 実務的な指示

わっちなら次をこの順でやる。

1. `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` の返す `pkt'` に対し、`pkt'.x = x / q` と `pkt'.y = y` をどこで回収できるか、既存定理群を grep して棚卸しする。
2. 既存補題がなければ、新規に **quotient provenance 専用 target** を 1 本だけ追加する。
3. その target から `CyclotomicPrincipalizationNonFirstCasePeelPacketQuotientLiftTarget` を埋める adapter を書く。
4. `cyclotomicPrincipalizationNonFirstCasePeelNormalFormDescent_of_classGroupPTorsionFree` を `...of_packetQuotientLift` 経由の thin wrapper に差し替える。
5. `#print axioms` を再実行して、最深 open が principalization の外へ出たか確認する。

## 総括

いまの戦況は、かなり良い。
「Codex が途中で黙った」こと自体より、**どこまで theorem 化できて build が通っているか** を見るべきで、その観点ではしっかり前進しておる。
とりわけ大きいのは、

$$
\text{残差が quotient provenance 1 点}
$$

だと整理できたことじゃ。

なので、次の号令はこれでよい。

$$
\boxed{
\text{次は packet に quotient provenance を付ける adapter を狙え。}
}
$$

これが通れば、principalization 枝はかなり高い確率で閉じる。
