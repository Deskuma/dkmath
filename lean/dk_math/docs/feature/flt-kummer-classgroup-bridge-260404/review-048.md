# Kummer branch の戦況と次の戦略

うむ、これはかなり良い戦況じゃ。
しかも、お主の言う通り Codex の応答が途中で途切れていても、**ビルドが通っている** なら、少なくとも「定理境界の追加で全体を壊してはおらぬ」という点は強い。ここは大事な前進じゃ。

まず盤面整理から言うぞい。

直前の段階では、non-first-case の最深 open は
`cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree`
に局所化されており、`TailError` datum から

* Branch A normal form の ((t,s))
* (q \mid t \land \neg q \mid s)
* peel 側 exact-error equation

までは no-sorry で露出できるようになっておった。つまり、その時点で open の正体は「bookkeeping」ではなく **normal form 後の t-side descent** だと読めるようになっていたのじゃ。  

そのさらに先の差分では、`PacketFromError` 全体を open とみなすのでなく、

* (p \mid t) 側の peel exact-error descent
* (\neg p \mid t) 側の既存 `NePCoprimeKernel`

へ分岐する定理
`cyclotomicPrincipalizationNonFirstCasePacketFromError_of_peelExactErrorDescent_and_nePCoprimeKernel`
が導入され、class-group 側の genuinely open な数学内容は
`cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree`
へ押し下げられた、と読むのが自然じゃ。diff の形そのものがそうなっておる。

ゆえに、**もし最新差分まで実際に入っていて build が通っているなら**、いまの最深 open はもはや `PacketFromError` ではなく、

$$
\texttt{cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree}
$$

である可能性が高い。
ここは Codex の返答が途中で切れたせいで文章報告が未完かもしれぬが、貼ってくれた diff 自体はそう読める。わっちはここを現暫定の最新戦況として扱うのがよいと思う。

## 戦況の解説

つまり、いまの非自明な残敵はこうじゃ。

1. first-case は実質閉じた。
2. non-first-case も、縦に刻むだけの戦はほぼ終わった。
3. 残る open は、**peel 側 exact-error 方程式から実際の descent existence を起こす核** に縮んだ。

この変化は大きい。
前は「Kummer non-first-case 全体が open」に見えていた。
今は違う。

$$
q \mid t,\ \neg q \mid s,\ p \mid t
$$

という support と、peel 側 exact-error equation までは no-sorry で出ておる。
よって、いま困っているのは data extraction でも normal form 化でもなく、**その exact-error から (z'^p = (x/q)^p + y^p) をどう作るか**、そこだけじゃ。

賢狼の目には、これは「未解決が多い」状態ではない。
**残る open の数学的型がはっきりした** 状態じゃ。

## 次の戦略

ここで大事なのは、もう **これ以上縦に割らぬ** ことじゃ。
prepare, valuation, error, tailError, packetFromError, packet, reduction, existence, witness と充分に刻んだ。これ以上刻んでも、監査図が伸びるだけで本丸は閉じぬ。

次は **横に接ぐ** 段階じゃ。

### 1. 最新 open の実名を先に確定する

Codex 応答が途中で切れたので、まずこれを確認するのが先じゃ。

見るべきは次の 4 本じゃ。

```lean
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalizationNonFirstCasePacketFromError_of_classGroupPTorsionFree
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
```

ここで、

* `PeelExactErrorDescent_of_classGroupPTorsionFree` が `uses sorry`
* `PacketFromError_of_classGroupPTorsionFree` が wrapper 化済み

なら、最新の最深 open は peel exact-error descent 側で確定じゃ。
逆に `PacketFromError_of_classGroupPTorsionFree` がまだ `uses sorry` なら、35d2 の変更は途中で止まっておる。

お主の build が通っておる以上、**LSP 表示より `#print axioms` と build を真実の源泉にする** のがよい。リポジトリ地図でも、詳細確認は自動レポートや `__sorries.txt` を真実の源泉とする方針じゃ。

### 2. 次の実装は adapter 一本狙い

最新 open が peel exact-error descent なら、次にやるべきは新しい分割ではなく、

$$
\text{Kummer exact-error data} \to \text{既存 Branch A peel descent 語彙}
$$

の **adapter theorem** を作ることじゃ。

すでに no-sorry で取れているものは十分強い。

* normal form ((t,s))
* (q \mid t \land \neg q \mid s)
* (p \mid t) の peel exact-error equation

ここまで来ておるのだから、次はこれを既存の

* `PrimeGe5BranchAValuationPeelPacketFromErrorTarget`
* `PrimeGe5BranchAPeelPthRootCoreTarget`

のどちらか、あるいはその手前の exact-error / pth-root core 補題群へ流すだけでよい。前段の報告でも、次課題はまさにその接続先の粒度調整だと明言されておる。

### 3. ねらいは `p ∣ t` 枝を既存 peel engine に丸投げすること

いまの open は

$$
p \mid t
$$

な peel 側だけに局所化された。
ならば新規にやるべき数学は「全体の existence」を証明することではなく、

$$
p \mid t,\quad
t = p t_1,\quad
pB = C + (p^{p-1} t_1^p)E
$$

という exact-error 方程式が、既存 peel engine の入力条件を満たすことを示すことじゃ。

ここでの勝ち筋は、`PeelExactErrorDescentTarget` 自体を新規証明するより、

$$
\text{existing peel theorem} \Rightarrow \text{PeelExactErrorDescentTarget}
$$

という薄い wrapper に落とすことじゃよ。
これが通れば、芋づるで

* `PacketFromError`
* `Packet`
* `Reduction`
* `Existence`
* `Descent`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree`
* `FLTPrimeGe5Target_of_kummerRoute`

まで `sorry` が消える見込みが高い。

## 提案する実務順

わっちなら次をこの順でやる。

### A. 真偽確認

まず上の `#print axioms` 4 本で、最深 open がどこにあるかを確定する。

### B. exact-error 入力整理

`cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree` の仮定列と、既存 peel theorem の仮定列を並べる。
ここで「既に持っているもの」と「足りぬもの」を 1 対 1 に対応させる。

### C. adapter theorem 作成

例えば思想としては、

```lean
theorem cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_existingPeelKernel
    (hPeelCore : <既存 peel 側 target>) :
    CyclotomicPrincipalizationNonFirstCasePeelExactErrorDescentTarget := by
  ...
```

の形じゃ。
ここで exact-error 方程式と (p \mid t) を既存核へ食わせる。

### D. wrapper 差し替え

`cyclotomicPrincipalizationNonFirstCasePeelExactErrorDescent_of_classGroupPTorsionFree`
を上の adapter 呼び出しに置換する。

### E. 再監査

最後に

```lean
#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree
#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute
```

を見て、principalization 側の `uses sorry` が消えたか確かめる。

## ロードマップの終点

閉じるまでの筋を一文で言えば、こうじゃ。

$$
\boxed{
\text{残る open を peel exact-error descent 1 本に確定し、
それを既存 Branch A peel machinery への adapter で潰す}
}
$$

これが通れば、Kummer / class-group principalization 枝はかなり高い確率で閉じる。
そのあと full FLT route にまだ `uses sorry` が残るなら、それはもう principalization 外の残件じゃ。そこではじめて全体棚卸しをすればよい。

今の戦況、悪くないどころか、かなり終盤じゃよ。
必要なら次に、**`PeelExactErrorDescentTarget` を既存 peel theorem に接ぐ adapter 雛形** を、そのまま Lean で起こすぞい。
