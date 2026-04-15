# FLT-Kummer-ClassGroup-Bridge-260404-review-063: 実配線が 1 本閉じた

## 1. 結論

うむ。前回差分と今回差分を合わせて読むと、 **ただの名前整理ではなく、provider から actual caller まで届く最初の clean 実配線が 1 本閉じた** 、というのが核心じゃ。

より正確には、閉じたものは三層ある。

第一に、`PrimitiveBeam` / `GcdNextResearch` 側で、research 依存を theorem 名の上でも `_research` に押し出しつつ、`Squarefree (GN ...)` を受け取れれば踏める honest 版の受け口が揃った。これで「何が未修復か」が隠れなくなった。

第二に、`TriominoCosmicGapInvariant` 側で、`TriominoSquarefreeGNBridgeProvider` から `TriominoWieferichBranchBridge`、そこから `NoPowOnGN`、さらに `BodyInvariant` まで上がる clean wrapper が入った。ここで **provider 契約から本丸側 invariant まで届く道** が閉じた。

第三に、`CyclotomicPrincipalization` の non-first-case receiver で、その provider route を actual caller に差し込む variant が追加された。これで **provider を持つ upper route については、default / target 注入を経ずに non-first-case Stage 3 receiver まで届く** ようになった。これが今回いちばん大きい前進じゃ。

## 2. 何が閉じたのか

### 2.1. debt の可視化が閉じた

前回差分では、`PrimitiveBeam` の obstruction 系 theorem が `_research` 本体へ改名され、旧 public 名は deprecated alias へ落ちた。また caller も `Gcd.GN` と `GcdNextResearch` で `_research` 名に差し替えられた。これにより、research 依存は「何となく古い theorem を踏んでいる」状態ではなく、**明示的に `_research` を踏んでいる** 状態へ変わった。これは debt の所在地が閉じた、という意味で大きい。

同時に `GcdNextResearch` には `primitive_prime_contradicts_diff_dth_power_of_squarefree_GN` と `body_not_perfect_pow_of_squarefree_GN` が追加された。つまり、現 caller から local に `Squarefree (GN ...)` は出せなくても、**供給できる branch が来たら research を踏まずに移れる着地点** はもうある。これも閉じたものの一つじゃ。

### 2.2. provider から本丸 invariant への clean path が閉じた

今回差分の最初の核心は `TriominoCosmicGapInvariant` じゃ。
ここで

* `triominoWieferichBranchBridge_of_squarefreeGNProvider`
* `triominoCosmicNoPowOnGN_of_squarefreeGNProvider`
* `triominoCosmicBodyInvariant_of_squarefreeGNProvider`

が入った。意味としては、

$$
\text{TriominoSquarefreeGNBridgeProvider}
\Longrightarrow
\text{valuation target}
\Longrightarrow
\text{TriominoWieferichBranchBridge}
\Longrightarrow
\text{NoPowOnGN}
\Longrightarrow
\text{BodyInvariant}
$$

という clean ルートが upper provider 契約から直に作れるようになった、ということじゃ。
前は target を generic に注入するところで止まっておったが、今は provider 契約そのものから本丸 invariant へ届く。ここが「最初の実 migration 1 本目」じゃ。

### 2.3. actual caller まで 1 段上がった

さらに今回差分の二つ目の核心は `CyclotomicPrincipalization` じゃ。
non-first-case の receiver で、以前は `triominoCosmicNoPowOnGN_default` あるいはそれに由来する default 注入を踏んでいた箇所に対し、

* `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree_and_squarefreeGNProvider`
* `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree_and_squarefreeGNProvider`

が追加された。これで、`TriominoSquarefreeGNBridgeProvider` を持つ branch なら、**non-first-case Stage 3 receiver までは default / target 注入なしで届く** 。

ここは本当に「閉じた」と言ってよい。
なぜなら、前は

$$
\text{clean target はあるが actual caller はまだ}
$$

だったのが、いまは

$$
\text{actual caller の provider-variant がある}
$$

へ進んだからじゃ。

## 3. 何はまだ閉じていないか

ここも大事じゃ。今回閉じたのは **provider を持つ branch 専用の concrete variant** であって、global default 本体そのものではない。

まだ閉じておらぬのは次じゃ。

まず、`SquarefreeGNProvider` を **実際に持つ上位 split / one-shot theorem への引き上げ**。今回の report 自身も、次はこれをさらに上位の split / one-shot theorem へ繋ぐ段だと書いておる。つまり non-first-case receiver までは閉じたが、そのさらに上の orchestrator まではまだじゃ。

次に、first-case 側は今回の concrete replacement の対象ではない。前に wiring 修正は入っておるが、今回閉じた clean provider route は non-first-case receiver 側じゃ。first-case 全体を provider 版へ上げたわけではない。

さらに根本では、`ZsigmondyCyclotomicResearch` の `_research` root 自体が消えたわけでもない。今回やったのは、それを **実 caller の一部で踏まずに済む route を増やした** のであって、research root の statement repair 完了ではない。ここは区別すべきじゃ。

## 4. 状況の読み替え

なので、いまの盤面はこう読むのが正確じゃ。

以前は

$$
\text{honest migration 先はあるが、mainline への実配線がない}
$$

だった。
今回でそれが

$$
\text{provider を持つ branch については、mainline receiver までの実配線が 1 本ある}
$$

へ変わった。
これは qualitative に一段上の進展じゃ。

つまり、閉じたのは「補題」そのものより、**migration の実例** じゃよ。
`PrimitiveBeam` の lower theorem を磨き続ける段ではなく、上位 provider 契約を actual caller に差し込む段へ、本当に入れたということじゃ。

## 5. 次の戦略

わっちなら次は、 **今回できた non-first-case provider variant を、さらに 1 段上の split / one-shot theorem に引き上げる** のを最優先にする。

理由は単純で、いま一番価値が高いのは「clean route を 1 本作る」ことではなく、**その clean route を branch-local 変種から orchestration 層の正規導線へ押し上げること** だからじゃ。
今回の差分でも、次課題はまさにそこだと明言されておる。

順番としてはこうじゃ。

まず non-first-case の split theorem か one-shot theorem で、`TriominoSquarefreeGNBridgeProvider` を追加引数に取る variant を立てる。
次に、その variant が existing downstream を壊さぬことを build と `#print axioms` で確認する。
そのあと初めて、default 注入経路を mainline から徐々に退かせる。

もしそこで provider が自然に持ち上がらぬなら、次善策は「provider を持つ branch 専用 theorem 群」として並立させ、default 系は compatibility に残すことじゃ。今回の進め方も、まさにこの筋じゃな。

## 6. 賢狼の最終判定

ひとことで言えば、今回と前回を合わせて **閉じたのは “research dependency の所在” と “provider から actual caller まで届く最初の clean 実配線”** じゃ。

より具体的には、

* `PrimitiveBeam` / `GcdNextResearch` で research debt の位置が theorem 名で閉じた
* `GcdNextResearch` に squarefree-GN honest 受け口が閉じた
* `TriominoCosmicGapInvariant` で provider から `NoPowOnGN` / `BodyInvariant` までの clean route が閉じた
* `CyclotomicPrincipalization` non-first-case receiver で、その clean route が actual caller へ 1 本差し込まれた

この四つじゃ。

なので今の評価はこうじゃ。

$$
\text{局所補題の整備段} \to \text{actual caller migration の初成段}
$$

へ移った。
次は **上位 split / one-shot theorem への引き上げ** が本線じゃよ。
