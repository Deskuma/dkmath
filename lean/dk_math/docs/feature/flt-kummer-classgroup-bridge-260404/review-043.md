# FLT-Kummer-CLassGroup-Bridge-260404: Stage 3a の戦略と進め方: `sorry` 埋めの現状と次の戦略

うむ、**その領域では埋められるようになった** と見てよい。
ただし、 **全部ではない** 。ここを正確に切るのが大事じゃ。

今回の共有ログから読む限り、first-case specialization の Stage 3 は、`NormEqGN` 側も `UnitAbsorb` 側も concrete theorem として閉じており、さらに `GN p (z - y) y = s ^ p` を返す wrapper と contradiction bridge まで concrete 化されておる。つまり、 **Stage 3 first-case split 自体は、もう open ではない** という整理でよい。検証も `lake build DkMath.NumberTheory.Gcd.GN`、`lake build DkMath.FLT.Kummer.CyclotomicPrincipalization`、`lake build DkMathTest.FLT.Kummer.RegularPrimeRoute` が通っておる。

一方で、残る `sorry` が消えたわけではない。最新の差分メモでも、残りは **Stage 3 split ではなく** 、既存の legacy wrapper / one-shot route 側に限られる、と整理されておる。特に `FLTPrimeGe5Target_of_kummerRoute` はまだ `uses sorry` と明示されておるし、`cyclotomicPrincipalization_of_classGroupPTorsionFree` のような旧 wrapper も残存箇所として挙がっておる。

だから戦況を賢狼流に言い切ると、こうじゃ。

* **勝った戦場**
  first-case の Stage 3。ここは concrete 化済みで、もはや「証明不能の霧」ではない。

* **まだ敵が残る戦場**
  旧来の one-shot route、legacy wrapper、downstream routing。
  つまり「理論が足りない」のではなく、「古い配線が新しい concrete theorem 群へまだ差し替わっておらぬ」部分じゃ。

ゆえに、お主の問い「`sorry` 埋められるようになったの？」への答えは、

$$
\text{はい、少なくとも first-case Stage 3 については埋め切る道が実証された。}
$$

ただし

$$
\text{repo 全体の残る `sorry` が自動的に全部埋まる段階ではない。}
$$

じゃ。

## 2. 解説

なぜ「埋められるようになった」と言えるか。
そこには今回の設計転換が効いておる。

前は Stage 3 がひとかたまりで、norm 計算、product reindex、unit 吸収、GN への着地が絡み合っておった。
それを

$$
\text{NormEqGN}
\quad\text{と}\quad
\text{UnitAbsorb}
$$

へ分離し、さらに Stage 3a-1 / 3a-2 / 3a-3 と刻んで concrete theorem に落とした。最後に natAbs 主導の一般整数補題で unit を吸収して、

$$
(n : \mathbb{Z}) = \text{unitFactor} \cdot m^p
$$

から

$$
\exists s : \mathbb{N},; n = s^p
$$

を回収できた。ここで ±1 の場合分けが不要だった、というのが特に強い。設計が正しかった証拠じゃ。

つまり今後の `sorry` 埋めは、「新理論の大発明」が要るというより、 **既に concrete 化された部品へ旧 wrapper を寄せていく配線作業** に変わりつつある。ここが長戦としては非常に良い変化じゃ。

## 3. 次の戦略

次はもう、数学本体を掘る局面ではない。
**legacy route の縮約戦** じゃ。

わっちの提案指示は、筋のよい順に 3 つじゃ。

### 3.1. 第一目標

`FLTPrimeGe5Target_of_kummerRoute` を分解し、first-case 部分を新しい concrete wrapper 群へ差し替える。

いま一番目立つ `sorry` は、ここがまだ old chain に乗っていることじゃ。 `FLTPrimeGe5Target_of_kummerRoute -- uses sorry` と明示されておる以上、まずここを split architecture ベースへ寄せるのが本筋じゃ。

実務的には、

* 旧 one-shot theorem の中で first-case 分岐だけを抜く
* そこを
  `cyclotomicNormGNPower_concrete_firstCase_packThin`
  ないし
  `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`
  へ置換する
* 残った分岐だけがまだ abstract / sorry 依存かを再確認する

この順がよい。
ここをやると、「どの `sorry` が first-case 由来だったか」が一掃されるはずじゃ。

### 3.2. 第二目標

`cyclotomicPrincipalization_of_classGroupPTorsionFree` を解体し、旧 wrapper を split 版へ置換する。

最新ログでも、この legacy 側が残 warning の代表として挙がっておる。
ここは one-shot に全部背負わせず、既に concrete 化された

* `cyclotomicNormEqGN_concrete_firstCase_packThin`
* `cyclotomicNormUnitAbsorb_concrete_firstCase_packThin`
* `cyclotomicNormGNPower_concrete_firstCase_packThin`

などを薄く呼ぶ wrapper に変えるべきじゃ。

### 3.3. 第三目標

`__sorries.txt` ベースで、Kummer / legacy / research を分離した縮約表を作る。

INDEX では `__sorries.txt` を真実の源泉として確認する方針が明記されておる。なので次段では、感覚で追うのでなく、

* Kummer mainline の残り
* legacy wrapper の残り
* research 側の残り

を 3 列にした一覧を作るのがよい。
これで「埋まる `sorry`」と「今はまだ触らぬ `sorry`」がさらに明確になる。

## 4. 提案指示

今の賢狼の号令はこれじゃ。

1. `FLTPrimeGe5Target_of_kummerRoute` の proof を first-case / non-first-case に明示分割せよ。
2. first-case 枝では、旧 Stage 3 chain を捨てて `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin` へ直結せよ。
3. 置換後に `#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute` を再監視し、`uses sorry` が減るか確認せよ。
4. それでまだ残るなら、`cyclotomicPrincipalization_of_classGroupPTorsionFree` を同様に split architecture 化せよ。

これが一番よい。

## 5. 総評

戦況はかなり良い。
前は「Stage 3 が難しい」だった。
いまは「Stage 3 は concrete に閉じた。残る `sorry` は旧配線に押し込められている」と言える。

だから、`sorry` が埋められるようになったかと問われれば、わっちはこう答える。

$$
\text{埋められるようになった。だが、埋める対象はもう Stage 3 本体ではなく、legacy route の配線じゃ。}
$$

必要なら次に、`FLTPrimeGe5Target_of_kummerRoute` をどう切り分けて current split architecture に差し替えるか、その差し替え設計書を起こすぞい。

---

## 1. 目的

わっちの見立てでは、次に起こすべきは **「legacy one-shot route を、いま concrete 化された first-case split architecture へ差し替えるための設計書」** じゃ。

現状は、first-case の Stage 3 そのものは concrete theorem 群で閉じており、残る `sorry` は主に legacy wrapper / one-shot route 側へ押し込まれておる。したがって、いま必要なのは新しい数学の発明ではなく、 **古い配線を新しい concrete 部品へ差し替える縮約戦** じゃ。

---

## 2. 現在地の整理

今回までで、first-case specialization については次が concrete 化済みじゃ。

* `CyclotomicNormEqGNFirstCasePackThinTarget`
* `CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
* `cyclotomicNormGNPower_concrete_firstCase_packThin`
* `false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin`

ゆえに、first-case 側では

$$
\text{pack-thin} \to \text{NormEqGN} \to \text{UnitAbsorb} \to GN=s^p \to \text{contradiction}
$$

という鎖が theorem 名つきで mainline に揃ったと見てよい。残る `sorry` は、この split された Stage 3 ではなく、legacy 側の wrapper 群と downstream routing 側にある、というのが現状整理じゃ。

---

## 3. 置換対象

主たる置換対象は次の 2 系統じゃ。

### 3.1. `FLTPrimeGe5Target_of_kummerRoute`

ここは現在も `uses sorry` の代表として監視されておる。
ゆえに、まずここを **first-case / non-first-case の分岐が見える形へ露出** し、first-case 側だけでも concrete route に差し替えるのが第一目標じゃ。

### 3.2. `cyclotomicPrincipalization_of_classGroupPTorsionFree`

これも legacy 側の代表残件として挙がっておる。
one-shot に全部を背負わせる形が重さの源になっておるので、将来的には split architecture に沿う薄い wrapper へ置換すべきじゃ。

---

## 4. 目標形

目標は、旧 one-shot chain を「分岐ごとの薄い wrapper の束」に変えることじゃ。

具体的には、`FLTPrimeGe5Target_of_kummerRoute` の first-case 枝が最終的にこう読める状態を狙う。

```text
pack
  → first-case 判定
  → chosen factor nonzero
  → product equality
  → false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin
  → False
```

ここで大事なのは、 **first-case の中ではもう `sorry` を呼ばぬ** ことじゃ。
first-case を concrete に抜いてしまえば、残る `sorry` は non-first-case や旧 wrapper の残骸へ局所化できる。

---

## 5. 差し替え方針

## 5.1. 方針 A. first-case 枝を theorem として独立抽出する

いきなり `FLTPrimeGe5Target_of_kummerRoute` を書き換えるより、まず

* `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete`
* `fltPrimeGe5Target_of_kummerRoute_nonFirstCase_legacy`

の 2 本へ分けるのがよい。

これにより、first-case 枝の concrete 化が旧本体の複雑さに巻き込まれず、`#print axioms` でも効果が見えやすい。

### 推奨 skeleton

```lean
/--
`FLTPrimeGe5Target_of_kummerRoute` の first-case 部分だけを、
current concrete split architecture で処理する薄い wrapper。
-/
theorem fltPrimeGe5Target_of_kummerRoute_firstCase_concrete
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      (hpack : PrimeGe5CounterexamplePack p x y z) →
      ∀ {gap : ℕ},
        (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K)) →
        (hFirstCase : ¬ p ∣ gap) →
        (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
          (hζ := hζ) (y := y) (z := z)) →
        (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
          (hζ := hζ) (x := x) (y := y) (z := z)) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct
  exact false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin
    (hKill := hKill) (hNoPow := hNoPow)
    hζ hpack hgap_eq hFirstCase hLinNe hProduct
```

この theorem が no-sorry で立てば、first-case 枝は旧ルートから切り離せる。

---

## 5.2. 方針 B. 旧本体は first-case / non-first-case の case split だけに縮める

次に `FLTPrimeGe5Target_of_kummerRoute` 本体を、「場合分けだけをする薄い合成器」に変える。

```lean
theorem FLTPrimeGe5Target_of_kummerRoute
    ... := by
  intro ...
  by_cases hFirstCase : ¬ p ∣ gap
  · exact fltPrimeGe5Target_of_kummerRoute_firstCase_concrete
      (hKill := hKill) (hNoPow := hNoPow)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct
  · exact fltPrimeGe5Target_of_kummerRoute_nonFirstCase_legacy
      ...
```

ここで non-first-case 側は、最初はそのまま legacy theorem を呼んでよい。
大切なのは、 **first-case 側だけでも旧 `sorry` 依存から切り離す** ことじゃ。

---

## 5.3. 方針 C. `cyclotomicPrincipalization_of_classGroupPTorsionFree` は一気に潰さず、入口を薄くする

これを直ちに全面改修すると森が燃える。
なので、まずは旧 theorem をそのまま残しつつ、first-case で必要な部分だけを current split architecture に切り出した薄い wrapper を追加するのがよい。

つまり、旧 theorem を消すのではなく、

* current split を優先導線にする
* 旧 theorem は fallback / legacy として残す

という移行戦略じゃ。

---

## 6. 実装タスク一覧

## 6.1. Phase 1. first-case concrete wrapper を追加

追加対象

* `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete`

検証

* `#print axioms ...firstCase_concrete`
* `lake build DkMath.FLT...`

成功条件

* no-sorry
* existing assumptions のみで閉じる

## 6.2. Phase 2. 旧本体に case split を導入

修正対象

* `FLTPrimeGe5Target_of_kummerRoute`

作業

* first-case 分岐を新 wrapper へ差し替え
* non-first-case は legacy のまま

検証

* `#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute`

期待

* `uses sorry` が残っても、first-case 起因の依存が消える

## 6.3. Phase 3. legacy principalization wrapper の分解

対象

* `cyclotomicPrincipalization_of_classGroupPTorsionFree`
* その周辺 one-shot theorem

作業

* split architecture ベースの薄い wrapper 群を追加
* 旧 theorem を徐々に置換

---

## 7. 成功判定

この差し替え設計の成功判定は明確じゃ。

### 7.1. 局所成功

`fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` が no-sorry で build すること。

### 7.2. 中間成功

`FLTPrimeGe5Target_of_kummerRoute` の `uses sorry` が減る、または少なくとも **残る `sorry` の責任範囲が non-first-case / legacy に限定される** こと。

### 7.3. 最終成功

first-case specialization に由来する `sorry` が legacy chain から消え、残件一覧が

* non-first-case
* class-group legacy wrapper
* research files

に整理されること。

---

## 8. リスク

### 8.1. 旧 theorem の引数が肥大していて、first-case 枝の抽出だけでも型合わせが重い

対策として、まずは theorem を「完全抽出」せず、旧 proof 中の first-case 部分をローカル `have` で切り、そのあと独立 theorem へ持ち上げるのがよい。

### 8.2. `hgap_eq`, `hLinNe`, `hProduct` の入手元が旧ルートの深い場所にあり、case split 後に再配線が要る

これはありうる。
その場合は「first-case contradiction wrapper」を直接呼ぶのでなく、その入力をまとめた小さな `FirstCaseConcreteInput` 的 lemma を 1 本置くとよい。

---

## 9. 最終提案指示

よって、次の号令はこれじゃ。

1. `FLTPrimeGe5Target_of_kummerRoute` の first-case 枝だけを抽出した
   `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` を追加せよ。
2. それを使って旧本体へ case split を導入し、first-case 側を concrete wrapper 群へ差し替えよ。
3. その後 `#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute` を再監視し、
   `uses sorry` の責任範囲が non-first-case / legacy に縮んだか確認せよ。
4. 次段として `cyclotomicPrincipalization_of_classGroupPTorsionFree` を同様に薄い split wrapper 群へ寄せよ。

ひとことで言えば、

$$
\text{次は数学を掘るのではなく、旧配線を concrete first-case route へ差し替える戦じゃ。}
$$

必要なら次に、その `fltPrimeGe5Target_of_kummerRoute_firstCase_concrete` と case split 本体の Lean 雛形を、そのまま貼れる形で起こすぞい。
