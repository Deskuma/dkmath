# FLT-Kummer-Bridge 045: first-case concrete mainline はもう product-free で通ると見てよい

うむ、じっくり読んだ。
今回の長い流れ、かなり美しい収束をしておる。結論から言うと、**first-case の concrete mainline は、ついに本質的に `hProduct` から自由になった** と見てよい。いまの主戦場は、もはや first-case の証明本体ではなく、**legacy one-shot / class-group route へこの product-free chain をどう注入するか** じゃ。

## 1. 戦況の大局

流れを一本の筋として読むと、こうじゃ。

最初は、first-case の Stage 3 を concrete に閉じることが主戦場だった。そこから `NormEqGN` と `UnitAbsorb` を分離し、さらに norm 側を product・Galois・units・GN への橋へ刻んで concrete 化した。加えて natAbs 主導の整数補題で unit 吸収を閉じ、first-case の Stage 3 自体は concrete になった。そこまでは、前の会話でも見えておった戦果じゃ。

その後の本当の見どころは、**`hProduct` をどこまで押し出せるか** に話が移ったことじゃ。最初は `hProduct` が Stage 3 の norm/GN chain に必要と思われていたが、direct norm-eval route により chosen factor の整数 norm が **full product identity なし** で直接 (GN,p,(z-y),y) に一致すると示せた。この段階で `CyclotomicNormEqGNFirstCasePackThinTarget` は interface レベルでも `hProduct`-free になった。さらに concrete theorem を見直すと `UnitAbsorb` も実は `hProduct` を使っておらず、こちらも interface から外れた。これで Stage 3 中核 2 target はどちらも `hProduct`-free になった。

次に unit-normalization chain 側を dependency 分解して、coprime leg は product-free と確定した。さらに責務 A を isolated receiver に切り出し、local factorization core から tail-sum ideal × chosen factor ideal (=,(x)^p) という product-free ideal-equality 候補を立てた。最後に、tail-sum ideal と chosen factor ideal の coprimality bridge まで product-free に閉じたことで、`chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_withoutProduct`、`cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin_withoutProduct`、`cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct` が揃い、そこから Stage 3 の power wrapper と contradiction wrapper からも `hProduct` を外せた。これで **Stage 1 / Stage 2 / Stage 3 の first-case concrete chain 全体が、実質 hProduct-free** になったと読んでよい。

この推移はかなり重要じゃ。単に theorem が増えたのではない。
**証明の本質依存が、full product identity から local tailsum route へ置き換わった** のじゃ。

## 2. 今どこが勝ちで、どこが残敵か

### 2.1. もう勝った場所

first-case の concrete chain は、いまやこう読める。

$$
\text{local factorization}
\to
\text{tailsum ideal × chosen ideal = }(x)^p
\to
\text{coprimality bridge}
\to
\text{chosen ideal = }p\text{ 乗 ideal}
\to
z-\zeta y = u\cdot\beta^p
\to
\operatorname{Norm}(z-\zeta y)=GN
\to
GN=s^p
\to
\text{contradiction}
$$

この鎖は no-sorry で揃っておる。
しかも途中で `hProduct` をもう要求しておらぬ。
だから、first-case に関しては「理論が足りない」のではなく、**もう mainline がある** と言ってよい。

### 2.2. 残っている敵

残敵は、もはや first-case chain そのものではない。
主に次の 2 つじゃ。

1. `cyclotomicPrincipalization_of_classGroupPTorsionFree` のような **legacy one-shot wrapper**
2. `FLTPrimeGe5Target_of_kummerRoute` 側の **downstream routing / case split の未整理**

つまり、いま残っている `sorry` は「first-case をどう証明するか」ではなく、**既存の old architecture が新しい product-free chain をまだ呼んでいない** ことに由来しておる。今回の報告でも、残る warning は既知の `CyclotomicPrincipalization.lean` の legacy `sorry` と研究用ファイル側だけ、と何度も確認されておる。

## 3. この長戦で最も大きな発見

わっちが見るに、今回の一連のログでいちばん大きかったのは、
**「`hProduct` が必要な証明」ではなく、「`hProduct` を使っていたのは旧 route の設計」だった** と確定したことじゃ。

前はこう見えておった。

$$
\text{full product identity}
\Longrightarrow
\text{first-case chain}
$$

だが、今は違う。

$$
\text{local tailsum factorization}
\Longrightarrow
\text{first-case chain}
$$

でよい、と theorem-level に固定できた。
full product identity は、少なくとも current first-case concrete mainline の本質ではない。ここを確定できたのは、かなり大きい。

## 4. 次の戦略

ここからは、数学の本丸を掘るより **route の外科手術** じゃ。
筋のよい順に言うぞい。

### 4.1. 最優先

`cyclotomicPrincipalization_of_classGroupPTorsionFree` を first-case / それ以外に分解し、first-case 枝を **product-free chain に直結** させる。

これが第一手じゃ。
理由は単純で、いまの logs では first-case mainline が既に勝っている。
ならば old one-shot wrapper の中で first-case を抱え続ける理由はない。

作業の思想はこうじゃ。

* まず theorem 本体を責務で二分する
* first-case 枝では `cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct` あるいは、その downstream contradiction wrapper 群を直接呼ぶ
* non-first-case 側だけを legacy として残す

こうすると、残る `sorry` の責任範囲が first-case から完全に退く。

### 4.2. 次点

`FLTPrimeGe5Target_of_kummerRoute` を case split 化し、first-case 枝を current stable bridge へ差し替える。

ここで大事なのは、route ファイル側に無理に alias を置くのでなく、**universe が安定している `CyclotomicPrincipalization.lean` 側の stable theorem を直接呼ぶ** ことじゃ。route-level alias は一度試して崩れた、という観測が既にあるからな。ここは過去の失敗から学ぶべき局面じゃ。

### 4.3. 後回しでよいもの

global full product identity の canonical supply theorem。
ここはもう、今すぐ掘る優先度はかなり下がった。
なぜなら current first-case mainline は product-free で通っておるからじゃ。
ここを先にやるのは、勝った前線へ追加兵を送るようなものじゃ。

## 5. 実務的な提案指示

わっちなら、次のように指示する。

### 指示 A. first-case 抽出

`cyclotomicPrincipalization_of_classGroupPTorsionFree` の proof を読み、
first-case 判定 `¬ p ∣ gap` を境に proof body を 2 つへ割る。

### 指示 B. first-case 差し替え

first-case 枝では old `hProduct` 依存 chain を呼ばず、

* `chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack` で `hLinNe` を supply するのか、あるいは既に pack から得るのか整理しつつ
* `cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct`
* `cyclotomicNormGNPower_concrete_firstCase_packThin`
* `false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree`

など current stable bridge 群へ直結させる

という導線に変える。

### 指示 C. 責任範囲の観測

その差し替え後に

* `#print axioms DkMath.FLT.cyclotomicPrincipalization_of_classGroupPTorsionFree`
* `#print axioms DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute`

を再監視し、`uses sorry` がまだ残るとしても、それが non-first-case / legacy 側だけに縮んだかを見る。

### 指示 D. もし崩れるなら

もし one-shot wrapper の内部で型や universe が暴れるなら、いきなり本体を書き換えず、

* `..._firstCase_withoutProduct`
* `..._nonFirstCase_legacy`

の 2 theorem に分離してから本体を合成する。

これが一番安全じゃ。

## 6. いまの見立ての一言要約

ひとことで言えば、こうじゃ。

$$
\boxed{
\text{first-case はもう証明する対象ではなく、legacy route へ注入すべき完成部品になった}
}
$$

だから次にやるべきは、新しい数学ではない。
**old route の first-case 枝を、この完成部品へ載せ替えること** じゃ。

## 7. 最終提案

賢狼の最終提案指示はこれじゃ。

1. `cyclotomicPrincipalization_of_classGroupPTorsionFree` を責務単位で first-case / non-first-case に分けよ。
2. first-case 枝は `...withoutProduct` 系の stable theorem 群へ差し替えよ。
3. その後 `FLTPrimeGe5Target_of_kummerRoute` にも同じ split を入れ、first-case を stable bridge へ直結せよ。
4. 再度 `#print axioms` で監視し、残る `sorry` の責任範囲が truly legacy のみになったか確認せよ。

😏 いまの盤面、かなり勝ち筋が見えておる。
ここからは「証明を生む戦」より、「勝った証明を旧王国へ輸血する戦」じゃよ。

必要なら次に、`cyclotomicPrincipalization_of_classGroupPTorsionFree` を case split 化するための Lean 雛形を、そのまま貼れる形で起こすぞい。

---

うむ、起こすぞい。
いまの流れからすると、狙いは **`cyclotomicPrincipalization_of_classGroupPTorsionFree` を first-case / non-first-case に割り、first-case 側を current の product-free chain へ差し替える雛形** じゃな。first-case の concrete chain はすでに `hProduct` を本質的に追放できており、残りは legacy route への注入戦だ、という整理でよい。

以下、**そのまま貼って整える用の Lean 雛形** を出す。
実際の引数列は現物の theorem 宣言に合わせて微調整が要るが、**分割の骨格** はこれでよいはずじゃ。

```lean id="55424"
/-
  Sketch:
  cyclotomicPrincipalization_of_classGroupPTorsionFree を
  first-case / non-first-case に責務分解するための雛形。

  方針:
  1. first-case branch だけを独立 theorem に切り出す
  2. そこでは old hProduct-based chain を呼ばず、
     current product-free chain / stable bridge を直接使う
  3. 本体 theorem は by_cases で 2 分岐するだけの薄い合成にする
-/

namespace DkMath.FLT

open scoped BigOperators

/--
first-case (`¬ p ∣ gap`) 専用の principalization / contradiction branch 雛形。

ここでは old one-shot chain を通らず、
current product-free chain を直接使う。
-/
theorem cyclotomicPrincipalization_firstCase_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
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
        -- ここは現物 signature に合わせて残す/削る
        -- もし hLinNe を pack or productEq から supply 済みなら簡約してよい
        (hLinNe :
          ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
            (hζ := hζ) (y := y) (z := z)) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe
  exact
    false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree
      (hCl := hCl) (hNoPow := hNoPow)
      (K := K) (p := p) (x := x) (y := y) (z := z) (ζ := ζ) (gap := gap)
      hζ hpack hgap_eq hFirstCase hLinNe


/--
first-case 用の descent witness を返す雛形。

もし downstream が `False` ではなく
`∃ g'` 型の branch target を要求するなら、こちらを差し込む。
-/
theorem qAdicGapReduction_firstCase_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z q : ℕ}
        [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      (hpack : PrimeGe5CounterexamplePack p x y z) →
      ∀ {gap : ℕ},
        (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K)) →
        (hFirstCase : ¬ p ∣ gap) →
        (hLinNe :
          ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
            (hζ := hζ) (y := y) (z := z)) →
        ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p := by
  intro K _ _ _ p x y z q _ _ hq hqx hqne hqgap ζ hζ hpack gap hgap_eq hFirstCase hLinNe
  exact
    qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree
      (hCl := hCl) (hNoPow := hNoPow)
      (K := K) (p := p) (x := x) (y := y) (z := z) (q := q) (ζ := ζ) (gap := gap)
      hq hqx hqne hqgap hζ hpack hgap_eq hFirstCase hLinNe


/--
non-first-case (`p ∣ gap`) 側の legacy placeholder。

まずは既存 route をそのまま呼ぶ薄い wrapper にして、
責任範囲をこちらへ閉じ込める。
-/
theorem cyclotomicPrincipalization_nonFirstCase_legacy
    -- 実際の existing assumptions をそのまま並べる
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      (hpack : PrimeGe5CounterexamplePack p x y z) →
      ∀ {gap : ℕ},
        (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K)) →
        (hNonFirstCase : p ∣ gap) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hNonFirstCase
  -- ここは既存 legacy theorem 呼び出しへ差し替える
  -- exact old_non_first_case_route ...
  sorry


/--
case split 後の本体雛形。

first-case は stable theorem 群へ、
non-first-case はひとまず legacy wrapper へ送る。
-/
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree_split
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      (hpack : PrimeGe5CounterexamplePack p x y z) →
      ∀ {gap : ℕ},
        (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K)) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq
  by_cases hFirstCase : ¬ p ∣ gap
  ·
    -- 供給の仕方は現物に合わせて 2 通りある。
    -- 1. すでに hLinNe が別補題で得られるならそれを使う
    -- 2. もし productEq-only 版がもう十分なら、その版を呼ぶ
    have hLinNe :
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
          (hζ := hζ) (y := y) (z := z) := by
      -- ここは現状の mainline 供給方法に合わせて埋める
      -- exact ...
      sorry
    exact
      cyclotomicPrincipalization_firstCase_of_classGroupPTorsionFree
        (hCl := hCl) (hNoPow := hNoPow)
        (K := K) (p := p) (x := x) (y := y) (z := z) (ζ := ζ) (gap := gap)
        hζ hpack hgap_eq hFirstCase hLinNe
  ·
    exact
      cyclotomicPrincipalization_nonFirstCase_legacy
        (hCl := hCl) (hNoLift := hNoLift)
        (K := K) (p := p) (x := x) (y := y) (z := z) (ζ := ζ) (gap := gap)
        hζ hpack hgap_eq (by exact not_not.mp hFirstCase)

end DkMath.FLT
```

これをさらに **実戦用** に寄せるなら、次の 2 点が大事じゃ。

まず、first-case 枝はもう `hProduct` ベースで書かぬことじゃ。
今回の流れでは、first-case concrete chain は local tailsum route で Stage 1 / Stage 2 / Stage 3 まで実質 `hProduct`-free になっておる。したがって first-case 用 wrapper は、`...withoutProduct` 系や stable contradiction bridge を直に呼ぶ形へ寄せるのが正しい。

次に、`hLinNe` の供給だけは現物に合わせて選ぶことじゃ。
ログ上では `hLinNe` 自体も productEq から供給できる補題が立っておるが、first-case local tailsum route の current mainline でどの theorem を入口にするかは、今のファイルの実シグネチャに合わせて決めた方が安全じゃ。`chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack` を使う形でもよいし、すでにもっと上流から得ているならそれを通してよい。

わっちの見立てでは、次の一手はこれじゃ。

1. まず `cyclotomicPrincipalization_firstCase_of_classGroupPTorsionFree` を **no-sorry** で立てる。
2. 次に `cyclotomicPrincipalization_of_classGroupPTorsionFree_split` の first-case 枝へそれを差し込む。
3. 最後に `#print axioms` で、本体の `uses sorry` が non-first-case 側へ局所化されたかを見る。

必要なら次に、これを **今の theorem 名へもっとぴったり合わせた版** に縮めて書き直すぞい。
