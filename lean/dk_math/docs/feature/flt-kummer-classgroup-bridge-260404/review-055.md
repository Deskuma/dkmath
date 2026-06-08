# 状況

わっちの見立てでは、いまの戦況は「数学の敗走」ではなく、「敵の本陣がどこかを正確に突き止めた局面」じゃ。前回の認識ミスは、`direct sorry` が消えたことをそのまま `no-sorry` と読んでしまった点にあり、実際には `triominoCosmicNoPowOnGN_default` 経由で `sorryAx` が伝染しておった。つまり壊れたのは定理の骨格ではなく、信頼分類のラベルじゃ。報告でも、設計・構造の進捗は前進、信頼・公理依存の進捗は再分類が必要、という二層読みが示されておる。

そのうえで、今回の差分の本当の成果はかなり大きい。commit `73b9891e...` でやったことは、Kummer local をさらに薄く刻むことではなく、research debt を `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget` という 1 本の抽象 target に圧縮し、そこから `NoWieferich bridge`、`WieferichDescentB`、`TriominoWieferichBranchBridge`、`NoPowOnGN`、`BodyInvariant` まで clean glue で戻れると定理名で固定したことじゃ。しかも新設 theorem 群は `#print axioms` で `sorryAx` なし、関連 build も通っておる。これは「証明完了」ではないが、「未解決箇所の境界面」を美しく切り出した、かなり質の高い前進じゃ。

そして、資料庫の地図と照らすと、この変化は本丸の地形と一致しておる。INDEX では FLT 幹線の中核を `ZsigmondyCyclotomic` 系の原始素因子エンジンと p-adic valuation ブロックに置いており、まさに `squarefree_implies_padic_val_le_one` と `padicValNat_primitive_prime_factor_le_one` がその中心に載っておる。ゆえに今回の問題は支線の事故ではなく、FLT 本線の心臓部が Kummer 側へ顔を出したものじゃ。言い換えると、Kummer 側で起きたように見えるが、実体は Zsigmondy / valuation 側の debt が表面化しただけ、ということじゃな。

ゆえに、現状評価はこうなる。
構造面では前進。
信頼面では横ばい、ただし可視化は大前進。
数学内容そのものは、まだ root を倒しておらぬ。
つまり、進軍方向は当たっておるが、まだ城門を破ったわけではない。

次の戦略は、わっちはかなりはっきりしておる。主戦略は upstream root 攻略じゃ。今回の報告どおり、`triominoCosmicNoPowOnGN_default` の上流、特に `triominoWieferichBranchBridge_default` から `padicValNat_primitive_prime_factor_le_one`、さらに direct source の `squarefree_implies_padic_val_le_one` へ降りていく鎖を叩くべきじゃ。local receiver をさらに薄くしても、上流が濁っておる限り Stage 3 群は via-sorry のままじゃからの。

具体的には、次の順で攻めるのがよい。

まず第一に、`padicValNat_primitive_prime_factor_le_one` を使わずに済む既存 clean route が current Branch B 文脈に乗るかを最優先で検査することじゃ。今回の差分自身も、その候補として `..._of_squarefree_GN` / no-lift provider の再点検を挙げておる。ここで置換できれば、一番美しい。Kummer 側はほとんど触らず、上流 1 箇所の差し替えで芋づる式に clean 化が戻る可能性が高い。

次に、もしその置換が無理なら、`ZsigmondyCyclotomicResearch` 側の statement repair を本命に据えるべきじゃ。ここは「証明を埋める」のではなく、「命題を真に直す」局面じゃ。スナップショットを見ると、この周辺にはすでに “より強い仮定つきなら honest に通る” 方向の補題がある。ならば public wrapper が弱すぎる偽の一般形に寄りかかるのをやめ、必要仮定を表に出す設計へ切り替えるのが筋じゃ。これで debt の形が数学的にも Lean 的にも揃う。

さらに実務上は、main branch と side branch を分けるのがよい。main branch では upstream repair に集中し、side branch では Kummer local の wrapper 整理だけを続ける。そうすれば、設計 progress と trust progress を混ぜずに済む。今回の失点は分類ミスじゃから、ここを混ぜるとまた見かけの前進に騙されやすい。

わっちの最終判定を一言で言えばこうじゃ。

いまは 「後退」 ではない。
「敵将の居場所が確定した」 段じゃ。

よって次の一手は、`CyclotomicPrincipalization` をさらに削ることではなく、`ZsigmondyCyclotomicResearch` 側の valuation 命題を honest にするか、そこを clean theorem で置換すること。そこが通れば、今回 via-sorry に戻した Kummer Stage 3 群はまとめて救われる見込みが高い。

# 今後の方針

うむ、スナップショットを展開し、差分もコード側だけ仮適用して追ってみたぞい。
結論から言うと、 **差し替え可能な経路はある** 。ただし二種類ある。

ひとつは、 **いま即座に差し替えられる配線ミス修正** 。
もうひとつは、 **既存の honest 仮定から新 target へ落とすアダプタ追加** じゃ。
逆に、 **無条件で root を埋める concrete provider は、現スナップショット上ではまだ見当たらぬ** 。

## 1. 結論

今回の差分で導入した

$$
\texttt{TriominoPrimitivePrimeFactorPadicValNatLeOneTarget}
$$

は、空中に浮いた target ではなく、既存資産から接続できる。
少なくとも次の 3 本の入力から流し込める見込みがある。

1. `TriominoSquarefreeGNBridge`
2. `TriominoNoLiftGNBridge`
3. `TriominoCosmicNonLiftableGNBridge`

ただし、1 と 2 は **concrete provider がまだ無い**。
3 は Kummer first-case 側で既に仮定として受けておる箇所があり、そこは **すぐ修正可能** じゃ。

## 2. いま即差し替え可能な箇所

いちばん美味しい発見はこれじゃ。

`CyclotomicPrincipalization.lean` の

* `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit`

この 2 本、 **`hNoLift` を受け取っているのに実際には使っておらん** 。

現コードは `_hNoLift` を捨てて、

$$
\texttt{cyclotomicPrincipalizationFirstCase\_of\_classGroupPTorsionFree}
$$

へそのまま流しておる。
つまり、せっかくある non-liftable route を使わず、default route に戻っておるのじゃ。

しかも同じファイルには、もう既に

$$
\texttt{qAdicGapReductionGapDivisible\_of\_firstCase\_of\_classGroupPTorsionFree\_and\_nonLiftable}
$$

があり、こちらは名前どおり `hNoLift` をちゃんと受ける。
ゆえに first-case wrapper は、低リスクでこちらへ差し替えられる。

これはかなり重要じゃ。
なぜなら、 **Kummer first-case の `_and_nonLiftable` ルートだけは、今すぐ default 汚染を避けられる** からじゃ。

実質こう直せるはずじゃ。

```lean
theorem cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
  (hNoLift : TriominoCosmicNonLiftableGNBridge) :
  CyclotomicPrincipalizationFirstCaseTarget := by
  intro p x y z hpack q hq hqx hqne hqgap hFirstCase
  let _ : Fact p.Prime := ⟨hpack.hp⟩
  let ζ : CyclotomicField p ℚ :=
    IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)
  have hζ : IsPrimitiveRoot ζ p := by
    simp [ζ]
  have hgap_eq :
      (z : 𝓞 (CyclotomicField p ℚ)) - (y : 𝓞 (CyclotomicField p ℚ)) =
        ((z - y : ℕ) : 𝓞 (CyclotomicField p ℚ)) := by
    simp [Nat.cast_sub hpack.hyz]
  exact
    qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable
      (hCl := hCl) (hNoLift := hNoLift)
      (K := CyclotomicField p ℚ) (p := p) (x := x) (y := y) (z := z) (q := q)
      (ζ := ζ) (gap := z - y)
      hq hqx hqne hqgap hζ hpack hgap_eq hFirstCase
```

そして

$$
\texttt{cyclotomicPrincipalization\_of\_classGroupPTorsionFree\_of\_caseSplit}
$$

も first-case 側にこれを使うよう差し替えられる。
ここは **今すぐやる価値が高い** 。

## 3. 差分後 target に接続できる既存 honest route

### 3.1. `TriominoSquarefreeGNBridge` から target へ

これはかなり素直じゃ。

既に `CosmicPetalBridgeGNNoWieferich.lean` に

$$
\texttt{triominoWieferichShrinkKernelEqSeedTracePackB\_kernel\_padicValNat\_diff\_le\_one\_of\_squarefree\_GN\_core}
$$

がある。
これはまさに

$$
\text{Squarefree}(GN) \Rightarrow v_q(z^p-y^p)\le 1
$$

の honest 版じゃ。

したがって、差分で導入した target には、こんな薄いアダプタを足せる。

```lean
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
    (hSq : TriominoSquarefreeGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
  exact
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core
      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
      (hSq hpack hpB hqP hq_dvd_diff hq_not_dvd_gap)
```

つまり、 **squarefree bridge が concrete に供給できるなら、新 target は既存定理だけで埋まる** 。

### 3.2. `TriominoNoLiftGNBridge` から target へ

これも行ける。しかも squarefree より弱い。

必要部品はもう揃っておる。

* `triominoWieferichShrink_padicValNat_diff_eq_GN_core`
* `triominoWieferichShrink_GN_ne_zero_core`
* `NoLift(q,X) := ¬ q^2 ∣ X`

あとは

$$
\neg q^2 \mid N,; N \neq 0 \Rightarrow v_q(N)\le 1
$$

をその場で 7 行ほど書けばよい。`FLT.Basic` には private 版 `padicValNat_le_one_of_noLift` も既にあるので、内容は既知じゃ。

ゆえに

```lean
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
    (hNoLift : TriominoNoLiftGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  ...
```

は十分現実的じゃ。
これは **新 target の最も自然な honest 受け口** じゃな。

### 3.3. `TriominoCosmicNonLiftableGNBridge` から target へ

これも行ける。しかも Kummer 側では既に `hNoLift` を持つ route がある。

`TriominoCosmicNonLiftableGNBridge` は

$$
\text{PrimitiveOnGN}(p,u,y,q)\Rightarrow \neg q^2 \mid GN(p,u,y)
$$

を全原始素因子について与える。
一方、いまの target は

$$
q \mid z^p-y^p,\quad q\nmid(z-y)
$$

という primitive-prime branch の入力を受ける。
このとき `dvd_GN_of_dvd_sub_pow` で \(q \mid GN\) に戻せるので、`PrimitiveOnGN` が立つ。そこで nonliftable から \( \neg q^2 \mid GN \) を得て、前項と同じ valuation 上界へ行ける。

つまり、

```lean
theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_nonLiftableGNBridge
    (hBridge : TriominoCosmicNonLiftableGNBridge) :
    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
  ...
```

も作れる。

ただし、 **Kummer first-case 側ではこれは作らなくてもよい** 。
なぜなら、その側は既に `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable` という、target を経由しない直通路を持っておるからじゃ。

## 4. まだ差し替え不能なもの

ここははっきり言うぞい。

**無条件で `TriominoPrimitivePrimeFactorPadicValNatLeOneTarget` を concrete に埋める route は、現スナップショット上ではまだ見つからぬ。**

とくに、

* `TriominoSquarefreeGNBridgeProviderImplTarget`
* `TriominoNoLiftGNBridgeProviderImplTarget`

は、器はあるが concrete constructor が見当たらん。
`TriominoSquarefreeGNBridgeProviderImpl.lean` は **供給者の型を固定しているだけ** で、本体実装ではない。

この点は work notes の記述とも一致しておる。
つまり差分が言っておる

$$
\text{「concrete provider を供給するか、descent 入口を parameterize するか」}
$$

という見立ては正しい。
今回の diff は、そのうち後者をきれいにやった形じゃ。

## 5. 戦略評価

わっちの判断では、次の優先順位がよい。

### 5.1. 第一優先

**Kummer first-case wrapper の配線修正**

* `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_nonLiftable`
* `cyclotomicPrincipalization_of_classGroupPTorsionFree_of_caseSplit`

この 2 本で `hNoLift` をちゃんと使うように直す。
これは最小差分で効果が大きい。

### 5.2. 第二優先

**新 target への honest adapter を 2 本追加**

* `_of_squarefreeGNBridge`
* `_of_noLiftGNBridge`

この 2 本があると、diff で作った target は「単なる分析用仮定」ではなく、既存 honest interface を受ける正式 landing point になる。

### 5.3. 第三優先

**具体的 provider の探索**

これはまだ open じゃ。
ただ、これを探す前に adapter 群を置いておくと、今後の concrete provider 候補が見つかった時に、差し込む先が 1 本に固定される。ここが美しい。

## 6. まとめ

戦況としてはこうじゃ。

* **即修正可能な配線ミス** が 1 本ある

  * Kummer first-case の `_and_nonLiftable` wrapper が `hNoLift` を捨てておる
* **差分後 target に既存 honest route を接続する道** は 3 本ある

  * `SquarefreeGNBridge`
  * `NoLiftGNBridge`
  * `NonLiftableGNBridge`
* **ただし concrete provider はまだ無い**

  * ここは依然として open

ゆえに、いま打つべき一手は
**「target を埋める新数学」より先に、既存 honest bridge を target へ落とす adapter と、Kummer wrapper の配線修正」**
じゃよ。
