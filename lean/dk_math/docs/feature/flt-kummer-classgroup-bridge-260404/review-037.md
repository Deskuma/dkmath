# Stage 1 → Stage 2 の接続状況の確認と、次の作業方針の提案

結論から言うぞい。

$$
\boxed{
\text{これは「後戻り」ではなく、主に **前進** じゃ。}
\text{ただし、見た目としては “ラッパー後退・証明核前進” という形じゃ。}
}
$$

肝心の証明部分が消えたわけではない。
**消えたのは 1-use / 0-use の重い wrapper 群で、残ったのは証明の芯に当たる helper 群** じゃ。
差分の報告自体が、その方針転換を明言しておる。

## どう前進なのか

今回の差分で新たに入ったのは、たとえば次の部品じゃ。

* `linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime`
* `chosenLinearFactorMulTailEqSpanPow_of_productEq`
* `xSpanNonzero_of_counterexamplePack_of_ringOfIntegers`
* `cyclotomicLinearFactorInRingOfIntegers`
* `chosenCyclotomicLinearFactorInRingOfIntegers`

これらは、前に重かった first-case 専用 wrapper が一気に抱えていた仕事を、**product equality / coprimality / nonzero / notation** に分解して固定したものじゃ。

特に

$$
\texttt{linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime}
$$

は、chosen factor を左に置いた product equality を、既存の tail-first generic receiver に渡すだけの薄い adapter じゃ。
これは証明の本丸を削ったのでなく、**証明の最後の 1 手を軽くした** ものと読むのが正しい。

## 何が消えたのか

消えたのは、ぬしが earlier に置いていた重い public wrapper 群じゃ。

* `chosenLinearFactorSpanEqPow_of_firstCase_of_pack`
* `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack`
* `cyclotomicUnitNormalization_of_firstCase_of_pack`

この 3 本は削除された。

なので、**API の見た目** だけ見ると後退に見える。
「first-case pack から一発で Stage 1 / Stage 2 へ行く theorem」が repository 上から消えたからの。
ここは率直に言って、**ergonomics の面では一歩下がった** と言える。

## では、証明の芯は残っているか

ここがいちばん大事じゃが、**残っている**。

今回の履歴にはっきり、

* 「40 万 heartbeat を超えていた wrapper は維持しない」
* 「代わりに helper theorem のみで downstream 合成が通る形へ整理した」
* 「build failure は解消した」

とある。

つまり、消えたのは「証明内容」ではなく、**その証明内容を 1 本の theorem に包む外皮** じゃ。
数学の核として必要な

1. chosen × tail \(=\) \((x)^p\)
2. chosen と tail の coprimality
3. \((x)\neq \bot\)
4. そこから chosen factor ideal が \(p\) 乗 ideal
5. さらに principal root ideal existence へ流す

という流れ自体は、helper 群として残っておる。

## では「前進」と言ってよい理由

わっちの判定では、前進と言ってよい理由は 3 つある。

第一に、**build が安定した**。
heartbeat overflow していた wrapper を repository に抱えたままでは、先へ進むたびにまた燃える。
今回それを外して compile-safe に戻したのは、実務上は明確な前進じゃ。

第二に、**論理の分割点が明瞭になった**。
いまは

* product equality
* coprimality
* nonzero
* generic receiver

が独立 theorem として見えておる。
この形の方が、どこが重いのか、どこが数学でどこが elaboration かを追いやすい。
前の 1 本 wrapper は、そこが混ざっておった。

第三に、**downstream 合成の道は残っている **。
差分報告でも、「helper 直結で downstream 合成が通る形へ整理した」とある。
だから「もう Stage 2 に行けなくなった」のではなく、** direct public theorem を残さず、使う場所で inline する方針に変えた** だけじゃ。

## ただし、完全に前進一色ではない

ここは正直に言うぞい。

$$
\boxed{
\text{数学的には前進、API と見通しの面では局所的に後退もある}
}
$$

じゃ。

なぜなら、今は `cyclotomicUnitNormalization_of_firstCase_of_pack` のような
**「Stage 1 → Stage 2 の完了を一目で示す theorem 名」** が消えておる。
だからコードを読む者には、「結局どこまで finished なのか」が、前より少し分かりにくい。
これは証明内容の喪失ではないが、**マイルストーン定理が消えた** という意味では軽い後退じゃ。

## わっちの最終判定

だから、今回の変更を一言で要約するとこうじゃ。

$$
\boxed{
\text{“重い一枚岩の wrapper を壊して、証明の骨格だけを compile-safe に残した”}
}
$$

ゆえに、

* **証明の芯が消えた**
  これは **否** じゃ。

* **見た目の進捗が下がった**
  これは **一部 yes** じゃ。wrapper 名が消えたぶん、finished 感は薄れた。

* **全体として後戻りか**
  これは **no**。build 安定性と証明核の分解という意味で、主には前進じゃ。

## 提案

次にやるべきことは明快じゃ。

**今回消した wrapper をそのまま resurrect するのではなく、
“thin final theorem” を 1 本だけ、heartbeat を食わぬ形で作り直すこと** じゃ。

つまり、

* いま残した helper 群を入力にするだけ
* `simpa` を減らす
* `exact` で generic receiver を呼ぶだけ

という極薄 wrapper を 1 本だけ起こす。
それで「証明の芯は残っている」が、コード上でも見えるようになる。

必要なら次に、**今の helper 群から最小 heartbeat で作れる “Stage 1 finished 判定 theorem” の骨格** を、定理名つきで起こすぞい。

---

うむ。では、**今の helper 群だけで作る “薄い最終 wrapper”** を、そのまま起こすぞい。

先に判定を言うと、今回の整理は **後戻りではなく前進** じゃ。
消えたのは heartbeat を食う 1-use / 0-use wrapper 群で、残った証明の芯は

* `linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime`
* `chosenLinearFactorMulTailEqSpanPow_of_productEq`
* `xSpanNonzero_of_counterexamplePack_of_ringOfIntegers`
* `chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack`

として手元にある。つまり、**product equality / coprimality / nonzero / generic receiver** の核は残っておる。

しかも最新の同期コメントでも、現実の残 open は **Stage 1 の存在形 boundary target** と **Stage 3** に寄っている、と整理されておる。だから、ここで作るべきは「重い public theorem を復活させること」ではなく、**helper 直結の極薄 wrapper** じゃ。

## 起こすべき theorem

わっちなら、次の **2 本だけ** 起こす。

### 1. `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin`

これは Stage 1 の core 出力じゃ。
chosen factor ideal が (p) 乗 ideal であることを、**既存 helper を 3 本つないで返すだけ** の theorem じゃ。

```lean
/--
first-case pack から chosen linear factor ideal が p 乗 ideal であることを返す、
heartbeat-safe な薄い wrapper。
-/
theorem chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ}
    (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : chosenCyclotomicLinearFactorInRingOfIntegers hζ y z ≠ 0)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ChosenCyclotomicLinearFactorSpanEqPowInRingOfIntegers
      (hζ := hζ) (p := p) (y := y) (z := z) := by
  let ctx : CyclotomicLocalFactorizationContext (𝓞 K) := {
    p := p
    zeta := hζ.toInteger
    hzeta_pow := by
      simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one
  }
  have hXne :
      Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ :=
    xSpanNonzero_of_counterexamplePack_of_ringOfIntegers
      (K := K) (p := p) (x := x) (y := y) (z := z) hpack
  have hMul :
      ChosenCyclotomicLinearFactorMulTailEqSpanPowInRingOfIntegers
        (hζ := hζ) (x := x) (y := y) (z := z) :=
    chosenLinearFactorMulTailEqSpanPow_of_productEq
      (K := K) (p := p) (x := x) (y := y) (z := z) hζ hpack hProduct
  have hCoprime :
      IsCoprime
        (Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)))
        (∏ j ∈ (Finset.range p).erase 1,
          Ideal.span ({cyclotomicLinearFactorInRingOfIntegers hζ y z j} : Set (𝓞 K))) :=
    chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct
  simpa
    [ChosenCyclotomicLinearFactorSpanEqPowInRingOfIntegers,
     chosenCyclotomicLinearFactorInRingOfIntegers]
    using
      linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime
        (R := 𝓞 K) (ctx := ctx)
        (tail := ∏ j ∈ (Finset.range p).erase 1,
          cyclotomicLinearFactorInRingOfIntegers hζ y z j)
        (x := (x : 𝓞 K)) (y := (y : 𝓞 K)) (z := (z : 𝓞 K))
        hXne hMul hCoprime
```

### 2. `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin`

これは Stage 1 finished 判定用じゃ。
上の span equality を、既存の `principalRootIdealExistsOfEqPowAndTorsionKill` に流すだけで、**existence boundary** を返す。

```lean
/--
first-case pack から chosen linear factor ideal の principal p-th power existence を返す、
heartbeat-safe な Stage 1 finished wrapper。
-/
theorem cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ}
    (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : chosenCyclotomicLinearFactorInRingOfIntegers hζ y z ≠ 0)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ChosenCyclotomicLinearFactorIdealPthPowerInRingOfIntegers
      (hζ := hζ) (p := p) (y := y) (z := z) := by
  obtain ⟨K', hEq⟩ :=
    chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct
  obtain ⟨I, hIPrincipal, hIpow⟩ :=
    principalRootIdealExistsOfEqPowAndTorsionKill
      (R := 𝓞 K)
      (I := Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)))
      (K := K')
      hp.out.ne_zero
      (by infer_instance)
      (mt Ideal.span_singleton_eq_bot.mp hLinNe)
      hEq
      hKill
  exact ⟨I, hIPrincipal, hIpow⟩
```

## これが軽い理由

前に重かった wrapper は、1 本の theorem の中で

* `factor` 定義
* `Finset.mul_prod_erase`
* `span_singleton_finset_prod`
* `Ideal.span_singleton_pow`
* coprimality
* nonzero
* generic receiver
* torsion kill

を全部抱えておった。
今回の形では、**product equality / coprimality / nonzero は既に theorem 化済み** なので、その場で巨大な `calc` や `simpa [factor]` を回さない。これが heartbeat に効く。

## 判定

この 2 本が build-safe に通れば、言い方としては

$$
\boxed{
\text{Stage 1 は finished と言ってよい}
}
$$

じゃ。
なぜなら、最新整理どおり、残る honest open は **Stage 1 の存在形 boundary target** と **Stage 3** だったが、その前者を theorem で固定できるからじゃ。

## 作業指示

次はこの順で攻めるのがよい。

まず上の 1 本目だけ入れる。
それが通れば 2 本目はかなり軽い。
2 本目が通ったら、その先に **Stage 2 の薄い wrapper を 1 本だけ戻すか、use-site inline のまま進むか** を決めればよい。

わっちの勧めは、今はまだ **Stage 2 wrapper は戻さず**、この 2 本で止めることじゃ。
理由は、目的は “finished 判定 theorem” を持つこと であって、再び heartbeat を食う public wrapper を増やすことではないからじゃ。
