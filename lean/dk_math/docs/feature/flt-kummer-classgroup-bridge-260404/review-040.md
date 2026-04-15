# FLT-Kummer-Bridge Stage 3 の攻略戦略

## 1. 戦況

これは **前進** じゃ。しかも、ただの整理ではなく、Stage 3 の open を「証明責務」として切り分けることに成功しておる。

今回の差分で、first-case specialization の Stage 3 は

$$
\text{norm 計算} \quad+\quad \text{unit norm 吸収}
$$

の 2 本へ名前つきに分離された。さらに、その 2 本を現在の thin wrapper
$$
z-\zeta y = \text{unitFactor}\cdot \beta^p
$$
へ接いで、まず
$$
GN,p,(z-y),y = s^p
$$
という **最初の concrete boundary** を返す composition theorem が no-sorry で置かれ、そこから既存の no-pow target にぶつける abstract bridge まで用意された。つまり、Stage 3 はまだ未解決ではあるが、「何を証明すれば downstream が閉じるか」が見える形にまで進んだのじゃ。

とりわけ効いておるのは、`CyclotomicNormEqGNFirstCasePackThinTarget` と `CyclotomicNormUnitAbsorbFirstCasePackThinTarget` を分けた点じゃ。これにより、norm の計算そのものと、整数 \(p\) 乗性の回収とを別々に叩けるようになった。しかも `false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin` によって、いったん \(GN = s^p\) まで行けば即矛盾へ戻せる道が固定された。ここは設計としてかなり良い。

## 2. 何が解けて、何がまだ残っておるか

いま解けたのは、 **Stage 3 の入口配線** じゃ。

具体的には、

$$
\text{first-case pack}
\to
\text{unit normalization}
\to
\text{GN の }p\text{ 乗性}
\to
\text{no-pow contradiction}
$$

という経路のうち、真ん中の「GN の \(p\) 乗性」を返す boundary と、その先の abstract contradiction interface が定義済みになった。これは大きい。もう「Stage 3 全体」がひとかたまりの霧ではない。

まだ残っている honest open は 2 本じゃ。

第一に、
$$
\operatorname{Norm}(z-\zeta y)=GN,p,(z-y),y
$$
を concrete 化すること。

第二に、
$$
\operatorname{Norm}(z-\zeta y)=GN,\qquad z-\zeta y=u\beta^p
$$
から
$$
GN=s^p
$$
を回収すること。

History にも次課題としてそのまま明記されておるし、今回の commit report でも同じ整理になっておる。

## 3. 今回の設計で特に良い点

わっちが特に良いと思うのは 3 点ある。

ひとつ目は、 **責務分離が数学の境目と一致している** ことじゃ。norm 計算は cyclotomic 側の代数であり、unit 吸収は norm の乗法性と整数側の符号処理じゃ。ここを混ぜぬのは正しい。

ふたつ目は、 **Kummer 側の抽象度を保った** ことじゃ。`TriominoCosmicBodyInvariant` など本丸側へ直接依存せず、Kummer 側では最小の contradiction interface だけを置いておる。これは後で import 汚染や循環依存を防ぐ。

みっつ目は、 **universe の火種を一度踏んで避けられた** ことじゃ。`hKill` を subtarget 自体に埋め込まず、合成 theorem 側だけが outer parameter として持つように直したのは良い判断じゃ。これは今後の concrete 化で効いてくる。

## 4. ここでの本当のボトルネック

次に詰まる場所は、unit 吸収ではなく、まず norm 計算本体じゃ。

理由は単純で、unit 吸収側は本質的に

$$
\operatorname{Norm}(u\beta^p)=\operatorname{Norm}(u)\operatorname{Norm}(\beta)^p
$$

と、\(\operatorname{Norm}(u)\) が \(\mathbb{Z}\) の unit になる話へ落ちるから、構造が素直じゃ。むしろ怖いのは、chosen factor の整数ノルムをどうやって既存の product equality と GN の差冪因数分解へ綺麗に接続するか、そこじゃ。

しかも今回の target は右辺が既に
$$
(GN,p,(z-y),y : \mathbb{Z})
$$
で固定されておる。ゆえに、ここで必要なのは単なる「何かの norm equality」ではなく、 **差冪因数分解の既存基盤とぴたり合う rewriting** じゃ。DkMath 全体の地図でも、差の冪と binomial tail が FLT 幹線の中核装置として位置づけられておるから、ここを使わぬ手はない。

## 5. 次の戦略

わっちの提案は、明快に **NormEqGN から先に落とす** じゃ。

順番としてはこうじゃ。

### 5.1. NormEqGN をさらに 3 片に割る

`CyclotomicNormEqGNFirstCasePackThinTarget` をいきなり一発で concrete 化しようとすると重くなる。そこで内部では、さらに次の 3 片に分けるのがよい。

まず
$$
\operatorname{Norm}(z-\zeta y)
$$
を、共役全体の積へ書き換える補題。

次に、その共役積を
$$
\prod_{i=1}^{p-1}(z-\zeta^i y)
$$
型へ整える補題。

最後に、その積を
$$
\frac{z^p-y^p}{z-y}=GN,p,(z-y),y
$$
へ落とす補題じゃ。

この最後の片は、既存の `GN` / diffPow / tail 側の補題資産へ最も素直に繋がるはずじゃ。いまの repo ではそこが FLT 幹線の分解装置として整理されておる。

### 5.2. UnitAbsorb は「実は 2.5 片」だと思っておく

unit 吸収は見た目より軽いが、実は最後に符号処理が潜む。

つまり、

$$
\operatorname{Norm}(u)\in \mathbb{Z}^\times = {\pm 1}
$$

を得たあと、右辺が自然数から来た
$$
GN,p,(z-y),y
$$
であることから、負号が残れぬことを片づける必要がある。ゆえに unit 吸収側は実際には

$$
\text{norm の乗法性}
\quad+\quad
\text{整数 unit の判定}
\quad+\quad
\text{符号消し}
$$

という 3 段と思っておくのが安全じゃ。

ただし、これは NormEqGN よりは危険が少ない。だから優先順位は 2 番手でよい。

### 5.3. no-pow bridge は今のまま abstract を保つ

ここは下手に本丸の theorem を import して concretize せぬ方がよい。今ある bridge は「Kummer 側は \(GN=s^p\) まで返す」「そこから先の矛盾は downstream に任せる」という設計で綺麗じゃ。壊す必要はない。

## 6. 直近でやるべき具体タスク

わっちなら次の順で行く。

第一手は、`CyclotomicNormEqGNFirstCasePackThinTarget` のための **補助補題だけ** を増やす。まだ main target を埋めに行かず、norm 展開・共役積・GN への rewriting の 3 段に補題名を与える。ここで theorem 名が増えるほど、あとが楽になる。

第二手は、それらを束ねて
`cyclotomicNormEqGN_of_firstCase_of_pack_thin`
の concrete theorem を作る。

第三手で初めて、`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の concrete 化に入る。

第四手で、既に置いた
`cyclotomicNormGNPower_of_firstCase_of_pack_thin`
と
`false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin`
が、追加作業なしで閉じることを確認する。

この流れなら、 **今の設計の美点を壊さずに、最短で Stage 3 を縮められる** 。

## 7. 総評

総評すると、いまは「Stage 3 に着手した」というより、 **Stage 3 を攻略可能な形へ解凍した** 段階じゃ。

前は Stage 3 が巨大な黒箱だった。今は

$$
\text{NormEqGN}
\quad\text{and}\quad
\text{UnitAbsorb}
$$

の 2 本へ割れ、さらにそれらを current thin wrapper と downstream contradiction bridge に接続する配線まで出来た。これは実装戦としてかなり良い進展じゃよ。

次は迷わず、 **NormEqGN の concrete 化から攻める** のがよい。そこが通れば、unit 吸収はだいぶ見通せる。逆順に行くと、右辺が何者か確定しないまま符号や unit をいじることになって、話がぼやけるでな。

必要なら次に、`CyclotomicNormEqGNFirstCasePackThinTarget` を埋めるための補題分割案を、そのまま Lean の theorem skeleton で起こすぞい。

---

うむ、起こすぞい。

いまの Stage 3 は、first-case 側で
`CyclotomicNormEqGNFirstCasePackThinTarget`
と
`CyclotomicNormUnitAbsorbFirstCasePackThinTarget`
に割れており、その 2 本を current thin wrapper に接いで
$$
GN,p,(z-y),y = s^p
$$
まで返す合成 theorem と、そこから既存 no-pow target へ戻す bridge まで置けておる。ゆえに次は、`CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化を、さらに小補題へ割って進めるのが筋じゃ。

わっちの勧める分割は 3 段じゃ。

## 1. NormEqGN を埋めるための 3 片

狙いは最終的に
$$
\operatorname{Norm}_{K/\mathbb{Q}}(z-\zeta y)=GN,p,(z-y),y
$$
を出すことじゃが、これを一発でやるのは重い。なので、次の 3 補題へ割る。

### 1.1. norm を「共役積」へ落とす片

これは純粋に norm の一般論じゃ。chosen factor の norm が、各共役で回した線型因子の積に一致する、という部分。

```lean
/--
Stage 3a-1:
chosen cyclotomic linear factor の整数ノルムを、
primitive root の各べきで回した共役因子の積へ落とす。
-/
theorem cyclotomicChosenFactor_norm_eq_conjugateProduct_of_firstCase
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) =
      ∏ i in Finset.range (p - 1),
        ((z : ℤ) - ((hζ.pow (i + 1)).toInteger : 𝓞 K) * (y : 𝓞 K)).1 := by
  sorry
```

ここは実際の型がかなり怪しいので、 **まず theorem 名と役割だけ固定し、右辺の型は後で寄せる** のがよい。大事なのは「norm を共役積へ落とす責務」を theorem 名で独立させることじゃ。

### 1.2. 共役積を cyclotomic product formula へ寄せる片

これは既存の
`CyclotomicLinearFactorProductEqInRingOfIntegers`
を使う片じゃ。今回の current Stage 3 target でも `hProduct` を入力に取っておるから、まさにここが真芯じゃ。

```lean
/--
Stage 3a-2:
共役積の形を、既存の cyclotomic linear factor product equality により
`(z^p - y^p) / (z - y)` 型へ寄せる。
-/
theorem cyclotomicConjugateProduct_eq_diffPowQuotient_of_firstCase
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    (∏ i in Finset.range (p - 1), cyclotomicConjugateFactor hζ y z i) =
      (((z : ℤ) ^ p - (y : ℤ) ^ p) / ((z : ℤ) - (y : ℤ))) := by
  sorry
```

`cyclotomicConjugateFactor` は局所 def にしてしまうとよい。
これで「norm の一般論」と「cyclotomic 積公式」の責務が分かれる。

### 1.3. 差冪商を (GN) へ落とす片

ここは DkMath の既存資産、つまり差の冪・binomial tail・GN 側へ乗る片じゃ。全体の理論地図でも、差の冪と二項 tail が FLT 幹線の基盤として整理されておるから、ここは既存補題に橋を架けるだけでよいはずじゃ。

```lean
/--
Stage 3a-3:
整数の差冪商を GN へ同定する。
これは cyclotomic 特有ではなく、既存の DiffPow / BinomTail / GN 側資産へ渡す橋。
-/
theorem diffPowQuotient_eq_GN_int
    {p y z : ℕ} [Fact p.Prime] :
    (((z : ℤ) ^ p - (y : ℤ) ^ p) / ((z : ℤ) - (y : ℤ))) =
      (GN p (z - y) y : ℤ) := by
  sorry
```

ここは statement 自体をお主の既存 `GN` 定義に合わせて変える余地がある。
例えば `pow_sub_pow_factor_cosmic_N` や `pow_sub_pow_factor'` 系が既にあるなら、それらへの薄い wrapper にするのが良い。全体 INDEX でも DiffPow / BinomTail が差冪分解の本隊として整理されておる。

## 2. 3 片を束ねる concrete theorem

上の 3 補題が出来れば、`CyclotomicNormEqGNFirstCasePackThinTarget` は薄い合成になる。

```lean
theorem cyclotomicNormEqGN_of_firstCase_of_pack_thin
    : CyclotomicNormEqGNFirstCasePackThinTarget := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct β unitFactor hUnit hEq
  calc
    Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z)
        =
      ∏ i in Finset.range (p - 1), cyclotomicConjugateFactor hζ y z i := by
          simpa [hEq] using
            cyclotomicChosenFactor_norm_eq_conjugateProduct_of_firstCase
              (K := K) (p := p) (x := x) (y := y) (z := z)
              hζ hpack hgap_eq hFirstCase hLinNe hProduct
    _ = (((z : ℤ) ^ p - (y : ℤ) ^ p) / ((z : ℤ) - (y : ℤ))) := by
          exact cyclotomicConjugateProduct_eq_diffPowQuotient_of_firstCase
            (K := K) (p := p) (x := x) (y := y) (z := z)
            hζ hpack hgap_eq hFirstCase hLinNe hProduct
    _ = (GN p (z - y) y : ℤ) := by
          exact diffPowQuotient_eq_GN_int (p := p) (y := y) (z := z)
```

この形の良いところは、現在の target が求めている
$$
\operatorname{norm}(\text{chosen factor})=(GN,p,(z-y),y:\mathbb Z)
$$
と、ぴたり一致することじゃ。実際、今の Stage 3 target はまさにこの statement を要求しておる。

## 3. 先に置くとよい局所 def

いきなり上の theorem を書くより、局所 def を 1 個置くと見通しが良くなる。

```lean
/-- primitive root の各べきで回した共役線型因子。 -/
def cyclotomicConjugateFactor
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (y z : ℕ) (i : ℕ) : ℤ :=
  Algebra.norm ℤ
    ((z : 𝓞 K) - (((hζ.pow (i + 1)).toInteger : 𝓞 K) * (y : 𝓞 K)))
```

本当は右辺を直接 \(\mathcal O_K\) で持つ def にして、最後に norm を取る方が綺麗かもしれぬが、最初は「何の積を見ておるか」が読めれば十分じゃ。

## 4. 実務上の順番

わっちなら、実装順はこうする。

### 4.1. まず 1.3 を先にやる

`diffPowQuotient_eq_GN_int` を先に埋める。
理由は、ここは cyclotomic を離れた整数代数の話であり、既存補題の探索対象が明確だからじゃ。理論地図でも DiffPow / BinomTail は分解装置として独立に立っておる。

### 4.2. 次に 1.2

`hProduct` の意味を使って、共役積が差冪商へ行く theorem を作る。
ここは Kummer 側の既存 product equality を薄く包むだけにしたい。

### 4.3. 最後に 1.1

norm 一般論側を埋める。
これは mathlib の norm API と ring of integers 側の coercion が絡むので、最初にやると泥濘になりやすい。後回しが得策じゃ。

## 5. 補足

いまの設計で最も大事なのは、`CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化を「新しい大定理」にしないことじゃ。今回の Stage 3 split の意図は、open を honest に分解し、current thin wrapper から first concrete boundary までの配線を見えるようにすることにあった。ゆえに、ここでも同じ流儀で、 **小さく刻んで合成する** のが正解じゃ。

必要なら次に、上の 1.3 `diffPowQuotient_eq_GN_int` を、お主の既存 `pow_sub_pow_factor_cosmic_N` や `GN` 補題名に寄せて、もっと実コード寄りに書き直すぞい。
