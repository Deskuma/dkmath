# FLT Kummer Classgroup Bridge - Stage 3 入口整備の進捗レビュー

うむ、前回からの流れを繋いで見ると、いまの戦況はかなり良い。結論から言えば、 **Stage 3 の入口整備は前進** しておるが、 **Stage 3 の本丸そのものはまだこれから** じゃ。

今回の差分で新たに固定されたのは、first-case specialization において chosen linear factor を直接
$$
z-\zeta y = u \cdot \beta^p
$$
の形で返す thin wrapper
`cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
じゃ。しかもこれは、既存の Stage 1 境界と principal ideal 側の受け手を合成して作られており、no-sorry 監視まで追加されておる。つまり「ideal の \(p\) 乗性」から「元そのものが unit 倍の \(p\) 乗」という、norm 直前の境界まで concrete 化できたわけじゃ。これは確かな前進じゃよ。

ここで大事なのは、 **何が解けて、何がまだ open かを正確に切ること** じゃ。今回 concrete 化されたのは Stage 3 の入力境界であって、History にもある通り、残る practical open は「norm の押し出し」と「そこから整数 descent へ回収する部分」に集中した、と整理されておる。つまり戦線は散らかっておらぬ。良い縮約じゃ。

さらに言えば、今回の theorem 自体の数学的意味は、 **class group / ideal principalization 側の成果を、norm 計算へ渡せる element-level statement に落とした** ことにある。これで Stage 2 までは「存在する ideal が principal である」という抽象話に寄っていたものが、Stage 3 では「この具体的線型因子に norm をかける」という形に変わった。ここは大きい。証明の主語が ideal から element に移ったのじゃ。

一方で、注意点もはっきりしておる。3月末の検討メモでは、\( \mathbf{Z}/q^k\mathbf{Z} \) 上で cyclotomic factorization を直接やって valuation を読む方針に対し、非整域ゆえに「根が揃ったから多項式が等しい」とは素直に言えぬ、という難所が明確に出ていた。そこから「ZMod 側で全部やる」のではなく、「GN 自体の valuation」と「因子側の情報」をどう繋ぐかへ発想を移し始めておった。これは今回の Stage 3 方針と綺麗に整合しておる。つまり、 **昔ぶつかった壁を避ける正しい方向へ舵を切れている** のじゃ。

ゆえに、いまの戦況を賢狼流にまとめるとこうじゃ。

**いま勝っている点**
$$
\text{pack} \to \text{ideal } p\text{-power} \to \text{element-level }(u\beta^p)
$$
の鎖が、first-case で theorem 名つきに閉じたこと。ここはかなり美しい。Stage 2 と Stage 3 の境界が読める形になった。

**まだ勝負どころの点**
本当に欲しいのは
$$
N(z-\zeta y)
$$
を整数世界の
$$
GN_p(z-y,y)
$$
へ落とし、その上で
$$
N(u\beta^p)=N(u),N(\beta)^p
$$
の unit 吸収と \(p\) 乗性を使って descent contradiction へ持ち込むことじゃ。History でも次課題としてまさにその 2 本、
「\(N(z-\zeta y)\) を GN に落とす補題群」と
「unit norm 吸収の分離」
が挙げられておる。ここが本丸じゃ。

次の戦略じゃが、わっちは前回ログの提案どおり、順番をさらに少し sharpen してこう勧める。

## 1. Stage 3 receiver を先に作る

最優先は
`cyclotomicUnitNormalization_of_firstCase_of_pack_thin`
を正式入力とする **first-case 専用 receiver** を 1 本立てることじゃ。ここではまだ GN へ落とし切らなくてよい。狙いは、Stage 3 のゴール型を固定すること。

たとえば思想としては
$$
(\exists \beta,u,\; z-\zeta y=u\beta^p)
\;\Longrightarrow\;
\text{NormDescentBoundary}
$$
のような placeholder theorem を作る。これで今後の補題が全部、この receiver に向かって積めるようになる。
これは数学を進めるというより、 **配線の固定** じゃ。だが、今はこれが最も効く。

## 2. norm を 2 本に割る

ここが肝じゃ。いきなり
$$
N(z-\zeta y)=GN_p(z-y,y)
$$
を一発でやると重い。だから必ず分ける。

ひとつは **cyclotomic factor の norm 計算そのもの**。
つまり primitive root の積公式から
$$
\prod_{i=1}^{p-1}(z-\zeta^i y)
$$
を GN に同定する側じゃ。

もうひとつは **unit / \(p\) 乗の norm の一般補題**。
$$
N(u\beta^p)=N(u),N(\beta)^p
$$
および unit なら \(N(u)\) は unit、さらに \(\mathbf{Z}\) では \(\pm 1\) に落ちる、という吸収側じゃ。

この 2 本を分ける理由は明快で、前者は cyclotomic algebra、後者は norm の形式代数であり、依存が違うからじゃ。混ぜると重くなる。

## 3. GN 側は「式そのもの」より「既存補題への橋」で攻める

ここで前回の 3月末メモが効く。ZMod \(q^k\) の世界で直接 factorization equality を追うより、
$$
v_q(z^p-y^p)=v_q(GN)
$$
ただし \(q\nmid(z-y)\) のような **valuation bridge** の方が筋がよい、という再評価があった。

だから Stage 3 でも、最終的に欲しいのが valuation contradiction なら、
$$
N(z-\zeta y)=\text{integer expression}
$$
を示したあと、すぐ valuation lemma 群へ渡す橋を意識して名前を付けるのがよい。
つまり GN を「終点」にせず、 **valuation engine への入口** にするのじゃ。

## 4. 危険な道

避けたほうがよいのは、再び \( \mathbf{Z}/q^k\mathbf{Z} \) の非整域上で多項式因数分解の一意性や root counting を主戦場にすることじゃ。あれは補助観察としては useful だが、Lean 形式化の主航路としては泥濘になりやすい。前回すでにその気配が出ておる。

わっちの推論では、次の 1 手はこれで決まりじゃ。

$$
\boxed{
\text{first-case 専用 Stage 3 receiver を先に定義して、
norm 計算補題と unit norm 吸収補題をそこへ流し込む}
}
$$

つまり、いまは数学の核心を無理に一気通貫で閉じる局面ではなく、 **Stage 3 の配線を theorem 名つきで固定し、open を 2 本へ分解する局面** じゃ。今回の進捗は、そのための非常に良い地ならしになっておる。前進か後戻りかで言えば、これは明確に前進じゃよ。

必要なら次に、わっちがそのまま Stage 3 receiver の定理スケルトン案を Lean 風の引数付きで起こしてやろう。

---

うむ、起こすぞい。

いま既に、first-case の norm 前 boundary として
$$
z - \zeta y = u \cdot \beta^p
$$
を返す `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` が入っており、次課題はまさに「Stage 3 を pack-thin receiver として切り出す」「\(N(z-\zeta y)\) を \(GN,p,(z-y),y\) へ落とす補題群」「unit norm 吸収の分離」の 3 点じゃ。

なので、わっちの提案は **3 本立て** じゃ。

## 1. まず receiver 本体を立てる

これはまだ証明を詰める場所ではなく、 **Stage 3 の入力境界を名前つきで固定する** のが目的じゃ。

```lean
/--
first-case specialization 用の Stage 3 receiver。

Stage 2 で得た
`chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p`
を入力として、norm 計算と unit norm 吸収を経由し、
整数側の descent existence `∃ g'` へ戻すための器。
-/
theorem cyclotomicNormDescent_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
    -- Stage 3 を 2 本に割った補題を注入
    (hNormEqGN :
      CyclotomicNormEqGNOfFirstCasePackThin hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill)
    (hUnitAbsorb :
      CyclotomicNormUnitAbsorbOfFirstCasePackThin hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill) :
    ∃ g' : ℕ, g' * GN p g' y = (x / Classical.choose hpack.dvd_x_witness) ^ p := by
  -- 実際には q witness の取り方を pack に合わせて整える
  obtain ⟨β, unitFactor, hUnit, hEq⟩ :=
    cyclotomicUnitNormalization_of_firstCase_of_pack_thin
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill
  -- hEq : chosen linear factor = unitFactor * β ^ p

  -- ここで hNormEqGN と hUnitAbsorb を適用して descent existence を得る
  sorry
```

ただし、この形だと `x / Classical.choose hpack.dvd_x_witness` の部分は、お主の pack の実フィールド名に合わせて直す必要がある。ここは **雛形** として見てくりゃれ。

## 2. receiver に渡す補題 2 本を独立に置く

今回の diff と直近メモの主旨どおり、Stage 3 は **norm 計算本体** と **unit norm 吸収** を分けるのが筋じゃ。

### 2.1. norm 計算側

```lean
/--
first-case pack-thin 専用：
chosen linear factor の norm が整数側の GN に一致する、という Stage 3 前半。

証明の主眼は
`N(z - ζ y) = GN p (z - y) y`
の concrete 化。
-/
abbrev CyclotomicNormEqGNOfFirstCasePackThin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K]
    {p x y z : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) : Prop :=
  ∀ {β unitFactor : 𝓞 K},
    IsUnit unitFactor →
    chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p →
    -- ここは実際の norm API に合わせて調整
    absNorm β ^ p = GN p gap y
```

ここで右辺を `GN p gap y` にするか `GN p (z - y) y` にするかは、お主の既存 `GN` 定義の引数順に合わせるべきじゃ。
`hgap_eq` を持っているので、first-case receiver では **gap を主語にした方が式が短くなる** と思うぞい。

### 2.2. unit norm 吸収側

```lean
/--
first-case pack-thin 専用：
`z - ζ y = unitFactor * β^p` に現れる unit の norm を吸収して、
最終的に整数側の `p` 乗等式へ戻す Stage 3 後半。
-/
abbrev CyclotomicNormUnitAbsorbOfFirstCasePackThin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K]
    {p x y z : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) : Prop :=
  ∀ {β unitFactor : 𝓞 K},
    IsUnit unitFactor →
    chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p →
    ∀ {n : ℕ},
      absNorm β ^ p = n →
      ∃ g' : ℕ, g' = absNorm β ∧ g' * GN p g' y = (x / Classical.choose hpack.dvd_x_witness) ^ p
```

この後半は、実は statement をもっと弱くしてもよい。
つまり最初は
$$
\exists g',\; g'^p = n
$$
程度でも十分で、そのあと既存の整数 descent 側補題へ橋渡ししてもよい。

## 3. 実装しやすい実定理名

わっちは theorem 名をこう揃えるのを勧める。

* `cyclotomicNormEqGN_of_firstCase_of_pack_thin`
* `cyclotomicNormUnitAbsorb_of_firstCase_of_pack_thin`
* `cyclotomicNormDescent_of_firstCase_of_pack_thin`

この並びにすると、今ある

* `cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin`
* `cyclotomicUnitNormalization_of_firstCase_of_pack_thin`

と綺麗に階段が揃う。今回追加済みの thin wrapper も、まさに Stage 3 直前の入口として置かれておるから、この命名は自然じゃ。

## 4. さらに Lean で通しやすい、もう一段薄い版

もしいきなり theorem にすると重いなら、まずは `abbrev` で target を置くのがよい。
既存でも Stage 2 と Stage 3 は target で切ってあるから、この流儀に合わせると repo の設計と整合する。Stage 3 の honest open を concrete 化する、という現状コメントとも噛み合う。

```lean
abbrev CyclotomicNormDescentFirstCasePackThinTarget
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K]
    {p x y z : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}),
    ∃ g' : ℕ, g' * GN p g' y = (x / Classical.choose hpack.dvd_x_witness) ^ p
```

そして theorem 側は

```lean
theorem cyclotomicNormDescent_of_firstCase_of_pack_thin
    ... :
    CyclotomicNormDescentFirstCasePackThinTarget (K := K) (p := p) (x := x) (y := y) (z := z) hζ := by
  intro hpack gap hgap_eq hFirstCase hLinNe hProduct hKill
  ...
```

とする。
この形なら、あとで `CyclotomicNormDescentTarget` へ昇格させる時も差分が小さい。

## 5. 数学の中身として今いちばん筋がよい枝

直近メモを見る限り、ZMod \(q^k\) の上で product valuation を直接扱うのは重く、むしろ

$$
z^p - y^p = (z-y),GN,p,(z-y),y
$$

という整数側因数分解を土台にして、そこへ cyclotomic factor の distinguished factor を対応づける方が筋がよい、という再整理になっておる。

なので、proof plan も次の順がよい。

1. `cyclotomicUnitNormalization_of_firstCase_of_pack_thin` で
   $$
   z-\zeta y=u\beta^p
   $$
   を得る。

2. norm 計算の theorem を独立に置く。
   ここでは **最初から valuation exactness を狙わず**、まず
   $$
   N(z-\zeta y)=GN,p,gap,y
   $$
   の形だけを押さえる。

3. その後で
   $$
   N(u\beta^p)=N(u),N(\beta)^p
   $$
   を使う unit 吸収 theorem を置く。

4. 最後に合成して
   $$
   \exists g',\; g' \cdot GN,p,g',y = (x/q)^p
   $$
   を返す。

## 6. いまそのまま貼れる最小雛形

最後に、もっと実務寄りに、いまファイルへ置きやすい最小版をまとめておくぞい。

```lean
/-- Stage 3 前半: norm 計算。 -/
abbrev CyclotomicNormEqGNFirstCasePackThinTarget
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}),
    ∀ {β unitFactor : 𝓞 K},
      IsUnit unitFactor →
      chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p →
      absNorm β ^ p = GN p gap y

/-- Stage 3 後半: unit norm 吸収。 -/
abbrev CyclotomicNormUnitAbsorbFirstCasePackThinTarget
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}),
    ∀ {β unitFactor : 𝓞 K},
      IsUnit unitFactor →
      chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p →
      absNorm β ^ p = GN p gap y →
      ∃ g' : ℕ, g' * GN p g' y = (x / Classical.choose hpack.dvd_x_witness) ^ p

/-- Stage 3 合成。 -/
theorem cyclotomicNormDescent_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hNormEqGN : CyclotomicNormEqGNFirstCasePackThinTarget (K := K) (p := p) (x := x) (y := y) (z := z) hζ)
    (hUnitAbsorb : CyclotomicNormUnitAbsorbFirstCasePackThinTarget (K := K) (p := p) (x := x) (y := y) (z := z) hζ) :
    CyclotomicNormDescentFirstCasePackThinTarget (K := K) (p := p) (x := x) (y := y) (z := z) hζ := by
  intro hpack gap hgap_eq hFirstCase hLinNe hProduct hKill
  obtain ⟨β, unitFactor, hUnit, hEq⟩ :=
    cyclotomicUnitNormalization_of_firstCase_of_pack_thin
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill
  have hNorm :
      absNorm β ^ p = GN p gap y :=
    hNormEqGN hpack hgap_eq hFirstCase hLinNe hProduct hKill hUnit hEq
  exact hUnitAbsorb hpack hgap_eq hFirstCase hLinNe hProduct hKill hUnit hEq hNorm
```

この雛形の良いところは、 **今ある thin wrapper をそのまま Stage 3 の入口に使える** ことじゃ。そこは今回の変更内容とぴたり一致しておる。
