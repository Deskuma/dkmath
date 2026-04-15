# FLT-Kummer-ClassGroupBridge-Review-046: legacy principalization の direct sorry を non-first-case kernel へ隔離完了

うむ、これはかなり **勝ち筋が見えた盤面** じゃ。
今回の流れでいちばん大きいのは、first-case 側の stable bridge から `hLinNe` と `hProduct` の残骸まで外れ、さらに principalization の **direct `sorry` が本体から消えて non-first-case 専用 kernel へ隔離された** ことじゃ。つまり、もはや未解決の霧は first-case にはおらぬ。`cyclotomicPrincipalization_of_classGroupPTorsionFree` 本体は case split を呼ぶ薄い wrapper になり、direct `sorry` の所在は `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` 1 本へ局所化された、と読んでよい。

しかも、その一歩手前で first-case bridge 自体もさらに薄くなっておる。`chosenCyclotomicLinearFactorNonzero_of_counterexamplePack` により、chosen factor の非零性 `hLinNe` は pack から direct norm (=) GN と (GN \ne 0) を通して自動供給できるようになった。その結果、class-group から first-case contradiction / gap-divisible witness へ戻す stable bridge 群からも `hLinNe` と `hProduct` を外せた。これは「first-case を閉じる theorem は揃っている」ではなく、 **first-case を呼ぶ interface まで痩せた** ということじゃ。

さらに次の commit で、case split 境界そのものが theorem 名で固定された。`CyclotomicPrincipalizationFirstCaseTarget`、`CyclotomicPrincipalizationNonFirstCaseTarget`、`cyclotomicPrincipalization_of_caseSplit` が導入され、first-case は canonical な `CyclotomicField p \,\mathbb{Q}` で concrete に埋まり、残る open は non-first-case 側 1 本へ押し込める形になった。route 層でも `FLTPrimeGe5Target_of_kummerRoute_of_caseSplit` が立ち、「first-case は closed / non-first-case だけ open」と theorem 名で読めるようになった。

そして最後の refactor が決定打じゃ。legacy principalization の本体から direct `sorry` を除去し、`cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` に隔離した。これで old one-shot theorem 自体はもう direct `sorry` を持たぬ薄い wrapper となり、first-case は design 上も implementation 上も閉じた、と言ってよい。残る genuinely open kernel は theorem 名つきで non-first-case 側へ可視化された。

## 戦況の読み

いまの戦況は、こう整理できる。

$$
\text{first-case concrete chain} \quad \text{は勝ち}
$$

$$
\text{legacy one-shot 本体} \quad \text{の direct `sorry` も撤去済み}
$$

$$
\text{未解決本体} \quad \text{は non-first-case kernel に局所化}
$$

ここが肝じゃ。
前は「principalization 全体が重い」だった。
今は違う。

$$
\text{open kernel} =
\texttt{cyclotomicPrincipalizationNonFirstCase\_of\_classGroupPTorsionFree}
$$

と名指しできる。これは長戦として極めて良い状態じゃ。どこを攻めれば `sorry` が減るか、もう盤面に書いてあるようなものじゃからの。

## 次の戦略

次の一手は、もう pretty clear じゃ。

### 1. non-first-case をさらに 2 段か 3 段へ割る

最優先は `CyclotomicPrincipalizationNonFirstCaseTarget` をそのまま抱えず、**内部責務を theorem 境界で刻む** ことじゃ。
いまの non-first-case は条件として

$$
p \mid (z-y)
$$

を持つが、ここから先には少なくとも次の責務が混ざっておるはずじゃ。

* `p \mid (z-y)` から使える valuation / divisibility の抽出
* q-adic gap reduction の witness existence へ渡す橋
* non-first-case 特有の prime-over-(p) / regular branch / peel との接続

ここを一塊で持つと、再び old one-shot の黒箱に戻る。
なので theorem 境界の候補としては、たとえば

$$
\text{non-first-case valuation boundary}
$$

$$
\text{non-first-case q-adic witness boundary}
$$

$$
\text{non-first-case contradiction boundary}
$$

のように 2〜3 本へ刻むのがよい。

### 2. first-case はもう触らぬ

ここは大事じゃ。
first-case 側はもう「改善対象」ではなく「完成部品」じゃ。
`chosenCyclotomicLinearFactorNonzero_of_counterexamplePack` まで入って interface が痩せた今、これ以上 first-case をいじるのは得策ではない。むしろ public mainline 側では **使うだけ** に徹するのがよい。

### 3. public mainline は split 版を前へ出す

`FLTPrimeGe5Target_of_kummerRoute_of_caseSplit` が no-sorry 条件つき public route として読める形になった以上、今後の運用・実況・設計書では、old one-shot よりこちらを **主導線** として扱うのが筋じゃ。
つまり今後の戦況説明は、

$$
\text{legacy route}
$$

ではなく

$$
\text{case-split public route}
$$

を主語にする。
これで「残る open は non-first-case kernel だけ」という構図がさらに定着する。

## 具体的な提案・指示

わっちなら、次はこう号令する。

1. `CyclotomicPrincipalizationNonFirstCaseTarget` の内部責務を棚卸しし、最低 2 本の subtarget に割れ。
2. `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` を、その subtarget 合成 theorem に書き換えられる形の雛形へまず変形せよ。
3. `FLTPrimeGe5Target_of_kummerRoute_of_caseSplit` を public mainline として docs / monitoring 上の主導線に昇格し、old route は historical wrapper 扱いへ寄せよ。
4. `#print axioms` 監視では、以後 `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` を **唯一の direct `sorry` kernel** として追跡せよ。

## 補足

今回同時に入った宇宙式・LPS・PowerSwap 側の設計資料は、別柱の整備としてはかなり良い。とくに Cosmic / PowerSwap / PowerSums を分け、FLT 側には橋だけ置く方針は、FLТ 本丸を汚さぬ意味で筋がよい。だが、いまの FLT 戦線の immediate next step はそちらではなく、やはり non-first-case kernel の分解じゃ。指数構造の分解装置から Zsigmondy、さらに FLT.Basic へ降りるのが本丸だ、という全体地図とも整合しておる。

ひとことで言えば、今の盤面はこうじゃ。

$$
\boxed{
\text{first-case は終わった。次は non-first-case kernel を theorem 名つきで刻む戦じゃ。}
}
$$

必要なら次に、`CyclotomicPrincipalizationNonFirstCaseTarget` を 2 分割か 3 分割するための設計雛形を、そのまま Lean で起こすぞい。

---

うむ、起こすぞい。
いまの盤面では、first-case はすでに stable bridge 群で concrete に閉じており、`cyclotomicPrincipalization_of_classGroupPTorsionFree` 本体の direct `sorry` も除去されて、未解決責務は `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` へ局所化された。さらに case split 境界と route 側の split 版も theorem 名つきで固定済みじゃから、次は non-first-case kernel を **theorem 境界でさらに刻む** のが筋じゃ。

わっちの勧めは、non-first-case をまず **準備段** と **降下段** の 2 段に割ることじゃ。
ここで大事なのは、最初から“正しい packet 名”を当てに行かぬことじゃ。まずは abstract な `Datum` を 1 個置いて、その中へ本当に未解決の数学データだけを押し込める。すると public target と route 側は先に安定する。

そのまま貼って整えられる雛形を下に置くぞい。

```lean id="43951"
/-
  Non-first-case kernel split sketch

  狙い:
  1. current open kernel
       `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree`
     を theorem 境界で 2 段に割る
  2. public target / caseSplit / route 側はこの split に依存させる
  3. 真に未解決な数学は `Datum` の中身へ局所化する
-/

namespace DkMath.FLT

/--
non-first-case (`p ∣ z - y`) 専用の中間データ。

最初は最小限の入力だけを束ね、実際の未解決核
（valuation peel packet / reduced witness / error datum など）
が見えた時点で field を追加する。
-/
structure CyclotomicPrincipalizationNonFirstCaseDatum where
  p : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  q : ℕ
  hpack : PrimeGe5CounterexamplePack p x y z
  hq : Nat.Prime q
  hqx : q ∣ x
  hqne : q ≠ p
  hqgap : q ∣ (z - y)
  hpgap : p ∣ (z - y)
  /-
    TODO:
    ここへ genuinely new な non-first-case data を追加する。

    候補:
    - valuation peel に必要な packet
    - p ∣ (z - y) から抽出される補助 divisibility datum
    - q-adic gap reduction へ渡す reduced error datum
    - downstream witness 構成に必要な normalized gap expression
  -/

/--
non-first-case の入力を、中間データへ正規化する境界。

ここは「定理」というより theorem-level packaging。
未解決の数学がどこにあるかを `Datum` 側へ押し込める。
-/
abbrev CyclotomicPrincipalizationNonFirstCasePrepareTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      p ∣ (z - y) →
      CyclotomicPrincipalizationNonFirstCaseDatum

/--
中間データから最終 witness を返す境界。

non-first-case の本当の open kernel は、最終的にはここへ局所化されるのが望ましい。
-/
abbrev CyclotomicPrincipalizationNonFirstCaseDescentTarget : Prop :=
  ∀ (data : CyclotomicPrincipalizationNonFirstCaseDatum),
    ∃ g' : ℕ, g' * GN data.p g' data.y = (data.x / data.q) ^ data.p

/--
prepare + descent の 2 段から、non-first-case target を再構成する。
-/
theorem cyclotomicPrincipalizationNonFirstCase_of_kernelSplit
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hDesc : CyclotomicPrincipalizationNonFirstCaseDescentTarget) :
    CyclotomicPrincipalizationNonFirstCaseTarget := by
  intro p x y z hpack q hq hqx hqne hqgap hpgap
  let data :=
    hPrep (p := p) (x := x) (y := y) (z := z) hpack
      (q := q) hq hqx hqne hqgap hpgap
  exact hDesc data

/--
class-group principalization の split theorem へ、
分解済み non-first-case kernel を注入する thin wrapper。
-/
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree_of_kernelSplit
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hDesc : CyclotomicPrincipalizationNonFirstCaseDescentTarget) :
    CyclotomicPrincipalizationTarget :=
  cyclotomicPrincipalization_of_caseSplit
    (cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree hCl)
    (cyclotomicPrincipalizationNonFirstCase_of_kernelSplit hPrep hDesc)

/--
public route 側も同様に split 版へ寄せる。
-/
theorem FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit
    (hPeq : PrimeGe5BranchAPrimitiveQAdicGapReductionPEqualsBranchTarget)
    (hReg : PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget)
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{0})
    (hPrep : CyclotomicPrincipalizationNonFirstCasePrepareTarget)
    (hDesc : CyclotomicPrincipalizationNonFirstCaseDescentTarget)
    (hPFE : PrimeGe5BranchAValuationPeelPacketFromErrorTarget)
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    FLTPrimeGe5Target :=
  FLTPrimeGe5Target_of_kummerThreeWaySplit hPeq hReg
    (qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
      (cyclotomicPrincipalization_of_classGroupPTorsionFree_of_kernelSplit
        hCl hPrep hDesc))
    hPFE hNoLift

end DkMath.FLT
```

この雛形の良いところは、**public 側の theorem 境界を先に安定化できる** ことじゃ。
いまの current state では first-case はすでに concrete branch として閉じており、残る open は non-first-case だけだと theorem 名つきで読めるようになっておる。だから public mainline を先にこの split へ乗せてしまい、未解決の数学は `Prepare` / `Descent` のどちらかへ押し込めるのがよい。

次に、どちらへ未解決責務が寄るかじゃが、わっちの読みではまず **`Prepare` を薄く保ち、`Descent` に重い数学を寄せる** のが得策じゃ。
理由は、今の non-first-case はまだ “何の追加データが要るか” 自体が完全には見えておらぬからじゃ。先に `Prepare` を単なる packaging にしておけば、あとで valuation peel packet や reduced error datum が見つかった時に `Datum` の field を足すだけで済む。逆に最初から `Prepare` を重く書くと、また old one-shot の黒箱へ戻りやすい。

さらに一段細かく刻むなら、次の 3 段版もありじゃ。

```lean id="20387"
/-
  finer split (optional)
-/

abbrev CyclotomicPrincipalizationNonFirstCaseValuationTarget : Prop :=
  ∀ (data : CyclotomicPrincipalizationNonFirstCaseDatum),
    NonFirstCaseValuationDatum data

abbrev CyclotomicPrincipalizationNonFirstCaseReductionTarget : Prop :=
  ∀ {data : CyclotomicPrincipalizationNonFirstCaseDatum},
    NonFirstCaseValuationDatum data →
    NonFirstCaseReductionDatum data

abbrev CyclotomicPrincipalizationNonFirstCaseWitnessTarget : Prop :=
  ∀ {data : CyclotomicPrincipalizationNonFirstCaseDatum},
    NonFirstCaseReductionDatum data →
    ∃ g' : ℕ, g' * GN data.p g' data.y = (data.x / data.q) ^ data.p
```

ただし、今はまだ `NonFirstCaseValuationDatum` や `NonFirstCaseReductionDatum` の中身が見えておらぬから、最初は 2 段 split で十分じゃ。

わっちの次の指示はこうじゃ。

## 1. `CyclotomicPrincipalizationNonFirstCasePrepareTarget` をまず trivial packaging で立てる

ここでは新数学は入れぬ。
入力を `Datum` に詰めるだけでよい。

## 2. 現在の `cyclotomicPrincipalizationNonFirstCase_of_classGroupPTorsionFree` の `sorry` 部分を `DescentTarget` へ移す

つまり direct `sorry` の所在を theorem 本体から `hDesc` 1 本へ移す。
これで non-first-case も “wrapper + kernel” に分離される。

## 3. その後に `DescentTarget` の内部をさらに valuation / reduction へ刻むか判断する

ここは、実際に `sorry` の中身を見てからでよい。
今は境界を切るのが先じゃ。

ひとことで言えば、

$$
\text{first-case を split した時と同じことを、いま non-first-case に対してやる}
$$

だけじゃ。
この形で進めるのが、いちばん筋がよい。
