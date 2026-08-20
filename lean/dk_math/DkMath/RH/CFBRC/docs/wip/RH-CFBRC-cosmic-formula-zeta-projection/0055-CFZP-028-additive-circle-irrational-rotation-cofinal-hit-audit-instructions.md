# CFZP-0055 / CFZP-028

## additive-circle irrational-rotation cofinal-hit audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-026: periodic third-quadrant phase-cell certificate — Green-A
- CFZP-027: subcritical large-cell coefficient readiness — Green-A

CFZP-027 により、Good-side の `A₀ ≥ 0` は sufficiently large cell で自動化された。
残る fixed-prime phase frontier は、共通 trim `τ` に対して

```text
T * j * log p
```

が modulo `2π` で第三象限 center target

```text
π + τ + T*ε
    < residue
    < 3π/2 - τ - T*ε
```

を cofinally hit することにほぼ尽きる。

本段では Mathlib の additive-circle irrational-rotation API を使い、

```text
Irrational ((T * log p) / (2π))
```

を明示仮定したとき、natural multiples `j * (T*log p)` が任意に大きい `j` で target を hit し、さらに actual real center の大きさから対応 cell index `k` も任意に大きく取れることを証明する。

これを CFZP-027 の

```text
Cfzp027CofinalReadyThirdQuadrantHitsForPrime
```

へ接続する。

**重要:** `W.rectangle.T` は一般の正実数なので、上記 irrationality は本段で自動証明してはいけない。これは explicit arithmetic/dynamical hypothesis として残す。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaAdditiveCircleIrrationalRotationCofinalHitAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaAdditiveCircleIrrationalRotationCofinalHitAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSubcriticalLargeCellCoefficientReadinessAudit
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic
```

実際の transitive import に応じて最小化してよい。

Mathlib には少なくとも次を利用できる:

```text
AddCircle.denseRange_zsmul_coe_iff

denseRange_zsmul_iff_nsmul

DenseRange.exists_mem_open
```

lemma 名・namespace は現在の Mathlib で確認して使うこと。

---

## 2. Gate A — fixed-prime rotation step / irrationality contract

fixed prime `p` の one-exponent phase incrementを first-class にする。

推奨:

```lean
noncomputable def cfzp028PrimePhaseRotationStep
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  W.rectangle.T * Real.log (p : ℝ)
```

period は `2 * Real.pi`。

irrationality contract:

```lean
def Cfzp028PrimePhaseRotationIrrational
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : Prop :=
  Irrational
    (cfzp028PrimePhaseRotationStep W p / (2 * Real.pi))
```

既存 center と step の exact identity:

```text
cfzpPrimePowerPhaseAngleCenter W p j
  = (j:ℝ) * cfzp028PrimePhaseRotationStep W p
```

を公開する。

`hp : Nat.Prime p` から step positivity も証明する:

```text
0 < cfzp028PrimePhaseRotationStep W p
```

`W.rectangle.hT` と `Real.log_pos` を使う。

---

## 3. Gate B — irrationality gives dense natural orbit

`a := cfzp028PrimePhaseRotationStep W p`、period `P := 2π` とする。

Mathlib の

```text
AddCircle.denseRange_zsmul_coe_iff
```

から integer multiples の dense range を得て、compact additive circle 上の

```text
denseRange_zsmul_iff_nsmul
```

を使って

```text
DenseRange (fun j : ℕ => j • (↑a : AddCircle P))
```

を得る theorem を作る。

概念形:

```lean
theorem cfzp028_denseRange_nsmul_primePhaseRotation
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    DenseRange (fun j : ℕ => j •
      (↑(cfzp028PrimePhaseRotationStep W p) : AddCircle (2 * Real.pi)))
```

必要な `Fact (0 < 2π)` instance は local `letI` / `haveI` で構成してよい。

---

## 4. Gate C — real fundamental target window

第三象限 center target の first-period endpoints を定義する。

```lean
noncomputable def cfzp028TargetLeft
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : ℝ :=
  Real.pi + τ + W.rectangle.T * ε

noncomputable def cfzp028TargetRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (τ : ℝ) : ℝ :=
  3 * Real.pi / 2 - τ - W.rectangle.T * ε
```

CFZP-027 の

```text
Cfzp027ThirdQuadrantTargetHasInterior ε W τ
```

から

```text
TargetLeft < TargetRight
```

を証明する。

さらに safe assumptions `0 < ε`, `0 < τ` と target interior から、target が fundamental period interior に入ることを示す:

```text
0 < TargetLeft
TargetRight < 2π
```

必要なら `0 ≤ ε` で十分な箇所は弱めてよい。

この target の quotient image を additive circle 上の nonempty open set として扱う。

実装方法は current Mathlib API に合わせること。候補:

- `AddCircle.openPartialHomeomorphCoe (2π) 0`
- `AddCircle.equivIco`
- quotient map の open-map API

低レベル quotient rewriting を無理に増やさない。

---

## 5. Gate D — dense natural orbit gives arbitrarily late target hits

単なる `∃ j` ではなく **任意 cutoff より後**を得る。

推奨 theorem shape:

```text
∀ J : ℕ, ∃ j : ℕ,
  J ≤ j ∧
  the additive-circle class of ((j:ℝ) * step)
    lies in the open target image
```

実装上は、dense natural orbitそのものを tail に変換してよい。

最も単純な考え方は、`J • a` だけ target を逆平行移動して、dense orbit `n • a` をその translated open set に当て、`j = J + n` とすることである。

概念:

```text
(J+n) • a = J • a + n • a
```

これにより「ℤ orbit density から正の index を作る」独自議論は不要。

可能なら再利用可能な generic lemma として

```text
DenseRange (fun n : ℕ => n • a)
  -> every nonempty open target is hit by some j ≥ J
```

を先に閉じてもよい。

---

## 6. Gate E — quotient hit lifts to an actual periodic cell index

Gate D の circle hit を、実数の

```text
TargetLeft + 2πk < (j:ℝ)*step
(j:ℝ)*step < TargetRight + 2πk
```

へ liftする。

`k` は最終的に `ℕ` で得ること。

推奨 route:

1. `AddCircle.equivIco` または `Int.fract` で representative `r ∈ [0,2π)` を取る。
2. target hit から `TargetLeft < r < TargetRight`。
3. floor/fract decomposition または quotient equalityから
   `((j:ℝ)*step) = r + 2π*z` (`z : ℤ`) を得る。
4. `hp : Nat.Prime p`, `0 < j` なら actual center は正、かつ target representative は `(π,3π/2)` 内なので `0 ≤ z` を示し `k := z.toNat` とする。

proof ergonomics が良ければ `Int.floor (((j:ℝ)*step)/(2π))` を直接 cell index に使ってよい。

この Gate の出口は CFZP-026 arithmetic hit:

```text
Cfzp026PrimePowerQuantitativeThirdQuadrantHit ε W p j k τ
```

open target hit は strict inequalityなので、026 の closed inequalitiesを直ちに満たす。

---

## 7. Gate F — cofinality in the cell index `k`

CFZP-027 provider は `j` だけでなく `k` も任意 cutoff より上を要求する。

step positivityから

```text
(j:ℝ) * step -> +∞
```

を使い、任意 `K` に対して sufficiently large `J_K` を選び、`j ≥ J_K` なら target lift の cell indexが `K ≤ k` になることを証明する。

`Tendsto Nat.cast atTop atTop` と positive constant multiplicationを再利用してよい。

専用補題として

```text
large j + target residue in first-period QIII target
  -> K ≤ lifted cell index
```

を切るとよい。

ここでは equidistribution/counting は不要。単に actual center が unbounded であることだけを使う。

---

## 8. Gate G — irrational rotation supplies CFZP-027 cofinal ready hits

最終 theorem:

```lean
theorem cfzp028CofinalReadyThirdQuadrantHitsForPrime_of_irrationalRotation
    {ε τ : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    {p : ℕ} (hp : Nat.Prime p)
    (hε : 0 < ε)
    (hτ : 0 < τ)
    (hτ4 : τ ≤ Real.pi / 4)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hinterior : Cfzp027ThirdQuadrantTargetHasInterior ε W τ)
    (hirr : Cfzp028PrimePhaseRotationIrrational W p) :
    Cfzp027CofinalReadyThirdQuadrantHitsForPrime ε W p τ
```

proof spine:

```text
hirr
  -> dense natural rotation orbit on AddCircle(2π)
  -> for every J/K, sufficiently late j hits open QIII target
  -> lift to natural cell index k ≥ K
  -> arithmetic quantitative hit

hsub
  -> CFZP-027 eventual readiness
  -> choose K beyond readiness threshold
  -> ReadyThirdQuadrantHit
```

注意: provider の `K` は任意入力なので、readiness threshold `K₀` と `max K K₀` を使う。

---

## 9. Gate H — optional direct downstream adapters

proof が短く保てるなら、Gate G と CFZP-027 を組み合わせた downstream adapter を追加してよい。

例:

```text
irrational rotation + subcritical + target interior
  -> cofinally many positive phase-core margins
```

または fixed prime の cofinal ready hits から、各 witnessについて CFZP-027 event/pulse credit を取得する theorem。

ただしまだ block dominanceへ飛ばさない。

---

## 10. Firewall / remaining gap

証明してはいけないもの:

- arbitrary `W` について `Cfzp027SubcriticalPhaseAspect W`
- arbitrary `W,p` について `Cfzp028PrimePhaseRotationIrrational W p`
- irrationalityの自動導出
- positive density / equidistribution / counting asymptotic
- Bad debt envelope の自動制御
- Good credit が Bad debt + current deficitを cofinally支配すること
- CFZP-024 certified block dominance provider
- CFZP-018 の無条件 provider
- infinite sum / joint limit / limit exchange
- RH

Gap marker例:

```lean
inductive Cfzp028AdditiveCircleIrrationalRotationCofinalHitGap : Prop
  | noIndependentPrimePhaseRotationIrrationalityProvider
  | noAutomaticSubcriticalWindowProvider
```

本段で **conditional phase-hit provider は閉じる**。残る Gap は phase-hitそのものではなく、その十分条件である window subcriticality / fixed-prime rotation irrationality の供給、およびその後の block credit-debt dominanceである。

---

## 11. roadmap / public import

- `DkMath/RH.lean` に新 module を追加。
- `0000-CFZP-roadmap.md` に CFZP-028 section を追加。

Green 条件:

```text
fixed-prime phase rotation step: CLOSED
rotation irrationality interface: CLOSED
irrationality -> dense natural AddCircle orbit: CLOSED
QIII fundamental target open/nonempty: CLOSED
arbitrarily late natural target hits: CLOSED
circle hit -> natural periodic cell lift: CLOSED
cofinal cell-index lift: CLOSED
irrational rotation -> CFZP-027 cofinal ready-hit provider: CONDITIONAL / CLOSED
independent irrationality provider: OPEN / GAP
subcritical-window provider: OPEN / GAP
block credit/debt dominance: OPEN / GAP
```

---

## 12. 実装姿勢

この段で重要なのは「density」という語を roadmap に追加することではなく、Mathlib の既存 irrational-rotation theorem を **CFZP-027 の exact arithmetic hit Propへ実際に接続すること**である。

最優先 spine:

```text
Irrational ((T*log p)/(2π))
        ↓
DenseRange natural multiples on AddCircle(2π)
        ↓
cofinally late hits of the open QIII center target
        ↓
lift to k : ℕ with k cofinal
        ↓
Cfzp026PrimePowerQuantitativeThirdQuadrantHit
        ↓
CFZP-027 readiness
        ↓
Cfzp027CofinalReadyThirdQuadrantHitsForPrime
```

ここが閉じれば、Good-side の phase-hit問題は conditional に完了し、次の本体は **cofinal Good credit と Bad debt の量的比較**へ移る。
