# 0013 — Projective two-scale nonresonance と moving-line collision Core

## 1. この文書の位置

`0012-Normalized-dominant-endpoint-and-moving-real-line.md` では、absolute eta endpoint が零へ収束した後でも dominant power による正規化を行うと、off-critical zero 上で非零の carrier が残り、その carrier が pair-left moving real line に漸近的に lock することを確認した。

本書では、その次の論理層を記録する。

主対象は次の二モジュールである。

```text
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionContracts
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionCore
```

ここで行われていることは、個別の zeta / eta 展開をさらに進めることではない。

すでに得られた非零 carrier が

1. 局所的な moving line に漸近的に載ること、
2. 同時に一つの fixed global line に漸近的に載ること、
3. carrier 自身は潰れないこと、
4. moving line の回転が二つの独立スケールで projectively nonresonant であること、

を組み合わせて、off-critical configuration を排除する抽象 collision theorem を証明する層である。

重要なのは、この collision theorem 本体は条件付きながら Lean Core として証明済みである一方、具体的 dominant endpoint carrier に対する fixed global-line provider は別問題として分離されていることである。

---

## 2. projective real-line geometry

complex real line では、方向 `direction` と `-direction` は同じ実一次元部分空間を張る。

したがって ordinary phase resonance の `z = 1` だけでなく、

```lean
z = 1 ∨ z = -1
```

を同一の projective triviality とみなす必要がある。

そのため現行実装では次を定義する。

```lean
def EtaPairProjectiveUnitRotation (z : ℂ) : Prop :=
  z = 1 ∨ z = -1
```

これは単なる技術的緩和ではない。

moving **vector** ではなく moving **real line** を比較している以上、向きが反転した `-1` も幾何学的には同じ line だからである。

---

## 3. 二スケール projective nonresonance

`MovingLineCollisionContracts` は、half-density schedule と full-density schedule の二種類の block rotation を用いる。

中心 theorem は次である。

```lean
theorem etaPairHalf_or_fullDensityBlockSchedule_rotationLimit_not_projectively_trivial
    {s : ℂ} (him : s.im ≠ 0) :
    ¬ EtaPairProjectiveUnitRotation
        (etaPairHalfDensityBlockSchedule.scheduledBlockRotationLimit s) ∨
      ¬ EtaPairProjectiveUnitRotation
        (etaPairFullDensityBlockSchedule.scheduledBlockRotationLimit s)
```

したがって `s.im ≠ 0` なら、二つの scheduled rotation limit が同時に projectively trivial になることはない。

証明の考え方は次である。

projectively trivial な unit rotation は `±1` なので、その平方は必ず `1` になる。

そこで hypothetical に half / full の両 limit が `±1` であると仮定すると、height を `2 * s.im` へ持ち上げたとき、対応する doubling / tripling rotation が双方 ordinary resonance `= 1` を起こす。

しかし既存の `etaPairTwoScaleRotation_nonresonant` が、非零 height において doubling / tripling の少なくとも一方は resonance しないことを保証している。

これにより同時 projective resonance が排除される。

この結果は certificate としても package される。

```lean
structure EtaPairProjectiveTwoScaleNonresonanceCertificate
    (s : ℂ) : Prop where
  doubling_rotation_tendsto : ...
  tripling_rotation_tendsto : ...
  at_least_one_limit_not_projectively_trivial : ...
```

そして

```lean
theorem etaPairProjectiveTwoScaleNonresonanceCertificate_of_im_ne_zero
```

により、任意の `s.im ≠ 0` でこの certificate が構成される。

ここには RH 仮定は入っていない。

---

## 4. collision theorem が要求する三つの provider

抽象 carrier

```lean
carrier : ℕ → ℂ → ℂ
```

に対して、collision theorem は三種類の情報を要求する。

### 4.1 local moving-line lock

```lean
def EtaCriticalMirrorOffCriticalLocalMovingLineLock
    (carrier : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    s.re ≠ (1 : ℝ) / 2 →
    Tendsto
      (fun k : ℕ =>
        etaPairMovingRealLineDefect s k (carrier k s))
      atTop (nhds 0)
```

これは off-critical zero 上で carrier が pair-left moving real line に漸近的に載ることを表す。

`0012` で確認した concrete carrier

```lean
etaCriticalMirrorDominantNormalizedEndpointCarrier
```

については、次が既に証明済みである。

```lean
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock :
    EtaCriticalMirrorOffCriticalLocalMovingLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier
```

したがって local lock は Gap ではない。

### 4.2 carrier noncollapse

```lean
def EtaCriticalMirrorOffCriticalCarrierNoncollapse
    (carrier : ℕ → ℂ → ℂ) : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    s.re ≠ (1 : ℝ) / 2 →
    ∃ c : ℝ,
      0 < c ∧
        ∀ᶠ k : ℕ in atTop, c ≤ ‖carrier k s‖
```

これは carrier の norm が eventually 正の一定値 `c` 以上に保たれることを要求する。

concrete dominant normalized endpoint carrier については、左右それぞれの非零 asymptotic constant から

```lean
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse :
    EtaCriticalMirrorOffCriticalCarrierNoncollapse
      etaCriticalMirrorDominantNormalizedEndpointCarrier
```

が証明済みである。

したがって noncollapse も Gap ではない。

### 4.3 fixed global-line lock

残る provider は次である。

```lean
structure EtaCriticalMirrorGlobalZeroLineLock
    (carrier : ℕ → ℂ → ℂ) where
  globalDirection : ℂ → ℂ
  globalDirection_ne_zero : ...
  carrier_tendsto_global_line : ...
```

これは各 zeta zero `s` に対して、`k` に依存しない一つの非零 complex direction を選び、その fixed real line へ同じ carrier が漸近的に載ることを要求する。

ここで `globalDirection` は local moving line の回転方向とは別物である。

collision theorem の本質は、**同じ非零 carrier** が

- `k` とともに回転する local line、
- `k` に依存しない global line、

の双方へ同時に lock できるか、という一点にある。

---

## 5. same-object cancellation lemma

collision Core には、同じ carrier を使っていることを定量化する重要 lemma がある。

```lean
theorem tendsto_one_of_mul_sub_one_tendsto_zero_of_eventually_norm_lower_bound
    {q z : ℕ → ℂ} {c : ℝ}
    (hc : 0 < c)
    (hproduct :
      Tendsto (fun k : ℕ => (q k - 1) * z k) atTop (nhds 0))
    (hlower : ∀ᶠ k : ℕ in atTop, c ≤ ‖z k‖) :
    Tendsto q atTop (nhds 1)
```

意味は明快である。

もし

```text
(q_k - 1) z_k → 0
```

であり、同時に `z_k` が零へ潰れず norm に正の下界を持つなら、消失は `z_k` 側へ逃がせない。

したがって係数側が

```text
q_k → 1
```

を満たさなければならない。

これは CFBRC audit の言葉では **same-object step** である。

carrier が零へ潰れる場合には、任意の係数 mismatch を `z_k → 0` が吸収してしまうため collision は得られない。

だから `0012` で確立した noncollapse は補助条件ではなく、collision mechanism の必須条件である。

---

## 6. local line と global line から phase constraint を作る

collision proof では、fixed global line の方向を

```lean
let direction : ℂ := hglobal.globalDirection s
```

とし、projective phase を

```lean
let phase : ℂ := direction * (conj direction)⁻¹
```

と置く。

local moving-line lock からは、base rotation を掛けた carrier の imaginary component が零へ行く。

global-line lock からは、`direction⁻¹` を掛けた carrier の imaginary component が零へ行く。

複素数 `z` が実軸へ近づくことは

```text
z - conj z → 0
```

と同値な skew condition に変換できる。

proof は local / global の二つの skew residual を同じ `carrier k s` 上へ持ち込み、差し引くことで最終的に

```text
(phase * baseRotation_k^2 - 1) * carrier_k → 0
```

という same-object residual を作る。

そこで noncollapse lemma を適用すると

```text
phase * baseRotation_k^2 → 1
```

が強制される。

---

## 7. positive-density schedule との衝突

次の theorem は、上の phase-square convergence が成立すると、任意の positive-density block schedule の rotation limit が projectively trivial になることを示す。

```lean
theorem scheduledBlockRotationLimit_projectively_trivial_of_phaseSquare_tendsto_one
    (S : EtaPairPositiveDensityBlockSchedule)
    (s phase : ℂ)
    (hphase :
      Tendsto
        (fun k : ℕ =>
          phase * etaPairBaseRotation s k * etaPairBaseRotation s k)
        atTop (nhds 1)) :
    EtaPairProjectiveUnitRotation (S.scheduledBlockRotationLimit s)
```

したがって collision 仮定からは half-density schedule と full-density schedule の **双方** が projectively trivial になってしまう。

しかし §3 の two-scale nonresonance により、`s.im ≠ 0` なら少なくとも一方は projectively nontrivial でなければならない。

ここで contradiction が完成する。

---

## 8. generic moving-line collision theorem

以上を一つにまとめた theorem が次である。

```lean
theorem etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
    {carrier : ℕ → ℂ → ℂ}
    (hlocal : EtaCriticalMirrorOffCriticalLocalMovingLineLock carrier)
    (hnoncollapse : EtaCriticalMirrorOffCriticalCarrierNoncollapse carrier)
    (hglobal : EtaCriticalMirrorGlobalZeroLineLock carrier)
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2
```

論理構造は次である。

```text
NontrivialRiemannZetaZero s
+ s.im ≠ 0
+ local moving-line lock
+ carrier noncollapse
+ fixed global-line lock
+ projective two-scale nonresonance

→ off-critical assumption impossible
→ s.re = 1 / 2
```

ここで two-scale nonresonance は `s.im ≠ 0` から Core として自動供給される。

concrete dominant normalized endpoint carrier について local lock と noncollapse も Core として自動供給される。

したがって、この route を concrete carrier に適用するときの主要な外部入力は fixed global-line lock である。

---

## 9. Core / Beam / Gap 監査

### Core

現在 Lean で証明済みなのは次である。

- projective triviality `±1` の定義
- nonzero height における two-scale projective nonresonance
- projective nonresonance certificate
- concrete dominant normalized endpoint carrier の local moving-line lock
- 同 carrier の off-critical noncollapse
- same-object cancellation lemma
- phase-square constraint から scheduled block rotation の projective triviality
- generic moving-line / fixed-line collision theorem

### Beam

証明済み Beam は次である。

```text
normalized nonzero carrier
→ local moving-line lock
→ same-object phase residual
→ projective resonance requirement
→ two-scale nonresonance contradiction
→ critical line
```

### Gap / provider boundary

この generic theorem 自身が自動生成しないものは

```text
EtaCriticalMirrorGlobalZeroLineLock carrier
```

である。

特に、

```text
carrier が local moving line に載る
```

ことから

```text
carrier が一つの fixed global line にも載る
```

ことは従わない。

後者を前者の言い換えとして扱うと循環になる。

したがって concrete dominant endpoint carrier に対する global-line provider がどのような標準解析・completed-zeta・Euler carrier から独立に導出されるかを、後続文書では厳密に監査しなければならない。

---

## 10. 重要な firewall

### 10.1 nonresonance 単独では RH を証明しない

rotation が nonresonant であるだけでは何も衝突していない。

同じ nonzero carrier が local moving line と fixed global line の双方に拘束されて初めて contradiction になる。

### 10.2 noncollapse を外してはいけない

carrier が零へ行くなら

```text
(q_k - 1) carrier_k → 0
```

から `q_k → 1` は導けない。

absolute endpoint collapse をそのまま collision に使えなかった理由がここにある。

### 10.3 fixed global line は結論から作ってはいけない

`globalDirection` を `s.re = 1/2` や critical-line fixedness を前提として選ぶなら、その provider は RH を埋め込んでいるだけになる。

provider の出所は独立に audit されなければならない。

### 10.4 generic theorem の証明済み性と RH の証明済み性は別

conditional theorem

```text
local + noncollapse + global → critical line
```

が Lean で閉じていても、load-bearing `global` provider が未解決なら RH は閉じない。

---

## 11. この段階での構造理解

`0011` までの endpoint Gap route では、original と mirror がともに零へ縮むため差も自動的に零へ縮み、位置情報を失っていた。

`0012` で dominant scale を剥ぐことにより、off-critical では零へ潰れない carrier を抽出した。

`0013` では、その非零 carrier を使うことで初めて

```text
moving line と fixed line の同時拘束
```

を数学的 contradiction に変換できることが形式化されている。

したがってこの route の本質は

```text
Gap → 0
```

ではなく、

```text
同じ nonzero object に二つの incompatible line constraints を課す
```

ことに移っている。

これは CFBRC の collision 読解における重要な転換点である。

---

## 12. 次の依存層

次に監査すべきは generic collision theorem の残る concrete provider、すなわち

```text
EtaCriticalMirrorGlobalZeroLineLock
  etaCriticalMirrorDominantNormalizedEndpointCarrier
```

をどこから作ろうとしているかである。

現行 repository では completed-zeta slope、weighted complete eta tail、Euler half-endpoint carrier などを通してこの fixed global-line condition を具体化する系列が存在する。

ただし research roadmap 自身は、最終的な dominant Euler half-endpoint transverse collapse が `RiemannHypothesis` と論理同値であることを明記している。

したがって後続文書では、

```text
何が unconditional Core まで閉じているか
```

と

```text
どの一点が RH-equivalent research boundary なのか
```

を混同せず、一段ずつ下流へ追跡する。
