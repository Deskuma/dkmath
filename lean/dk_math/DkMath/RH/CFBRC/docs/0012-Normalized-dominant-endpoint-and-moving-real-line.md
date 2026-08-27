# 0012 — Normalized dominant endpoint と moving real line

## 1. 目的

`0011-Eta-critical-mirror-endpoint-energy-collapse-and-outer-normalization.md` では、standard nontrivial zeta zero において original / critical-mirror の finite eta endpoint がともに `0` へ収束し、その結果 endpoint TotalEnergy / Big / Gap / outer Big もすべて `0` へ collapse することを確認した。

この absolute collapse だけを観測している限り、off-critical zero と critical-line zero を区別する位置情報は失われる。

本書では、その次の事実層として、dominant index power によって endpoint を正規化し、さらに pair-left base rotation によって moving frame へ移すことで、off-critical zero 上に **非零の asymptotic carrier** が残ることを記録する。

ここで重要なのは、`endpoint → 0` と `normalized endpoint → nonzero limit` が矛盾しないことである。後者は消失速度を dominant scale で割った相対量を観測している。

---

## 2. 対象モジュール

主対象は次である。

```text
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameNormalizedEvenDefectEndpointAsymptotic
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingRealLine
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameMovingLineCollisionContracts
```

この層では `EtaCriticalMirrorPairedFrameMovingLineCollisionCore` の collision theorem 自体にはまだ進まない。

まず collision に必要な三要素のうち、

```text
local moving-line lock
noncollapse
fixed global-line lock
```

の前二者がどこまで Core として得られているかを固定する。

---

## 3. pair-left moving real line

`EtaCriticalMirrorPairedFrameMovingRealLine.lean` は、複素方向 `direction` が張る実一次元部分空間を

```lean
noncomputable def complexRealLine (direction : ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, z = direction * (r : ℂ)}
```

として定義する。

pair-left moving line は

```lean
noncomputable def etaPairMovingRealLine
    (s : ℂ) (k : ℕ) : Set ℂ :=
  complexRealLine (etaPairBaseCounterRotation s k)
```

である。

したがって line の方向そのものが truncation / pair index `k` に依存して回転する。

これは fixed real axis ではなく、eta pair の base phase に追随する moving frame である。

---

## 4. base rotation で moving line を実軸へ戻す

moving line の定義は、base rotation を掛けると ordinary real axis に戻るよう選ばれている。

```lean
theorem etaPairMovingRealLine_mem_iff_baseRotation_mul_mem_realAxis
    (s : ℂ) (k : ℕ) (z : ℂ) :
    z ∈ etaPairMovingRealLine s k ↔
      etaPairBaseRotation s k * z ∈ complexRealAxis
```

したがって moving-line membership は、rotated value の虚部が `0` であることと同値になる。

```lean
theorem mem_etaPairMovingRealLine_iff_defect_eq_zero
    (s : ℂ) (k : ℕ) (z : ℂ) :
    z ∈ etaPairMovingRealLine s k ↔
      etaPairMovingRealLineDefect s k z = 0
```

ここで

```lean
etaPairMovingRealLineDefect s k z
```

は `etaPairBaseRotation s k * z` の imaginary part である。

この設計により、回転する line の幾何を実数値 transverse defect として扱える。

---

## 5. spectral translation に対する幾何

moving line は実方向 spectral translation に対して不変である。

```lean
theorem etaPairMovingRealLine_add_real
```

一方、虚方向 translation に対しては logarithmic phase rotation を受ける。

```lean
theorem etaPairMovingRealLine_add_imag_mem_iff
```

したがって、real coordinate と imaginary spectral coordinate の役割が分離されている。

real shift は line を変えず、imaginary shift が phase を回転させる。

この性質は後の nonresonance / moving-line collision で重要になる。

---

## 6. normalized rotated endpoint

absolute endpoint collapse 後の情報を取り出すため、dominant index power で normalized した even defect endpoint を使う。

さらに pair-left frame へ運ぶ量が

```lean
noncomputable def etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
    (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  etaPairBaseRotation s k *
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k
```

である。

rotation は unit norm なので、normalized endpoint の norm は保存される。

```lean
theorem norm_etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint
```

したがって moving frame への移送は大きさを変更せず、phase だけを除去する gauge change として働く。

---

## 7. zero locus 上の endpoint と defect tail

nonreal nontrivial zeta zero `s` では、rotated normalized even endpoint と rotated normalized defect tail の間に exact identity がある。

```lean
theorem etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint_eq_neg_rotatedDefectTail
```

内容は、zero-locus 上で normalized finite endpoint が defect tail の負号付き表現になる、というものである。

ここでは単なる近似ではなく有限 index `k` ごとの exact identity が使われる。

そのため defect tail の asymptotic が得られれば、endpoint 側へ直接移送できる。

---

## 8. asymptotic certificate

この情報は次の structure にまとめられる。

```lean
structure EtaCriticalMirrorNormalizedEvenDefectEndpointAsymptoticCertificate
    (a : ℝ) (s C : ℂ) : Prop where
  rotated_endpoint_tendsto :
    Tendsto
      (etaCriticalMirrorIndexNormalizedRotatedEvenDefectEndpoint a s)
      atTop (nhds (-C))
  endpoint_norm_tendsto :
    Tendsto
      (fun k : ℕ =>
        ‖etaCriticalMirrorIndexNormalizedEvenDefectEndpoint a s k‖)
      atTop (nhds ‖C‖)
  norm_limit_ne_zero :
    ‖C‖ ≠ 0
```

この certificate が重要なのは、rotated value の limit だけでなく、gauge-invariant な norm limit が **非零** であることまで保持する点である。

つまり phase をどの frame で読むかに依存せず、carrier 自体が collapse していないことを保証する。

---

## 9. critical line の左右で dominant side を選ぶ

critical line の右側では mirror side が dominant となり、次が証明されている。

```lean
theorem etaCriticalMirrorRightNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
```

左側では original side が dominant となる。

```lean
theorem etaCriticalMirrorLeftNormalizedEvenDefectEndpointAsymptoticCertificate_of_zero
```

したがって off-critical zero では必ず左右どちらか一方に nonzero normalized asymptotic certificate が存在する。

```lean
structure EtaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate
    (s : ℂ) : Prop
```

および

```lean
theorem etaCriticalMirrorOffCriticalDominantEndpointAsymptoticCertificate_of_zero
```

がその side-aware package である。

ここで初めて、critical mirror の左右を単純に同じ scale で比較するのではなく、その側で支配的な decay scale を選択する。

---

## 10. rate collapse は off-critical zero では不可能

非零 norm limit を持つため、dominant normalized endpoint が `0` へ rate collapse することはできない。

左右それぞれについて

```lean
theorem not_etaCriticalMirrorRightIndexNormalizedEvenDefectEndpointRateCollapse

theorem not_etaCriticalMirrorLeftIndexNormalizedEvenDefectEndpointRateCollapse
```

が証明されている。

さらに side-aware provider 全体について

```lean
theorem not_etaCriticalMirrorZeroLocusDominantEndpointRateCollapse_of_offCriticalZero
```

が成立する。

したがって、absolute eta endpoint は zero locus 上で `0` へ収束する一方、off-critical と仮定して dominant scale で正規化すると、carrier は非零のまま残る。

これは本ルートにおける重要な noncollapse Core である。

---

## 11. concrete dominant carrier

`MovingLineCollisionContracts.lean` では左右の dominant side を一つの carrier にまとめる。

```lean
noncomputable def etaCriticalMirrorDominantNormalizedEndpointCarrier
    (k : ℕ) (s : ℂ) : ℂ :=
  if s.re ≤ (1 : ℝ) / 2 then
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint s.re s k
  else
    etaCriticalMirrorIndexNormalizedEvenDefectEndpoint
      (criticalMirror s).re s k
```

この定義は desired global line や RH の結論を使っていない。

左右の asymptotic analysis から直接構成される side-aware local carrier である。

---

## 12. local moving-line lock

carrier が off-critical zero 上で local pair-left moving line に近づく性質は

```lean
def EtaCriticalMirrorOffCriticalLocalMovingLineLock
    (carrier : ℕ → ℂ → ℂ) : Prop
```

として抽象化される。

具体 carrier については無条件に証明済みである。

```lean
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_localMovingLineLock :
    EtaCriticalMirrorOffCriticalLocalMovingLineLock
      etaCriticalMirrorDominantNormalizedEndpointCarrier
```

内容は、off-critical zero において

```text
moving-line transverse defect → 0
```

というものである。

つまり normalized dominant carrier は、pair index とともに回転する local real line へ asymptotically lock する。

---

## 13. noncollapse contract

collision に必要なもう一つの条件は、同じ carrier が大きさを失わないことである。

```lean
def EtaCriticalMirrorOffCriticalCarrierNoncollapse
    (carrier : ℕ → ℂ → ℂ) : Prop
```

これは、ある `c > 0` が存在し、十分大きな `k` で

```text
c ≤ ‖carrier k s‖
```

となることを要求する。

具体 carrier については

```lean
theorem etaCriticalMirrorDominantNormalizedEndpointCarrier_noncollapse :
    EtaCriticalMirrorOffCriticalCarrierNoncollapse
      etaCriticalMirrorDominantNormalizedEndpointCarrier
```

が証明済みである。

この theorem は前節の nonzero norm asymptotic certificate を使っている。

---

## 14. ここまでで閉じたもの

本段階で Lean Core として閉じているのは次である。

```text
absolute endpoint → 0
↓
dominant-scale normalization
↓
off-critical dominant normalized endpoint → nonzero asymptotic size
↓
pair-left rotation
↓
local moving real line への transverse defect → 0
↓
同一 carrier の eventual norm lower bound > 0
```

したがって、後の collision theorem に必要な

```text
local moving-line lock
noncollapse
```

は concrete carrier に対して既に Core である。

---

## 15. まだ閉じていないもの

`MovingLineCollisionContracts.lean` は、さらに fixed global line provider を次の structure として要求する。

```lean
structure EtaCriticalMirrorGlobalZeroLineLock
    (carrier : ℕ → ℂ → ℂ) where
  globalDirection : ℂ → ℂ
  globalDirection_ne_zero : ...
  carrier_tendsto_global_line : ...
```

これは同じ concrete carrier が、index `k` に依存しない一つの global direction の real line にも asymptotically lock することを要求する。

この段階では、その provider を local moving-line lock や noncollapse から自動的に得ることはできない。

したがって状態は

```text
local moving-line lock: CLOSED
carrier noncollapse: CLOSED
fixed global-line lock: separate provider
```

である。

---

## 16. audit: positive sequence tending to zero との違い

本層の役割は、単に「何かが zero へ行く」ことではない。

absolute endpoint は実際に zero へ行く。

一方、その dominant decay scale を除去した normalized endpoint は nonzero norm limit を持つ。

したがって後の contradiction は

```text
positive quantity → 0
```

のような不正な議論ではなく、**非零の同一 carrier が二つの非整合な line constraint を同時に満たせるか**という same-object collision 問題へ変換される。

この変換が `0011` の absolute collapse から moving-line route へ移る数学的意味である。

---

## 17. 次の依存地層

次に記録すべきなのは moving-line collision のための rotation nonresonance と generic collision Core である。

特に

```text
EtaPairProjectiveUnitRotation
EtaPairProjectiveTwoScaleNonresonanceCertificate
etaCriticalMirror_re_eq_half_of_movingLine_globalLine_collision_core
```

の関係を整理する必要がある。

そこで初めて、

```text
nonzero same carrier
+ local moving line
+ fixed global line
+ projective nonresonance
→ off-critical impossible
```

という collision theorem が完成する。
