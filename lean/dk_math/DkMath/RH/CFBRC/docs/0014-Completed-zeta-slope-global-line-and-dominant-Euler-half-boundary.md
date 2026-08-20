# 0014 — Completed-zeta slope global line と dominant Euler half research boundary

## 1. この文書の位置

`0013-Projective-two-scale-nonresonance-and-moving-line-collision-core.md` では、generic moving-line collision Core を記録した。

同じ非零 carrier が

```text
local moving line
fixed global line
```

の双方へ asymptotically lock し、さらに projective two-scale nonresonance が成立すると、off-critical nontrivial zero は存在できない。

具体的な dominant normalized endpoint carrier については、local moving-line lock と noncollapse は既に Core として閉じていた。

したがって残る大きな入力は fixed global-line provider である。

本書では、その fixed line が completed-zeta canonical slope からどこまで無条件に得られているか、またどこから先が RH-equivalent research boundary になるかを記録する。

主対象は次である。

```text
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfRHEquivalenceAudit
DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameCompletedZetaRelativePhaseCollision
```

---

## 2. completed-zeta canonical slope carrier

`EtaCriticalMirrorPairedFrameCompletedZetaEulerMainLineReduction` では、nearby `GammaR * zeta` value を canonical displacement で割った carrier

```lean
etaCriticalMirrorNormalizedNearbyGammaZetaCarrier
```

が定義される。

standard nontrivial zeta zero `s` 上では、これは既存の

```lean
completedZetaCanonicalSlopeCarrier
```

と exact に一致する。

```lean
theorem etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_eq_slopeCarrier_of_zero
```

さらに、この carrier は

```lean
completedZetaCanonicalSlopeDirection s
```

が張る fixed complex real line へ asymptotically lock する。

```lean
theorem etaCriticalMirrorNormalizedNearbyGammaZetaCarrier_tendsto_global_line
```

したがって completed-zeta 側には、zero locus から得られる canonical fixed direction と、その方向へ lock する explicit nearby carrier が既に存在する。

この部分は研究仮定ではない。

---

## 3. Euler-main mismatch の縮約

completed-zeta nearby carrier と weighted eta tail の Euler-main carrier の transverse mismatch は、

```text
Euler-main transverse defect
-
nearby completed-zeta slope-carrier defect
```

という exact difference に書ける。

```lean
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseError_eq_main_sub_nearby
```

nearby slope carrier 側の transverse defect は既に `0` へ収束するため、completed-zeta / Euler-main mismatch collapse は、Euler-main carrier 自身の fixed-line collapse と同値になる。

```lean
theorem etaCriticalMirrorWeightedTailCompletedZetaNearbyEulerMainTransverseCollapse_iff_mainCarrier
```

ここで fixed-line 問題は、completed-zeta carrier 自体の line lock ではなく、eta 側 Euler-main carrier をその同じ line へ載せる問題へ縮約される。

---

## 4. dominant half と suppressed half

`EtaCriticalMirrorPairedFrameCompletedZetaDominantEulerHalfReduction` では、Euler-main carrier を

```text
dominant half
+
suppressed half
```

へ exact に分解する。

```lean
theorem etaCriticalMirrorDominantWeightedTailEulerMainCarrier_eq_dominant_add_suppressed
```

critical line 上では full Euler main carrier を保持する。

off-critical では、左右のうち slower-decaying な一方だけを

```lean
etaCriticalMirrorDominantEulerHalfEndpointCarrier
```

として残し、もう一方を

```lean
etaCriticalMirrorSuppressedEulerHalfEndpointCarrier
```

とする。

suppressed half は every nontrivial zero 上で `0` へ収束する。

```lean
theorem etaCriticalMirrorSuppressedEulerHalfEndpointCarrier_tendsto_zero
```

さらに completed-zeta slope frame で見た suppressed half の transverse defect も `0` へ収束する。

```lean
theorem etaCriticalMirrorSuppressedEulerHalfEndpointCarrierTransverseError_tendsto_zero
```

したがって Euler-main line collapse は、single dominant half-endpoint carrier の line collapse と同値になる。

```lean
theorem etaCriticalMirrorWeightedTailEulerMainCarrierTransverseCollapse_iff_dominantHalfEndpoint
```

この時点で asymptotically irrelevant な half は Core で除去済みである。

---

## 5. 最終 contract

残る contract は次である。

```lean
def EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse : Prop :=
  ∀ {s : ℂ},
    NontrivialRiemannZetaZero s →
    s.im ≠ 0 →
    Tendsto
      (fun k : ℕ =>
        etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseError k s)
      atTop (nhds 0)
```

これは、nonreal nontrivial zero 上で single dominant Euler half-endpoint carrier が completed-zeta canonical slope line に asymptotically入る、という主張である。

この contract が得られれば RH が従う。

```lean
theorem riemannHypothesis_of_dominantEulerHalfEndpointCarrierTransverseCollapse
```

しかし重要なのは、その逆も証明されていることである。

critical line 上では dominant Euler half carrier 自体が exact zero になる。

```lean
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrier_eq_zero_of_re_eq_half
```

したがって RH を仮定すれば transverse collapse contract は自動的に成立する。

```lean
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis
```

最終 audit theorem は次である。

```lean
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse ↔
      RiemannHypothesis
```

よって、この contract は RH より弱い独立補題ではない。

これは RH の explicit Euler-half / completed-zeta slope-language による exact reformulation である。

---

## 6. relative phase collision 側から見た同じ境界

`EtaCriticalMirrorPairedFrameCompletedZetaRelativePhaseCollision` は、completed-zeta slope direction と pair-left moving gauge の relative counter-rotation を明示する。

```lean
etaCriticalMirrorCompletedZetaRelativeCounterRotation
```

これは fixed completed-zeta unit direction と logarithmic base rotation の積に exact 分解される。

```lean
theorem etaCriticalMirrorCompletedZetaRelativeCounterRotation_eq_fixed_mul_exp
```

もしこの relative counter-rotation の imaginary part が `0` へ収束すると、その unit-complex square は `1` へ収束する。

すると half-density と full-density の block rotation limit が双方 projectively trivial になる。

しかし nonzero height では projective two-scale nonresonance が既に証明されているため、これは不可能である。

```lean
theorem not_etaCriticalMirrorCompletedZetaRelativeCounterRotation_im_tendsto_zero
```

したがって、off-critical zero に対して relative phase が asymptotically real になるという contract は contradiction を起こし、critical line を強制する。

```lean
theorem etaCriticalMirror_re_eq_half_of_completedZetaRelativePhaseImagCollapse
```

この route は collision mechanism 自体が既に強力であることを示す。

問題は、その relative phase collapse を zero-locus data から独立に導くことである。

---

## 7. Core / Gap 監査

### Core

次は Lean Core として閉じている。

- completed-zeta canonical slope direction の構成
- zero locus 上の nearby `GammaR * zeta` carrier と canonical slope carrier の一致
- nearby carrier の fixed slope-line lock
- weighted Euler remainder の除去
- suppressed Euler half-endpoint の decay
- Euler-main collapse と dominant-half collapse の同値
- relative phase collapse が nonzero height で projective nonresonance と衝突すること
- dominant-half transverse collapse から RH が従うこと
- RH から dominant-half transverse collapse が従うこと
- よって dominant-half transverse collapse と RH が論理同値であること

### Gap / research boundary

独立に必要なのは、zero-locus data から

```text
single dominant Euler half-endpoint carrier
```

を completed-zeta canonical fixed slope line に入れる新しい analytic identity または estimate である。

現行 audit では、その contract 自身を追加仮定として置くことは数学的進歩ではない。

なぜなら、その contract は既に RH と exact に同値だからである。

---

## 8. 証明地図

現在の reduction は次のように読める。

```text
standard nontrivial zeta zero
→ completed-zeta canonical slope direction
→ nearby GammaR*zeta slope carrier
→ fixed global slope-line lock                    [CLOSED]

weighted eta complete tail
→ Euler main + remainder
→ remainder transverse contribution               [REMOVED]
→ dominant half + suppressed half
→ suppressed half transverse contribution         [REMOVED]

残る single dominant Euler half
→ completed-zeta fixed slope line ?               [RH-EQUIVALENT]
→ moving-line / fixed-line same-carrier collision
→ projective two-scale nonresonance
→ Re(s)=1/2
```

この図で重要なのは、completed-zeta fixed line 自体が未構成なのではないことである。

fixed line とその canonical slope carrier は既に Core である。

残る一点は、eta 側の surviving dominant carrier と completed-zeta 側の fixed slope line を同じ-object geometry として接続することである。

---

## 9. 監査結論

この段階では、証明骨格の大部分は conditional plumbing ではなく explicit Core まで還元されている。

しかし最終 provider はまだ独立には得られていない。

特に

```text
EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse
```

をそのまま research assumption として採用して RH を導くことは、RH を別言語で仮定しているのと論理的に同じである。

したがって今後の数学的進歩とは、この contract を仮定せず、zero-locus の既知構造、completed-zeta、Euler half-endpoint、あるいは別の独立 arithmetic / analytic invariant から導出することである。

この境界を越えたとき初めて、moving-line collision route は RH の reformulation から proof へ進む。
