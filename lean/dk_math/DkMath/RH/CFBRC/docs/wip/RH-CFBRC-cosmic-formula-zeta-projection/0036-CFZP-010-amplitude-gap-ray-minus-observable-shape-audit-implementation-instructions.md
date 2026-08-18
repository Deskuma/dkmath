# CFZP-0036 — CFZP-010 amplitude-Gap / ray-minus observable-shape audit 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-0035
- Expected parent commit: `c107aedd3900a6f89ab51b78ca7ccb256062e866`
- 日本語を正本とする。

CFZP-0035 は Green-A closeout とする。

0031〜0035 により critical-line phase toolkit は branch-free に閉じた。

```text
GammaR unit carrier
Hardy/projective normalization
Cartesian angular velocity
Re(zeta'/zeta)
Re(zeta'/zeta) = - RiemannSiegelPhaseRate
```

以後 phase investigation は拡張しない。

CFZP-009 で残った source-side frontier は次の二つである。

```text
1. finite/cofinal common-baseline reach provider
2. amplitude-side Gap -> source ray-minus whole exact projection
```

ただし 2 を直接 equality として攻める前に、両 observable の shape が本当に同一かを exact に監査する。

---

## 1. 010 の中心問題

CFZP-004 の amplitude-side Gap は、same-height critical mirror pair の modewise amplitude difference を二乗した diagonal ledger である。

既存 exact surface:

```text
cfzpAggregateMirrorMinusWholeUpTo X delta
  = cfzpAggregateMirrorGapUpTo X delta
```

また carrier-weighted 版は

```text
cfzpAggregateCarrierWeightedMirrorGapUpTo X s
  = sum_q cost(q) * normSq(cfzpSameHeightMirrorModeDifference q s)
```

である。

一方 CS17/CS25 の source ray-minus whole は、各 prime `p` について finite geometric ray を先に複素和として圧縮し、normalized state

```text
Z = pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ...
```

を作ったあと

```text
rayMinusDensity = normSq (Z - 1)
```

を `t` で積分し、さらに prime weight `log p` で aggregate したものである。

したがって両者の間には少なくとも次の三つの構造差がある。

```text
A. same-height mirror amplitude difference
   vs finite geometric source ray mode

B. sum of modewise normSq
   vs normSq of a finite complex mode sum
   => Gram / interference cross terms

C. pure difference-square Gap
   vs normSq(Z - 1)
   => baseline 1 and signed interaction
```

010 はこの差を exact に可視化し、旧 backlog

```text
amplitude Gap -> ray-minus whole equality
```

を、必要なら

```text
mode transform + interference ledger + normalization bridge
```

へ再分類する。

010 では bridge provider 自体を証明しなくてよい。

---

## 2. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaAmplitudeGapRayMinusObservableShapeAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaAmplitudeGapRayMinusObservableShapeAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideNormalizedRayPolarizationOrderingAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic
```

0035 phase moduleを source-side dependency に混ぜない。

---

## 3. Gate A — amplitude-side diagonal Gap surface を固定

既存 CFZP-004 API を adapter として公開する。

必須:

```text
amplitudeMinusWhole_X(delta) = amplitudeGap_X(delta)
```

および carrier-weighted 版

```text
carrierWeightedGap_X(s)
  = sum_q cost(q) * normSq(sameHeightMirrorModeDifference(q,s))
```

を 010 namespace / theorem family から参照できるようにする。

新しい定義を無意味に複製しない。

可能なら、critical center `delta = 0` で amplitude Gap が零になる既存 theorem も adapter として公開する。

この Gate の目的は「amplitude Gap は modewise diagonal quadratic ledger」であることを明示すること。

---

## 4. Gate B — source ray-minus whole の exact normalized shape

CS17/CS25 から pointwise exact に

```text
rayMinusDensity = normSq (Z - 1)
```

を公開する。

さらに pure complex algebra として

```text
normSq (Z - 1)
  = normSq Z + 1 - 2 * Z.re
```

を theorem にする。

既存 `CommonDensity - InteractionDensity` theorem がそのまま使える場合は adapter にする。

aggregate についても既存

```text
Eminus_X = C_X - I_X
```

を 010 の shape theorem として参照できるようにする。

ここで `Eminus_X` を amplitude Gap と呼ばない。

---

## 5. Gate C — finite ray が「和を先に作る」ことを明示

既存

```lean
pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_weighted_compression
pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_endpoint_div
```

等を調査し、各 prime `p` の normalized ray stateが finite geometric sum / geometric compression であることを最も簡潔な exact theorem として公開する。

目標概念形:

```text
Z_p,X(t)
  = weight(t) * sum_{j=1}^{m(X,p)} r_p(t)^j
```

既存 API が finite sum form をすでに持つなら再利用する。

既存 API が compression

```text
weight * (r - r^(m+1)) / (1-r)
```

までしか持たない場合は、それを public surface として採用してよい。

重要なのは「source ray は prime-power mode を複素和にしてから quadraticize する」ことを exact に固定すること。

---

## 6. Gate D — generic finite Gram / interference decomposition

source ray の quadraticization に cross term が不可避であることを一般 finite theorem として固定する。

推奨は `Finset` 上の複素族 `a : ι -> ℂ` に対して

```text
normSq (sum i in S, a i)
  = sum i in S, sum j in S,
      Re(conj(a i) * a j)
```

の exact theorem。

その後、安価なら diagonal/off-diagonal split を追加する。

概念形:

```text
normSq(sum a_i)
  = sum normSq(a_i) + Cross(S,a)
```

ここで `Cross` は ordered off-diagonal sumでも unordered pairの `2*Re` sumでもよい。Lean proof ergonomics を優先する。

必須なのは、modewise diagonal ledgerだけでは source ray normSq を一般には回収できないことを exact に表すこと。

一般 counterexample も一つ置く。

例:

```text
a1 = 1, a2 = 1
normSq(a1 + a2) = 4
normSq(a1) + normSq(a2) = 2
```

これにより

```text
normSq(sum modes) = sum normSq(modes)
```

は pure algebra からは出ないことを記録する。

---

## 7. Gate E — amplitude Gap と source ray-minus の三層 mismatch classification

010 の中心 closeout。

次を一つの exact / explicit classification surface にまとめる。

```text
amplitude side:
  same-height mirror difference
  -> modewise normSq
  -> diagonal Gap ledger

source ray side:
  finite geometric mode sum
  -> normSq(sum)
  -> diagonal + Gram/interference
  -> minus baseline/interaction via normSq(Z - 1)
```

直接 equality を証明しようとしない。

少なくとも次の frontier を一個だけ残す。

```lean
inductive Cfzp010AmplitudeGapToRayMinusSameObservableBridgeGap : Prop
  | noExactModeTransformInterferenceNormalizationBridgeProvided
```

marker の docstring には、欠けているものを

```text
1. mirror amplitude mode -> source geometric mode transform
2. Gram/interference transport
3. baseline 1 / interaction normalization
```

と明記する。

旧 `Cfzp006AmplitudeGapToRayMinusWholeProjectionGap` を単に rename して終えない。010 の成果は、なぜ bridge が一段の equality ではないかを theorem 群で説明すること。

---

## 8. 010 closeout / roadmap reclassification

module が Green なら ROADMAP を更新する。

期待する分類:

```text
CFZP-010 Green-A:
  direct amplitude-Gap = ray-minus-whole target is not justified by current algebra.
  The correct bridge, if it exists, must transport modes and retain interference
  plus the source baseline/interaction normalization.
```

この時点で source-side frontier は

```text
A. common-baseline finite/cofinal reach provider
B. mode-transform + interference + normalization bridge
```

へ整理される。

010 の結果だけで `A` も `B` も証明済み扱いしない。

次段階は 010 の audit 結果を見て決める。

---

## 9. Firewall

禁止:

- `Complex.arg`
- global `Complex.log` branch の新規導入
- infinite Euler product / cutoff limit exchange
- `normSq(sum) = sum normSq` の無条件使用
- amplitude Gap と ray-minus whole の rename equality
- RH 結論
- RH-equivalent research boundary を provider として使うこと

許可:

- finite `Finset` algebra
- `Complex.normSq`
- finite geometric sums
- existing Mellin weight / ray APIs
- exact Gram / cross-term decomposition
- generic finite countermodel

---

## 10. Green 条件

Green-A:

- amplitude-side diagonal Gap surface が正確に再公開される。
- source ray-minus の `normSq(Z-1)` / common-interaction shape が exact に再公開される。
- source ray が finite complex mode sum/compression であることが exact に固定される。
- finite Gram/interference decomposition が証明される。
- direct diagonal equality が一般には成立しないことが countermodel で固定される。
- bridge frontier が `mode transform + interference + normalization` として一個に再分類される。
- no `sorry`, `admit`, `axiom`, `native_decide` in new module.
- `DkMath.RH` public import を追加する。
- roadmap を更新する。

Green-B:

- generic Gram theorem か finite ray compression surfaceの一部が既存 API 制約で弱くなるが、direct equality の不適切さと corrected bridge shape は exact に固定できる。

Red:

- cross term を捨てる。
- amplitude Gap を ray-minus whole と定義で同一視する。
- source ray の `-1` baseline を無視する。
- infinite / RH-equivalent provider を導入する。
