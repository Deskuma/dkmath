# 0010 — Eta critical mirror endpoint limits

## 1. 目的

本書は、standard nontrivial Riemann-zeta zero と、その same-height critical mirror に対して、有限 Dirichlet-eta endpoint がどのように零極限へ移送されるかを記録する。

前書 `0009-Standard-zeta-same-height-critical-mirror-zero-bridge.md` までで、非自明零点 `s` から `criticalMirror s` も再び非自明零点になることが Lean Core として固定された。

本書では、その零点対を eta の有限部分和列へ移し、同じ truncation index `N` によって観測される二本の endpoint sequence が、ともに `0` へ収束するところまでを固定する。

ここで重要なのは、本書が有限段階の exact closure を主張しないことである。

$$
\operatorname{etaPartialEndpoint}(N,s)\longrightarrow 0
$$

は、ある有限 `N` で endpoint が厳密に `0` になることを意味しない。

同様に original と mirror の両 endpoint が `0` へ収束することだけから、`s = criticalMirror s` も導けない。

したがって、本書は後の energy、paired-frame、collision 構造へ入るための解析的な **Core** を固定する文書である。

---

## 2. 対象モジュール

主対象は次である。

```text
DkMath.RH.CFBRC.EtaCriticalMirrorEndpointLimits
```

このモジュールは直接、次を import する。

```text
DkMath.RH.CFBRC.CriticalMirrorZeroBridge
DkMath.RH.Weave.Analytic.EtaPairedContinuation
```

eta 側の依存を下へたどると、主要な流れは次である。

```text
EtaFiniteClosure
  ↓
EtaPairDecomposition
  ↓
EtaLimitBridge
  ↓
EtaEvenPairing
  ↓
EtaPairedLimit
  ↓
EtaTermDecay
  ↓
EtaAbsoluteConvergence
  ↓
EtaFiniteFactorization
  ↓
EtaZetaIdentification
  ↓
EtaHalfPlaneReconstruction
  ↓
EtaPairedSummability
  ↓
EtaPairedIdentification
  ↓
EtaPairedHolomorphic
  ↓
EtaContinuationDomains
  ↓
EtaPairedContinuation
  ↓
EtaCriticalMirrorEndpointLimits
```

この長い依存列の役割は、形式的な alternating sum を置くだけではなく、**genuine finite eta endpoint sequence と analytic eta value の一致を解析的に証明すること**にある。

---

## 3. finite eta endpoint

有限 eta endpoint は `EtaFiniteClosure.lean` で定義される。

```lean
noncomputable def etaPartialEndpoint (N : ℕ) (s : ℂ) : ℂ :=
  finiteEndpoint (Finset.range N) (etaSignedVector s)
```

ここで `etaSignedVector` は、一始まりの Dirichlet eta

$$
1^{-s}-2^{-s}+3^{-s}-4^{-s}+\cdots
$$

に対応する genuine alternating vector である。

したがって `etaPartialEndpoint N s` は、単なる補助多項式ではなく、最初の `N` 項を実際に足した有限 Dirichlet-eta endpoint である。

また有限段階では

```lean
theorem etaPartialEndpoint_eq_positive_sub_negative
```

により、positive block と negative block の exact difference として分解される。

さらに

```lean
theorem etaPartialEndpoint_eq_zero_iff_parity_balance
```

によって、有限 endpoint の exact zero は二つの parity block の exact equality と同値である。

この finite exact statement と、本書で扱う infinite limit statement は区別しなければならない。

---

## 4. 偶数 truncation と paired difference

`EtaEvenPairing.lean` は、一つの paired eta term を

```lean
noncomputable def etaPairTerm (s : ℂ) (k : ℕ) : ℂ :=
  etaUnsignedVector s (2 * k) - etaUnsignedVector s (2 * k + 1)
```

と定義する。

一始まりでは

$$
(2k+1)^{-s}-(2k+2)^{-s}
$$

に対応する。

最初の `K` pair の有限和は

```lean
noncomputable def etaPairedPartial (K : ℕ) (s : ℂ) : ℂ :=
  (Finset.range K).sum (etaPairTerm s)
```

である。

そして重要な有限恒等式として

```lean
theorem etaPartialEndpoint_two_mul_eq_etaPairedPartial
    (K : ℕ) (s : ℂ) :
    etaPartialEndpoint (2 * K) s = etaPairedPartial K s
```

が証明されている。

ここには極限も解析接続も使われない。

したがって paired representation は infinite series の並べ替えから導入されるのではなく、まず有限 truncation 上の exact identity として固定されている。

これは後の解析を安全に進めるための重要な Core である。

---

## 5. paired eta が `Re(s) > 0` で収束する理由

通常の unsigned zeta series は絶対収束領域として `Re(s) > 1` を持つ。

一方、隣接二項を差し引いた `etaPairTerm` には一段追加の減衰が生じる。

`EtaPairedSummability.lean` では、`0 < s.re` の下で

```lean
theorem norm_etaPairTerm_le_summableMajorant
```

を証明し、概念的には

$$
\lVert\operatorname{etaPairTerm}(s,k)\rVert
\lesssim
\lVert s\rVert(k+1)^{-\Re(s)-1}
$$

という summable majorant を得ている。

その結果、

```lean
theorem etaPairedSummableAt_of_pos_re
    {s : ℂ} (hre : 0 < s.re) :
    EtaPairedSummableAt s
```

が成立する。

さらに even / odd subsequence を同じ極限へ glue することで、完全な finite eta endpoint sequence について

```lean
theorem etaPartialEndpoint_tendsto_pairedTsum_of_pos_re
```

が証明される。

したがって `Re(s) > 0` では、有限 endpoint 列そのものが paired infinite sum へ収束する。

---

## 6. paired infinite sum と analytic eta の同定

paired sum が収束するだけでは、それが standard zeta と結び付いた analytic eta と同じ値であるとはまだ言えない。

DkMath はこの二つを意図的に分離している。

```lean
def EtaPairedTsumIdentifiesAnalyticAt (s : ℂ) : Prop :=
  (∑' k : ℕ, etaPairTerm s k) = analyticEta s
```

`analyticEta` は

```lean
noncomputable def analyticEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
```

である。

まず `Re(s) > 1` の絶対収束領域では、finite factorization と zeta Dirichlet series を用いて、有限 eta endpoint の極限が `analyticEta s` に一致することを証明する。

その後、paired sum と genuine finite endpoint sequence が同じ極限を持つことから、極限の一意性によって

```lean
theorem etaPairedTsumIdentifiesAnalyticAt_of_one_lt_re
```

が得られる。

ここでも infinite series を危険に再配列して同一視するのではなく、**同じ finite sequence の極限の一意性**を使っている。

---

## 7. identity theorem による非実右半平面への延長

`EtaPairedHolomorphic.lean` は

```lean
noncomputable def etaPairedValue (s : ℂ) : ℂ :=
  ∑' k : ℕ, etaPairTerm s k
```

を定義し、`Re(s) > 0` 全体で holomorphic であることを証明する。

一方、raw zeta-product の `analyticEta` は `s = 1` における Mathlib の zeta value と removable continuation の扱いを区別する必要がある。

そこで `EtaPairedContinuation.lean` は、実軸を避けた二つの領域

```text
upper-right : Re(s) > 0, Im(s) > 0
lower-right : Re(s) > 0, Im(s) < 0
```

を別々に扱う。

安全な anchor として

```lean
etaUpperAnchor = 2 + i
etaLowerAnchor = 2 - i
```

を取り、`Re(s) > 1` で既に証明した局所的一致を出発点に identity theorem を適用する。

その結果、

```lean
theorem etaPairedValue_eq_analyticEta_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    etaPairedValue s = analyticEta s
```

が証明される。

これにより、非実な open right half-plane 全体で paired eta の genuine infinite value と analytic eta が一致する。

---

## 8. finite eta endpoint の analytic eta への収束

前節までの結果を合成して、`EtaPairedContinuation.lean` は

```lean
theorem etaPartialConvergesAt_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    EtaPartialConvergesAt s
```

を証明する。

`EtaPartialConvergesAt s` の定義は

```lean
Tendsto (fun N : ℕ => etaPartialEndpoint N s)
  atTop (nhds (analyticEta s))
```

である。

したがって、ここで初めて genuine finite eta endpoint sequence と analytic continuation 側の値が、非実右半平面で直接結ばれる。

---

## 9. standard zeta zero から eta endpoint zero limit へ

`analyticEta` は standard zeta を因子として持つため、

```lean
theorem analyticEta_eq_zero_of_riemannZeta_eq_zero
    {s : ℂ} (hz : riemannZeta s = 0) :
    analyticEta s = 0
```

は直接得られる。

これと前節の convergence theorem を合成すると、

```lean
theorem etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s)
      atTop (nhds 0)
```

が成立する。

ここが standard zeta zero と finite eta dynamics をつなぐ主要な解析 bridge である。

---

## 10. nontrivial zero への特殊化

`EtaCriticalMirrorEndpointLimits.lean` は、`0009` までで固定した critical-strip Core を使用する。

非自明零点 `s` には

```lean
nontrivialRiemannZetaZero_re_pos hs
```

によって

$$
0<\Re(s)
$$

がある。

したがって `s.im ≠ 0` を与えれば、直ちに

```lean
theorem etaPartialEndpoint_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)
```

を得る。

これは original point 側の endpoint-zero limit である。

---

## 11. critical mirror 側も同じ truncation limit で消える

`0009` では

```lean
riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero
```

および

```lean
criticalMirror_re_pos_of_nontrivialRiemannZetaZero
```

が証明済みである。

また `criticalMirror` は虚部を保存するので、`s.im ≠ 0` なら mirror point の虚部も非零である。

これにより

```lean
theorem etaPartialEndpoint_criticalMirror_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
      atTop (nhds 0)
```

が得られる。

ここで original と mirror は、どちらも同じ自然数 index `N` を truncation parameter として持つ。

したがって後の paired-frame 構造では、異なる二種類の極限パラメータを後から同期させるのではなく、最初から共通 index の二本の endpoint sequence として扱える。

---

## 12. two-sided endpoint-vanishing certificate

二本の零極限は次の structure にまとめられる。

```lean
structure EtaCriticalMirrorEndpointVanishing (s : ℂ) : Prop where
  original : Tendsto (fun N : ℕ => etaPartialEndpoint N s) atTop (nhds 0)
  mirror : Tendsto (fun N : ℕ => etaPartialEndpoint N (criticalMirror s))
    atTop (nhds 0)
```

そして

```lean
theorem etaCriticalMirrorEndpointVanishing_of_nontrivialRiemannZetaZero
```

が、非実非自明零点からこの certificate を構成する。

この structure は後続モジュールにとって重要である。

original と mirror の零極限を別々の仮定として持ち回るのではなく、「同じ `s` の critical-mirror pair に対する二方向 endpoint vanishing」という一つの Lean object に固定できるからである。

---

## 13. mirror-minus-original displacement も zero へ行く

二本の sequence がともに `0` へ収束するため、その差も `0` へ収束する。

```lean
theorem etaCriticalMirrorEndpoint_sub_tendsto_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        etaPartialEndpoint N (criticalMirror s) - etaPartialEndpoint N s)
      atTop (nhds 0)
```

同様に和についても

```lean
theorem etaCriticalMirrorEndpoint_add_tendsto_zero_of_nontrivialRiemannZetaZero
```

がある。

したがって asymptotic level では、mirror pair の endpoint difference も sum も消える。

ただし、この事実の意味を過大評価してはならない。

両 endpoint 自体が `0` へ行くのであれば、その和と差が `0` へ行くことは topology の一般則から従う。

したがって、この差の零極限だけでは、新たな fixed-point rigidity は生じていない。

---

## 14. exact zero と zero limit の firewall

本書で最重要の監査点である。

次は証明済みである。

$$
\operatorname{etaPartialEndpoint}(N,s)\longrightarrow0
$$

しかし、ここから

$$
\exists N,\quad \operatorname{etaPartialEndpoint}(N,s)=0
$$

は導けない。

さらに、

$$
\operatorname{etaPartialEndpoint}(N,\operatorname{criticalMirror}(s))
-
\operatorname{etaPartialEndpoint}(N,s)
\longrightarrow0
$$

から

$$
\operatorname{criticalMirror}(s)=s
$$

も導けない。

二つの異なる parameter point に属する sequence が、同じ零極限を持つことは一般に可能である。

したがって本書で得られたものは **asymptotic co-vanishing** であり、RH に必要な **same-object collision / fixedness** ではない。

この firewall は後の paired-frame、energy、moving-line 議論でも維持する。

---

## 15. `s.im ≠ 0` 条件

本書の主 theorem は `s.im ≠ 0` を仮定する。

これは arbitrary な技術仮定ではなく、`EtaPairedContinuation.lean` が upper-right / lower-right の二つの非実 continuation domain 上で identity theorem を使っていることに由来する。

したがって、この段階では

```text
nontrivial zero
+
nonreal condition
```

から endpoint vanishing を得る。

後続の `StandardZetaRealAxisClosure.lean` には、非自明ゼータ零点が実軸上に存在しないことを閉じる theorem が実装されているが、そのモジュールは moving-line 系へ依存する後段の構造を import している。

本書では依存順を逆転させないため、その後段 theorem を前提として用いない。

よって `s.im ≠ 0` は本書の局所的な theorem contract としてそのまま記録する。

---

## 16. Core / Beam / Gap 監査

### Core

次は現行 Lean 実装で証明済みである。

1. finite eta endpoint は genuine alternating finite sum である。
2. even finite endpoint は paired finite difference sum と exact に一致する。
3. paired eta difference series は `Re(s) > 0` で summable である。
4. paired eta value は `Re(s) > 0` で holomorphic である。
5. `Re(s) > 1` の anchor region で paired eta と analytic eta が一致する。
6. upper-right / lower-right domain の identity theorem により、非実 `Re(s) > 0` 全体へ一致が延長される。
7. 非実右半平面の standard zeta zero では finite eta endpoint が `0` へ収束する。
8. 非実 nontrivial zero `s` と `criticalMirror s` の両方で endpoint が `0` へ収束する。
9. original/mirror endpoint の和と差も `0` へ収束する。

### Beam

本書で形成された Beam は次である。

```text
standard nontrivial zeta zero pair
  ↓
analytic eta zero pair
  ↓
genuine finite eta endpoint sequences
  ↓
two-sided zero limit
```

これは standard zeta の零点集合を、有限 eta observables の共通 truncation dynamics へ移送する representation / analytic bridge である。

### Gap

本書では次を証明していない。

1. finite `N` における exact endpoint closure。
2. original と mirror の finite endpoint equality。
3. zero-limit difference から parameter equality を導く rigidity。
4. `criticalMirror s = s`。
5. `Re(s) = 1/2`。

したがって RH の load-bearing Gap はまだ残る。

---

## 17. 状態表

| 項目 | 状態 | 分類 |
|---|---|---|
| genuine finite eta endpoint の定義 | 証明・定義済み | Core |
| even endpoint と paired finite sum の exact identity | 証明済み | Core |
| paired eta の `Re(s) > 0` summability | 証明済み | Core |
| paired eta の `Re(s) > 0` holomorphicity | 証明済み | Core |
| paired eta と analytic eta の非実右半平面での一致 | 証明済み | Core |
| nonreal zeta zero → eta endpoint zero limit | 証明済み | Core |
| mirror zero → mirror eta endpoint zero limit | 証明済み | Core |
| original/mirror endpoint の共通 truncation | 定義上成立 | Core |
| endpoint difference → `0` | 証明済み | Core |
| ある有限 truncation で endpoint が exact zero | 未導出 | Gap |
| endpoint co-vanishing → mirror fixedness | 導出不可 | Obstruction / Gap |
| mirror fixedness → `Re(s)=1/2` | 幾何 theorem は既存、前件が未導出 | Gap |

---

## 18. 本書の位置付け

`0009` まででは、standard zeta zero set が same-height critical mirror に対して閉じていることを得た。

本書では、その mirror pair を genuine finite eta endpoint sequence に持ち込み、両側が同じ truncation parameter の下で `0` へ収束することを得た。

したがって依存図は次まで進んだ。

```text
NontrivialRiemannZetaZero s
  ↓
NontrivialRiemannZetaZero (criticalMirror s)
  ↓
eta endpoint at s → 0
eta endpoint at criticalMirror s → 0
  ↓
mirror/original endpoint displacement → 0
```

ここはまだ collision ではない。

しかし、標準ゼータの零点対を finite observable の共通 index 系へ移送したことにより、後続の energy decomposition、normalization、weighted transport、paired-frame 構造を同じ対象上で構築する入口が得られた。

次に依存順で現れる主要層は `EtaCriticalMirrorEnergyCollapse` および endpoint energy / outer normalization である。
