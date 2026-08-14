# IPSM-001 — Prime-side sign mechanism audit

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: research audit / no RH claim

---

## 0. 目的

XDP-017〜021 により、boundary-safe residue window `W` に対する fixed Xi second-moment defect は、有限 Pascal / von Mangoldt arithmetic defect approximant の ordered endpoint として表現された。

現在の形式的 frontier は、既存 zero-side theorem が与える

$$
0 \le D_\Xi(W.R)
$$

に対し、RH-equivalent assumption を使わず prime-side arithmetic surface から反対向き

$$
D_\Xi(W.R) \le 0
$$

を得られるかどうかである。

XDP-021 自身は sign theorem を含まない。本 audit は sign を仮定した provider を導入せず、有限 arithmetic surface の各成分を分解し、どこに definite sign が存在し得るか、どこが obstruction になるかを判定する。

---

## 1. 正本 surface

XDP-021 の finite arithmetic defect approximant は概念的に

$$
D_{\varepsilon,X}(W)
:= Q(W.R)-\operatorname{Re} A_{\varepsilon,X}(W)
$$

である。

ここで `Q(W.R)` は fixed radial second moment、`A_{ε,X}(W)` は `(2πi)⁻¹` で正規化された XDP-020 arithmetic approximant である。

ordered endpoint は

$$
\lim_{\varepsilon\to0^+}
\left(
\lim_{X\to\infty}D_{\varepsilon,X}(W)
\right)
= D_\Xi(W.R)
$$

であり、`X ↔ ε` exchange、joint limit、uniform-in-ε cutoff theorem は主張しない。

---

## 2. finite explicit formula の四成分

`PascalCenteredXiMellinQuadraticArithmeticLimit` により、fixed `ε > 0`, `τ = 0` では finite arithmetic surface は exact に

```text
von Mangoldt right-edge term
+ archimedean correction
+ elementary correction
+ top-horizontal correction
```

へ分解される。

重要なのは、有限高さでは top-horizontal correction を捨てていないことである。

従って sign mechanism を探す際、prime term 単体の符号を full arithmetic endpoint の符号と同一視してはならない。

---

## 3. normalization audit

prime right-edge integrand には末尾に `Complex.I` がある。

一方、XDP-021 normalization は

$$
(2\pi i)^{-1}
= -\frac{i}{2\pi}
$$

である。

したがって prime contribution に限れば、外側の `I` は normalization と exact に相殺する。

概念的に、normalized prime contribution の実部は

$$
\frac{1}{\pi}
\sum_{n\le X}\Lambda(n)n^{-\sigma}
\int_{-T}^{T}
\operatorname{Re}
\left(
q_\varepsilon(a+it)e^{-it\log n}
\right)dt
$$

へ落ちる。

ここで

$$
a:=\sigma-\frac12>0
$$

かつ `q_ε` は `τ = 0` の centered quadratic Mellin weight である。

この exact real-kernel rewrite は Lean module にはまだ named theorem として存在しない。次実装候補である。

---

## 4. `τ = 0` Mellin quadratic weight

既存 theorem により

$$
q_\varepsilon(z)
:=z^2H_\varepsilon(z)
$$

である。

ここで `H_ε` は `centeredMellinBoxApprox ε` の centered Mellin spectral weight。

既存 Mellin API は

$$
H_\varepsilon(z)
=
\frac{1}{2\varepsilon}
\int_{-\varepsilon}^{\varepsilon}e^{tz}\,dt
$$

を exact に与える。

従って通常の複素解析計算では、`z ≠ 0` で

$$
H_\varepsilon(z)
=
\frac{\sinh(\varepsilon z)}{\varepsilon z}
$$

となり、patched value を含む entire continuation として

$$
q_\varepsilon(z)
=
\frac{z\sinh(\varepsilon z)}{\varepsilon}
$$

と読める。

この `sinh` closed form は現時点で Lean Core ではない。本 audit では解析上の候補式として用い、実装時には既存 interval-integral identity から別 theorem として証明する。

---

## 5. 一つの von Mangoldt mode の周波数 audit

`L := log n` とし、右辺 centered coordinate を `a + it` とする。

上の closed form を用いると

$$
q_\varepsilon(a+it)e^{-iLt}
=
\frac{1}{2\varepsilon}
\left[
 e^{\varepsilon a}(a+it)e^{-i(L-\varepsilon)t}
 -e^{-\varepsilon a}(a+it)e^{-i(L+\varepsilon)t}
\right].
$$

そこで

$$
F_{a,T}(c)
:=
\int_{-T}^{T}
\operatorname{Re}\left((a+it)e^{-ict}\right)dt
$$

と置く。

`c ≠ 0` なら elementary integration により

$$
F_{a,T}(c)
=
\frac{2a\sin(cT)}{c}
+
\frac{2\left(\sin(cT)-cT\cos(cT)\right)}{c^2}.
$$

`c = 0` では連続延長値は

$$
F_{a,T}(0)=2aT.
$$

従って一つの log-frequency `L` に対する real kernel は

$$
K_{\varepsilon,a,T}(L)
:=
\frac{
 e^{\varepsilon a}F_{a,T}(L-\varepsilon)
 -e^{-\varepsilon a}F_{a,T}(L+\varepsilon)
}{2\varepsilon}.
$$

この式は `sin((L±ε)T)` と `cos((L±ε)T)` を保持する。

よって continuous frequency `L` の段階では、kernel は単調な正 kernel / 負 kernel ではなく振動 kernel である。

### 判定 Q1

```text
finite von Mangoldt contribution の各 n 項を
Λ(n) ≥ 0 だけから同一符号へ押し込む経路
```

は主 Beam としない。

ただしこれは、実際の離散集合 `L = log n` 上で正負両方が必ず出ることを Lean で証明した、という意味ではない。

本 audit が固定するのは次だけである。

```text
continuous log-frequency kernel に振動が残るため、
termwise definite sign を自明な coefficient-sign argument として
利用してはならない。
```

必要なら後続 module で、この continuous-frequency obstruction を named theorem 化する。

---

## 6. correction terms の扱い

有限 explicit formula は prime term のほかに

```text
archimedean correction
elementary correction
top-horizontal correction
```

を同じ weight で保持する。

従って Q2 / Q3 の監査方針は、各 correction を個別にゼロへ送ることではなく、まず normalized real part の exact decomposition を作ることである。

狙う形は

$$
\operatorname{Re}A_{\varepsilon,X}
=
P_{\varepsilon,X}
+A_\varepsilon
+E_\varepsilon
+H_\varepsilon^{\mathrm{top}}.
$$

その上で

```text
P 単独 sign
correction 単独 sign
pairwise compensation
whole-surface square / energy identity
```

の順に監査する。

現時点では correction の definite sign を主張しない。

---

## 7. CF2D radial mass との本当の inequality target

XDP-021 の CF2D surface により radial side は既に同じ theorem surface へ rewrite できる。

従って独立 sign mechanism が最終的に必要とする有限 inequality は

$$
Q_{\mathrm{CF2D}}(W.R)
\le
\operatorname{Re}A_{\varepsilon,X}(W)
$$

または、その eventual / endpoint 版である。

これが得られれば

$$
D_{\varepsilon,X}(W)\le0
$$

となる。

ここで `Q_CF2D` は square-mass observable なので、候補となる機構は単項 Fourier sign より

```text
whole arithmetic surface の square / energy completion
critical-mirror pair cancellation
CF2D q2 保存との exact comparison
```

である。

---

## 8. ordered-limit sign transport

sign mechanism 本体と、sign を endpoint へ輸送する位相は分離する。

必要な一般形は次である。

### fixed ε

もし fixed `ε > 0` に対し、ある `X₀` 以降

$$
D_{\varepsilon,X}(W)\le0
$$

かつ

$$
D_{\varepsilon,X}(W)
\longrightarrow
D_\varepsilon(W)
$$

なら、closed order set による極限保存から

$$
D_\varepsilon(W)\le0
$$

を得られる。

### ε → 0+

さらに、ある punctured right-neighborhood で

$$
D_\varepsilon(W)\le0
$$

かつ

$$
D_\varepsilon(W)
\longrightarrow
D_\Xi(W.R)
$$

なら

$$
D_\Xi(W.R)\le0
$$

を得られる。

これは `X ↔ ε` exchange を必要としない。

従って Q5 / Q6 に対する first answer は

```text
joint limit は不要。
ordered limit の各段で eventual nonpositivity を保存すれば足りる。
```

である。

ただし、この transport theorem は sign mechanism そのものではない。eventual sign を仮定する conditional adapter に留める。

---

## 9. IPSM-001 判定

現時点の Beam / Obstruction を次のように固定する。

### Obstruction A — naive termwise von Mangoldt sign

```text
Λ(n) ≥ 0
+ quadratic Mellin weight
⇒ each prime-power mode has one fixed sign
```

という単純経路は採用しない。

continuous log-frequency kernel に oscillatory `sin / cos` structure が残るためである。

### Beam A — exact normalized real decomposition

prime / archimedean / elementary / top を normalized real observablesとして named 化する。

### Beam B — whole-surface sign / energy audit

四項全体と CF2D radial `q2` の間に exact square / pair identity が存在するか調べる。

### Beam C — ordered sign transport

fixed `ε` の `X → ∞` と、endpoint の `ε → 0+` を別々に使い、eventual sign を final defect へ運ぶ conditional theorem を用意する。

---

## 10. 次 Lean module 候補

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
```

最初の実装 scope は、RH に触れない pure representation / order transport に限定する。

候補 theorem surface:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution
pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution
pascalCenteredXiMellinQuadraticNormalizedElementaryContribution
pascalCenteredXiMellinQuadraticNormalizedTopContribution

pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms

pascalCenteredXiArithmeticDefectEndpoint_nonpos_of_eventually_approximant_nonpos
pascalCenteredXiFixedDefect_nonpos_of_eventually_endpoint_nonpos
```

次の段階で、必要なら Mellin kernel の real closed form を独立 module へ切る。

```text
DkMath.Analysis.MellinQuadraticRealKernel
```

ここでは `Complex.arg` を導入しない。

---

## 11. 非目標

IPSM-001 では以下を主張しない。

```text
finite arithmetic defect の nonpositivity
prime term の discrete n 上での sign-change theorem
correction term の definite sign
uniform-in-ε prime cutoff convergence
X ↔ ε exchange
joint limit
T → ∞
top-horizontal disappearance
fixed defect vanishing
Riemann Hypothesis
```

---

## 12. 次 checkpoint

次の実装判断は明確である。

```text
XDP representation block
  COMPLETE

IPSM sign block
  Gate 1:
    normalized real four-term decomposition

  Gate 2:
    ordered-limit sign transport adapter

  Gate 3:
    whole-surface square / energy audit

  Gate 4:
    independent inequality or named obstruction
```

最初から `fixed defect ≤ 0` を provider として仮定しない。

sign が閉じなければ、その不足を named obstruction として固定する。
