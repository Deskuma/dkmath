# CFZP-0064 / CFZP-036

## prime-axis sigma-stripped periodic carrier and vanishing finite remainder — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-033: prime-power logarithmic coordinate `u = j * log p` と exact sigma-decay
- CFZP-034: prime-axis `j = 1` reservoir と sigma weight `exp(-σ log p)`
- CFZP-035: actual branch-free event / reference-mass exact signed efficiency

CFZP-035 は Green-A。safe prime-power pair で

```text
actual event = reference mass * exact signed efficiency
|signed efficiency| <= 1
```

を閉じ、prime axis では

```text
actual event(p,1)
  = exp(-σ log p) * cfzp035PrimeAxisSignedAmplitude ε W p
```

を exact に得た。

次に prime distribution へ進む前に、`cfzp035PrimeAxisSignedAmplitude` 自体を解析する。
既存 CFZP-006W の profile 定義を展開すると、`u = log p` に対して sigma weight を剥がした amplitude は

```text
periodic trigonometric carrier + finite rational remainder
```

へ exact に分解でき、remainder は large `u` で `K/u` に抑えられる。

さらに leading periodic carrier は

```text
S * sin(T*u) + C * cos(T*u)
```

という一個の非自明な周期波になる。

**CFZP-036 の目的は、prime-axis 問題を「素数分布」と「解析波形」に完全分離すること。**

本段では prime distribution、Bertrand、PNT、Mertens、Dirichlet、density、infinite sum、limit exchange、residual elimination、CFZP-018 provider、RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisSigmaStrippedPeriodicCarrierAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeAxisSigmaStrippedPeriodicCarrierAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaExactSignedEfficiencyNormalizationAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に公開 import を追加。

---

## 2. Gate A — coordinate-level sigma-stripped amplitude

`p` を消した real coordinate `u` 上の amplitude を first-class にする。

既存記号:

```text
a := cfzpModePhaseAbscissa W = W.rectangle.σ - 1/2
T := W.rectangle.T
```

候補定義:

```lean
noncomputable def cfzp036PrimeAxisCoordinateAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (u / ε) *
    (Real.exp ((cfzpModePhaseAbscissa W) * ε) /
        (u - ε) ^ 2 *
        cfzpNegativeFrequencyBoundaryCore
          (cfzpModePhaseAbscissa W) (u - ε) W.rectangle.T -
     Real.exp (-(cfzpModePhaseAbscissa W) * ε) /
        (u + ε) ^ 2 *
        cfzpNegativeFrequencyBoundaryCore
          (cfzpModePhaseAbscissa W) (u + ε) W.rectangle.T)
```

multiplication order は Lean が扱いやすい形へ調整してよい。

prime specialization を証明する。

目標:

```text
cfzp035PrimeAxisSignedAmplitude ε W p
  = cfzp036PrimeAxisCoordinateAmplitude ε W (log p)
```

under safe prime assumptions。

proof spine:

1. CFZP-035 `event = sigmaWeight * signedAmplitude`。
2. CFZP-006W
   `event = positiveScale * (Profile(left)-Profile(right))`。
3. `criticalScale p = exp(-(1/2) log p)`。
4. `Profile(v)=exp(-a v)/v^2 * Core(v)`。
5. `a = σ-1/2` を使い

```text
exp(σu) * exp(-u/2) * exp(-a(u-ε)) = exp(aε)
exp(σu) * exp(-u/2) * exp(-a(u+ε)) = exp(-aε)
```

へ exact recombination。
6. `2*u*(2*ε)⁻¹ = u/ε`。

既存 theorem が使える箇所は再証明しない。

---

## 3. Gate B — boundary core の linear-phase decomposition

新しい簡単な phase function を導入する。

```lean
noncomputable def cfzp036LinearPhaseCore
    (a T θ : ℝ) : ℝ :=
  a * Real.sin θ - T * Real.cos θ
```

exact identity:

```text
cfzpNegativeFrequencyBoundaryCore a v T
  = v * cfzp036LinearPhaseCore a T (v*T)
      + sin(v*T)
```

を証明する。

これは

```text
(a*v+1) sin(vT) - vT cos(vT)
```

の単純分解である。

absolute bound も用意する。

`0 <= a`, `0 <= T` の下で例えば

```text
|cfzp036LinearPhaseCore a T θ| <= a + T
```

を証明する。

---

## 4. Gate C — exact leading carrier + remainder decomposition

略記:

```text
Eplus  = exp(a ε)
Eminus = exp(-a ε)
l = u - ε
r = u + ε
phaseL = LinearPhaseCore a T (T*l)
phaseR = LinearPhaseCore a T (T*r)
```

leading periodic carrier を

```lean
noncomputable def cfzp036PrimeAxisLeadingPeriodicCarrier
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (Real.exp (a*ε) * phaseL -
   Real.exp (-a*ε) * phaseR) / ε
```

相当で定義する。

remainder は、次の簡約形が使いやすい。

```text
R(u)
 = Eplus / l * phaseL
 + Eminus / r * phaseR
 + (u/ε) *
     (Eplus / l^2 * sin(T*l)
      - Eminus / r^2 * sin(T*r))
```

候補:

```lean
noncomputable def cfzp036PrimeAxisAmplitudeRemainder ... := ...
```

そして exact theorem:

```text
cfzp036PrimeAxisCoordinateAmplitude ε W u
  = cfzp036PrimeAxisLeadingPeriodicCarrier ε W u
      + cfzp036PrimeAxisAmplitudeRemainder ε W u
```

を証明する。

この Gate は algebraic exact identity。large-`u` assumptions は不要。
分母 nonzero が必要なら theorem 側だけに `u-ε ≠ 0`, `u+ε ≠ 0`, `ε ≠ 0` を付ける。

---

## 5. Gate D — remainder の finite `K/u` envelope

prime-independent constant を一個定義する。

候補:

```text
K(ε,W)
 = (2*Eplus + Eminus) * (a + T)
   + (4*Eplus + Eminus) / ε
```

`a > 0`, `T > 0`, `ε > 0` なので positive。

under:

```text
0 < ε
1 <= u
2*ε <= u
```

から

```text
u/2 <= u-ε
u <= u+ε
1/(u-ε) <= 2/u
1/(u+ε) <= 1/u
u/(u-ε)^2 <= 4/u
u/(u+ε)^2 <= 1/u
```

相当を使い、

```text
|cfzp036PrimeAxisAmplitudeRemainder ε W u|
  <= cfzp036PrimeAxisRemainderConstant ε W / u
```

を finite theorem として閉じる。

定数は sharp でなくてよい。Lean proof を簡単にするため 2,4 を 4,8,16 等へ粗くしてよい。
重要なのは:

- constant が `u`, `p` に依存しない
- `K/u` 型
- infinite limit theorem を使わない

ことである。

必要なら補助 theorem:

```text
0 <= K
0 < K
```

を置く。

---

## 6. Gate E — periodic carrier を one sinusoid/cosine pair へ展開

`δ := T*ε`、`x := T*u`。

まず指数和差:

```text
D := exp(aε) - exp(-aε)
M := exp(aε) + exp(-aε)
```

を局所 def または named def にしてよい。

unnormalized coefficients の推奨形:

```text
S0
 = a * cos(δ) * D
   - T * sin(δ) * M

C0
 = -a * sin(δ) * M
   - T * cos(δ) * D
```

そして exact theorem:

```text
cfzp036PrimeAxisLeadingPeriodicCarrier ε W u
  = (S0 * sin(T*u) + C0 * cos(T*u)) / ε
```

を `sin_sub`, `sin_add`, `cos_sub`, `cos_add` で閉じる。

命名候補:

```text
cfzp036LeadingSinCoeffNumerator
cfzp036LeadingCosCoeffNumerator
```

---

## 7. Gate F — leading carrier が恒等ゼロではないことを内部証明

ここは重要な completion gate。

係数平方和の exact identity を狙う。

```text
S0^2 + C0^2
 = (a^2 + T^2) *
   (cos(δ)^2 * D^2 + sin(δ)^2 * M^2)
```

cross term は exact に cancel する。

さらに

```text
0 < a
0 < T
0 < ε
0 < D
0 < M
D <= M
```

を使い、右辺が strictly positive であることを証明する。

`D > 0` は

```text
-aε < aε
exp(-aε) < exp(aε)
```

から得る。

第二因子の positivity は、例えば `M >= D > 0` と

```text
sin^2 δ + cos^2 δ = 1
```

を用いて

```text
D^2 <= cos^2 δ * D^2 + sin^2 δ * M^2
```

相当へ落としてよい。

completion target:

```text
0 < S0^2 + C0^2
```

および

```text
S0 ≠ 0 ∨ C0 ≠ 0
```

相当の theorem。

**leading periodic carrier が zero function ではないことを外部 hypothesis にしてはいけない。**

---

## 8. Gate G — explicit period

coordinate period を

```lean
noncomputable def cfzp036PrimeAxisCarrierPeriod
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  2 * Real.pi / W.rectangle.T
```

と置く。

証明:

```text
0 < CarrierPeriod
LeadingCarrier(u + CarrierPeriod) = LeadingCarrier(u)
```

`T > 0` と trig periodicity を使う。

この theorem により prime-axis arithmetic question は

```text
u = log p modulo (2π/T)
```

へ明示的に還元される。

---

## 9. Gate H — carrier margin dominates exact amplitude once `u` is large

limit を使わず finite implication を置く。

例えば `κ > 0` に対して:

```text
κ <= LeadingCarrier(u)
K/u <= κ/2
```

なら

```text
κ/2 <= CoordinateAmplitude(u)
```

を証明する。

同様に negative side:

```text
LeadingCarrier(u) <= -κ
K/u <= κ/2
```

なら

```text
CoordinateAmplitude(u) <= -κ/2
```

を証明してよい。

これは exact decomposition + `|R| <= K/u` だけで閉じる。

prime specialization も短ければ用意する。

```text
u = log p
```

かつ eligibility/large-log 条件の下で leading carrier margin が actual prime-axis event sign へ transport する theorem。

ただし prime がその phase margin cell に存在する theorem は作らない。

---

## 10. Optional Gate I — leading carrier の positive / negative phase witness

実装が短ければ、係数 nonzero から一周期中に正値・負値を取ることを有限 theorem で示す。

atan2 は不要。

- `S0 > 0` なら `θ = π/2` で positive、`3π/2` で negative
- `S0 < 0` なら逆
- `S0 = 0` なら `C0 ≠ 0` なので `θ = 0, π` を使う

という case split でよい。

coordinate `u` へ戻す必要はなく、phase variable `θ` 上の theorem でもよい。

次段 CFZP-037 で continuity を使った robust positive/negative open arc に強化できる。

---

## 11. Firewall

次を本段では導入しない。

```text
prime p with log p in a positive carrier arc
prime-log equidistribution
Bertrand / PNT / Mertens / Dirichlet
positive weighted density
infinite sum
summability / divergence
limit exchange
exceptional/higher-power residual elimination
CFZP-018 provider
global RH
```

Gap 例:

```lean
inductive Cfzp036PrimeAxisSigmaStrippedPeriodicCarrierGap : Prop
  | noPrimeLogCarrierArcHitProvider
  | noPrimeAxisWeightedSignedCarrierDominanceProvider
  | noExceptionalHigherPowerResidualElimination
  | noAutomaticSubcriticalWindowProvider
```

---

## 12. Roadmap update

CFZP-036 section を追記し、少なくとも以下を明示する。

```text
coordinate sigma-stripped amplitude: CLOSED
prime specialization to CFZP-035 amplitude: CLOSED
boundary core linear-phase decomposition: CLOSED
exact leading periodic carrier + remainder: CLOSED
finite K/u remainder envelope: CLOSED
single sin/cos coefficient normal form: CLOSED
leading coefficient nontriviality: CLOSED internally
explicit period 2π/T: CLOSED
finite carrier-margin -> actual-amplitude sign transport: CLOSED
prime-log carrier-arc hit provider: OPEN / GAP
weighted signed carrier dominance: OPEN / GAP
infinite sums / prime distribution / global RH: OUT OF SCOPE
```

---

## completion condition

CFZP-036 を Green とする最低条件:

1. `cfzp035PrimeAxisSignedAmplitude` が `u=log p` の coordinate amplitude に exact 接続。
2. coordinate amplitude = leading periodic carrier + remainder を exact 証明。
3. remainder に p-independent finite `K/u` envelope。
4. leading carrier を `S sin(Tu)+C cos(Tu)` へ exact 展開。
5. `(S,C)` が同時に zero ではないことを **内部証明**。
6. carrier period `2π/T` を exact 証明。
7. finite carrier margin が exact amplitude の符号へ transport する theorem。
8. prime distribution / infinite sum / RH を導入しない。

この段が閉じれば次の arithmetic frontier は非常に明確になる。

```text
Find / control primes p such that
  log p mod (2π/T)
lies in a robust positive carrier arc,
with the sigma weight exp(-σ log p).
```

その前に CFZP-037 では、035/036 の actual carrier に対して robust positive/negative phase arcs と finite margin windows を作るのが自然である。
