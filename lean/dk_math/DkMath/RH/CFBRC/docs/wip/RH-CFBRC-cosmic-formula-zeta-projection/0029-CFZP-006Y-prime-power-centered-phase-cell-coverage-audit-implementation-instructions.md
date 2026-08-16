# CFZP-0029 — CFZP-006Y prime-power centered phase-cell coverage audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前の Green checkpoint:

```text
d23de1452cf92676e524958c82d38b37d8de8c95
Add: CFZP-0028: CFZP-006X negative-frequency boundary profile derivative / local monotonicity audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
```

006X では exact に

```text
F'(u)
  = exp(-a*u) / u^3 * D(a,T,u)
```

が公開され、`u > 0` では derivative と derivative core `D` の sign / zero が完全に同値になった。

さらに centered prime-power interval

```text
uL = j*log p - ε
uR = j*log p + ε
```

に対して

```text
D(a,T,u) ≤ 0 on Ioo uL uR
  → F antitone on Icc uL uR
  → 0 ≤ prime-power event
```

および dual な nonpositive event adapter まで閉じた。

006X の残 frontier は

```lean
CfzpPrimePowerCenteredDerivativeCellCoverageGap
  | noIndependentPrimePowerCenteredIntervalDerivativeSignCellProvider
```

である。

今回 CFZP-006Y では、この `u`-interval 問題を phase angle

```text
θ = u*T
```

へ無次元化し、prime-power arithmetic center を

```text
Θ = j*T*log p
η = ε*T
```

とする centered angular interval

```text
[Θ-η, Θ+η]
```

として first-class 化する。

目的は universal sign を出すことではない。

目的は

```text
prime-power centered interval
  ↓
dimensionless angular interval
  ↓
explicit phase sign-cell coverage certificate
  ↓
derivative-core sign on the whole centered interval
  ↓
conditional one-event sign
```

という exact finite bridge を構築することである。

重要:

- equidistribution は扱わない。
- density / asymptotic distribution は扱わない。
- infinite prime argument は扱わない。
- 新しい `X → ∞` argument は扱わない。
- all prime powers に共通する event sign は主張しない。
- cumulative ledger monotonicityは主張しない。
- baseline reach existence は主張しない。
- zeta-zero / RH は主張しない。

---

# 1. 監査済み006X API

006X の derivative core は

```lean
cfzpNegativeFrequencyBoundaryProfileDerivativeSinCoeff
cfzpNegativeFrequencyBoundaryProfileDerivativeCore
```

である。

数学的には

```text
A(a,T,u)
  := u^2 * (T^2 - a^2) - 2*(a*u + 1)

D(a,T,u)
  := A(a,T,u) * sin(u*T)
     + 2*T*u*(a*u + 1) * cos(u*T)
```

である。

既存 exact theorem:

```lean
cfzpNegativeFrequencyBoundaryProfile_deriv
cfzpNegativeFrequencyBoundaryProfile_deriv_*_iff_derivativeCore_*
```

を再利用する。

局所 monotonicity:

```lean
cfzpNegativeFrequencyBoundaryProfile_antitoneOn_Icc_of_derivativeCore_nonpos
cfzpNegativeFrequencyBoundaryProfile_monotoneOn_Icc_of_derivativeCore_nonneg
```

prime-power event adapter:

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_derivativeCore_nonpos_on_centeredInterval
cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_derivativeCore_nonneg_on_centeredInterval
```

006Y ではこれらを置き換えない。

angular cell coverage から006X hypothesis を供給する薄い上位 layer を作る。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
import Mathlib.Tactic
```

必要なら real trigonometric interval API 用に最小限の Mathlib import を追加してよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — derivative core の dimensionless phase normalization

`T > 0` の下では

```text
α := a / T
θ := u * T
```

と置ける。

すると exact に

```text
a*u = α*θ
u^2*(T^2-a^2) = θ^2*(1-α^2)
```

である。

そこで dimensionless sin coefficient を first-class 定義する。

推奨:

```lean
noncomputable def cfzpPhaseDerivativeSinCoeff
    (α θ : ℝ) : ℝ :=
  θ ^ 2 * (1 - α ^ 2) - 2 * (α * θ + 1)
```

そして phase derivative core:

```lean
noncomputable def cfzpPhaseDerivativeCore
    (α θ : ℝ) : ℝ :=
  cfzpPhaseDerivativeSinCoeff α θ * Real.sin θ +
    2 * θ * (α * θ + 1) * Real.cos θ
```

を定義する。

中心 theorem:

```lean
cfzpNegativeFrequencyBoundaryProfileDerivativeCore_eq_phaseDerivativeCore
```

目標:

```text
T ≠ 0
  → D(a,T,u)
      = H(a/T, u*T)
```

ここで `H := cfzpPhaseDerivativeCore`。

proof は unfold + field_simp + ring で閉じることを優先する。

この bridge により derivative sign 問題は length scale から独立した

```text
H(α,θ)
```

の符号問題になる。

---

# 4. Gate B — rectangle phase aspect ratio

CFZP-facing helper として必要なら

```lean
noncomputable def cfzpModePhaseAspectRatio
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpModePhaseAbscissa W / W.rectangle.T
```

を定義する。

既存 rectangle contract には

```text
W.rectangle.hσ : 1 < W.rectangle.σ
W.rectangle.hT : 0 < W.rectangle.T
```

があるため、少なくとも

```text
0 < cfzpModePhaseAbscissa W
0 < W.rectangle.T
0 < cfzpModePhaseAspectRatio W
```

を exact に出せるなら公開してよい。

ただし positivity helper の theorem-name 探索で実装が重くなる場合、006Y の核心ではないので局所 `have` で済ませてもよい。

---

# 5. Gate C — prime-power centered angular coordinates

006W の

```text
L = j*log p
uL = L-ε
uR = L+ε
```

を angle へ運ぶ。

推奨 definitions:

```lean
noncomputable def cfzpPrimePowerPhaseAngleCenter
    (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  W.rectangle.T * cfzpPrimePowerPhaseCenter p j

noncomputable def cfzpPrimePowerPhaseAngleHalfWidth
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  W.rectangle.T * ε

noncomputable def cfzpPrimePowerPhaseAngleLeft
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseAngleCenter W p j -
    cfzpPrimePowerPhaseAngleHalfWidth ε W

noncomputable def cfzpPrimePowerPhaseAngleRight
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseAngleCenter W p j +
    cfzpPrimePowerPhaseAngleHalfWidth ε W
```

名前は調整可。

exact bridge:

```text
T*uL = θL
T*uR = θR
```

または multiplication orientation を implementation に合わせて統一する。

safe hypotheses

```text
hε : 0 < ε
hε2 : ε < Real.log 2
hp : Nat.Prime p
hj : 0 < j
```

と `W.rectangle.hT` の下で

```text
0 < θL < θR
0 < η
θL = Θ-η
θR = Θ+η
```

を公開する。

prime-power arithmetic center が

```text
Θ = j*T*log p
```

であることも exact theorem として公開してよい。

---

# 6. Gate D — angular phase-core sign と original derivative-core sign の interval bridge

006Y の中心 theorem 1。

`u ∈ Ioo uL uR` とする。

`T > 0` なので

```text
θ := T*u
```

は

```text
θ ∈ Ioo θL θR
```

へ移る。

Gate A の exact bridge を使い、次の adapter を作る。

### nonpositive coverage

仮定:

```text
∀ θ ∈ Ioo θL θR,
  cfzpPhaseDerivativeCore α θ ≤ 0
```

結論:

```text
∀ u ∈ Ioo uL uR,
  cfzpNegativeFrequencyBoundaryProfileDerivativeCore a T u ≤ 0
```

### nonnegative coverage

dual に

```text
∀ θ ∈ Ioo θL θR,
  0 ≤ cfzpPhaseDerivativeCore α θ
```

から original derivative-core nonnegative を得る。

推奨 theorem family:

```lean
cfzpPrimePowerDerivativeCore_nonpos_on_centeredInterval_of_phaseCore_nonpos
cfzpPrimePowerDerivativeCore_nonneg_on_centeredInterval_of_phaseCore_nonneg
```

これらは finite variable substitution adapter であり sign provider ではない。

---

# 7. Gate E — first-class phase sign-cell predicates

phase core

```text
H(α,θ)
  = Aθ(α,θ)*sin θ
    + 2*θ*(α*θ+1)*cos θ
```

について、`α ≥ 0`, `θ > 0` では

```text
2*θ*(α*θ+1) > 0
```

である。

006X の sign cells を dimensionless phase form へ移す。

少なくとも以下を first-class predicate または theorem として用意する。

### Nonpositive cell NP1

```text
0 ≤ Aθ
sin θ ≤ 0
cos θ ≤ 0
```

なら

```text
H(α,θ) ≤ 0
```

### Nonnegative cell NN1

```text
Aθ ≤ 0
sin θ ≤ 0
0 ≤ cos θ
```

なら

```text
0 ≤ H(α,θ)
```

必要なら dual cells を追加してよい。

推奨 theorem:

```lean
cfzpPhaseDerivativeCore_nonpos_of_sinCoeff_nonneg_sin_nonpos_cos_nonpos
cfzpPhaseDerivativeCore_nonneg_of_sinCoeff_nonpos_sin_nonpos_cos_nonneg
```

さらに coverage を first-class にするなら

```lean
noncomputable def / def
  cfzpPhaseDerivativeNonposCellCovered ... : Prop :=
    ∀ θ ∈ Set.Ioo θL θR, <cell conditions>
```

のような predicate を設けてもよい。

重要なのは、angular interval の全点で cell condition が成立することを hypothesis として明示すること。

---

# 8. Gate F — phase-cell coverage から one-event sign へ exact adapter

006Y の中心 theorem 2。

safe-frequency hypotheses と witnessed prime power の下で、angular centered interval 全域が nonpositive phase-core cell に入るなら

```text
0 ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j
```

を証明する。

proof route:

```text
1. angular coverage
2. Gate D で original derivative-core ≤ 0 on Ioo uL uR
3. 006X event nonnegative adapter
```

推奨 theorem:

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_phaseDerivativeCore_nonpos_on_centeredAngle
```

さらに cell predicate を導入した場合は

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonneg_of_nonposPhaseCellCoverage
```

のような薄い theorem もよい。

dual:

```text
phase core ≥ 0 on centered angular interval
  → Event ≤ 0
```

推奨:

```lean
cfzpPrimePowerBranchFreeTrigEvent_nonpos_of_phaseDerivativeCore_nonneg_on_centeredAngle
```

ここでも universal event sign は禁止。

---

# 9. Gate G — finite witnessed cell-membership certificate

今回の「coverage audit」の目的は、各 witnessed prime power に対して

```text
center angle Θ
half width η
interval [Θ-η, Θ+η]
```

を explicit に持たせることである。

最低限、以下の certificate theorem を用意する。

```text
θ ∈ [Θ-η, Θ+η]
  ↔ θ ∈ [T*(L-ε), T*(L+ε)]
```

または定義展開で同等の exact statement。

さらに implementation が自然なら、任意の explicit cell interval `[cL,cR]` に対して

```text
θL ≥ cL
θR ≤ cR
```

なら

```text
Icc θL θR ⊆ Icc cL cR
```

を generic helper として用意してよい。

これにより将来

```text
prime-power centered phase interval
  ⊆ known derivative sign cell
```

を単純な endpoint inequality で証明できる。

推奨 helper:

```lean
cfzpPrimePowerCenteredAngle_Icc_subset_of_cell_bounds
```

名前は調整可。

---

# 10. Gate H — optional quadrant cell certificates

Mathlib の real trig interval API が自然に使える場合のみ、explicit quadrant interval の sign certificate を追加してよい。

例えば phase angle が

```text
π ≤ θ ≤ 3π/2
```

にあるとき

```text
sin θ ≤ 0
cos θ ≤ 0
```

を得る thin adapter、または

```text
3π/2 ≤ θ ≤ 2π
```

で

```text
sin θ ≤ 0
0 ≤ cos θ
```

を得る adapter が自然に閉じるなら有用。

ただし theorem-name 探索が重い場合は必須にしない。

006Y の必須成果は **angular normalization と coverage-to-event bridge** であり、trig periodic cell library の全面実装ではない。

また arbitrary integer period `2πk` まで一般化しようとして scope を広げない。

---

# 11. Gate I — derivative sign-change witness の扱い

006X 指示書では `π/T` と `2π/T` で derivative core の逆符号 witness を optional としたが、006X implementation では必須にしていない。

006Y でもこれは optional のままでよい。

もし phase-normalized core `H` なら簡単に

```text
H(α,π) < 0
H(α,2π) > 0
```

を `α ≥ 0` の下で exact に閉じられる場合は、global fixed-sign route が不可能であることを明示する補助 audit として追加してよい。

しかし proof が noisy なら省略する。

重要なのは universal monotonicityを仮定しないこと。

---

# 12. 今回閉じる frontier / 残す frontier

## 12.1 今回閉じるもの

006X の frontier

```text
centered u-interval derivative sign coverage
```

を

```text
dimensionless centered phase interval
[Θ-η, Θ+η]
```

上の explicit finite sign-cell coverage 問題へ変換する。

つまり006Y Green 後は

```text
Θ = j*T*log p
η = ε*T
```

が phase cell のどこに入るかだけを調べれば、既存 derivative/event machinery へ exact に接続できる。

## 12.2 必ず残すもの

未解決:

- 全 prime powers の centered angular interval が同一 sign cell に入ること
- arithmetic centers `j*T*log p` の distribution
- phase-cell crossing event の一般分類
- all prime powers の共通 event sign
- cumulative ledger monotonicity
- cumulative ledger one-sidedness / boundedness
- finite baseline reach existence
- cofinal reach
- convergence
- correction source sign
- top-horizontal matching
- zeta-zero conclusion
- RH conclusion

推奨 frontier marker:

```lean
inductive CfzpPrimePowerPhaseCellArithmeticCoverageGap : Prop
  | noIndependentPrimePowerArithmeticCenterPhaseCellCoverageProvider
```

006X の derivative-cell coverage marker は履歴として残してよい。

---

# 13. Dependency / firewall

006Y は finite real angular-coordinate audit である。

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- infinite Euler product
- infinite prime distribution theorem の導入
- equidistribution claim
- density claim
- 新規 `X → ∞` argument
- infinite sum/integral exchange
- unconditional global phase-core sign
- unconditional profile monotonicity
- unconditional event sign
- cumulative ledger monotonicity
- baseline reach existence
- convergence
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

使うものは finite prime-power witness、`Real.log`, real `sin/cos`, interval/order algebra のみ。

---

# 14. 実装順序

推奨:

```text
1. new module / imports
2. dimensionless phase sin coefficient Aθ
3. dimensionless phase derivative core H
4. D(a,T,u) = H(a/T,u*T) exact bridge
5. optional rectangle aspect ratio helper
6. prime-power angular center Θ / halfwidth η / left-right angle
7. angular coordinate exact identities and positivity/order
8. angular phase-core coverage → original derivative-core coverage
9. dimensionless phase sign-cell theorems
10. phase-cell coverage → one-event sign adapters
11. generic centered-angle interval subset certificate
12. optional quadrant / π,2π witnesses
13. frontier marker
14. DkMath/RH.lean public import
```

---

# 15. 成功条件

006Y Green 条件:

1. `CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. dimensionless phase derivative sin coefficient を first-class 化。
4. dimensionless phase derivative core `H(α,θ)` を first-class 化。
5. `T ≠ 0` の下で `D(a,T,u) = H(a/T,u*T)` を exact に証明。
6. prime-power center angle `Θ = j*T*log p` を first-class 化。
7. phase halfwidth `η = ε*T` を first-class 化。
8. left/right angleを `Θ-η`, `Θ+η` として first-class 化。
9. safe regime と witnessed prime power から `0 < θL < θR` を exact に得る。
10. angular phase-core nonpositive coverageから original derivative-core nonpositive coverageを exact に得る。
11. dual nonnegative coverageも得る。
12. angular phase-core nonpositive coverageから prime-power event nonnegativeを conditional に得る。
13. dualに angular phase-core nonnegative coverageから event nonpositiveを得る。
14. 少なくとも一つの dimensionless nonpositive sign-cell theorem。
15. 少なくとも一つの dimensionless nonnegative sign-cell theorem。
16. all prime powers の phase-cell coverageを主張しない。
17. equidistribution / densityを主張しない。
18. universal event signを主張しない。
19. cumulative ledger monotonicityを主張しない。
20. reach existence / convergenceを主張しない。
21. zeta-zero / RHを主張しない。
22. target module build Green。
23. `lake build DkMath.RH` Green。
24. `./lean-build.sh` Green。
25. `./lean-test.sh` Green。
26. `git diff --check` Green。
27. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
28. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 16. 006Z への候補

006Y が Green になった後の第一候補は

```text
CFZP-006Z — finite prime-power phase-cell partition / signed-ledger decomposition audit
```

である。

006Y 後は各 witnessed pair `(p,j)` に対し centered angular interval

```text
[Θ-η, Θ+η]
```

が first-class になる。

次段では有限 pair-support を

```text
certified nonpositive-derivative cell
certified nonnegative-derivative cell
crossing / unresolved cell
```

の三群へ partition し、branch-free trig ledger を

```text
Ledger
  = Ledger_nonnegEvent
    + Ledger_nonposEvent
    + Ledger_unresolved
```

という exact finite signed decompositionへ落とすことを候補とする。

ただし unresolved 群を空と仮定してはならない。

目的は universal sign を出すことではなく、**どの prime-power events が sign-certified で、どれが frontier に残るかを有限 ledger 上で可視化すること**である。

---

# 17. 006Y の位置づけ

```text
006R  cutoff dynamics
006S  event support = prime powers
006T  one-event sign = phase primitive balance
006U  cumulative contact = closed-phase ledger reaches baseline
006V  safe regimeで branch-free exp/cos/sin ledger
006W  one-event = centered profile displacement F(L-ε)-F(L+ε)
006X  derivative core / local monotonicity → centered event sign
006Y  u-intervalを dimensionless phase-cell [Θ-η,Θ+η] へ変換
```

006Y は prime distribution theorem ではない。

役割は、残る sign-provider 問題を

```text
j*T*log p
```

という具体的 prime-power arithmetic center と有限 trigonometric phase-cell occupancy の問題へ exact に変換することである。
