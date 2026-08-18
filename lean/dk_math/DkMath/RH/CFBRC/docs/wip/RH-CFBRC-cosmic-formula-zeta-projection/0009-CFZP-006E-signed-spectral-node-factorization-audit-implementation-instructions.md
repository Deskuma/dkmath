# CFZP-0009 — CFZP-006E signed spectral-node factorization audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した Green checkpoint:

```text
6737f6e7134119fba1e31484f0f451e9d6a544fd
Add: CFZP-0008: CFZP-006D off-diagonal pair / Gram-index audit
```

CFZP-006D 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit
```

CFZP-006D は prime-power label 上で次を exact に閉じた。

```text
PairReal(q,r)
  = Re(ScaledMode(q) * conj(ScaledMode(r)))

FullPairSum
  = TotalSourceMass

DiagonalPairSum
  = SquaredWeightDiagonal

FullPairSum
  = DiagonalPairSum + OffDiagonalPairSum

CrossModeInterference
  = OffDiagonalPairSum
```

`OffDiagonalPairSum` は符号不定であり、非負性は主張していない。

今回の CFZP-006E では、既存 `MellinQuadraticGramKernel` の feature

```text
c_j * z_j * exp(t * z_j)
```

へ prime-power mode を接続するための **mode-level signed spectral lift** を作る。

---

# 1. 今回の数学的核心

一つの prime-power label `q > 1` を固定する。

functional-reflection mode は

```text
D_q(s) = q^(-(1-s)) - q^(-s)
```

である。

`s` を実方向へ `τ` だけ平行移動すると、CFZP-001/005 の branch-free factorization から

```text
D_q(s + τ)
```

の実方向依存は

```text
exp(+τ log q)
exp(-τ log q)
```

の二本へ exact に分かれる。

したがって Mellin spectral node の自然な候補は `q` 自身ではなく

```text
z₊(q) = +log q
z₋(q) = -log q
```

である。

さらに `MellinQuadraticGramKernel` の feature には node factor `z_j` 自身が掛かるため、係数側を `log q` で割れば、二本の feature の和が shifted scaled mode そのものになる。

**minus branch の係数には余分な minus を入れないこと。**

`z₋ = -log q` 自身が functional difference の minus sign を供給する。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaSignedSpectralNodeFactorizationAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSignedSpectralNodeFactorizationAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit
import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic
```

既存 `DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — horizontal real shift

実方向平行移動を明示する。

推奨:

```lean
noncomputable def cfzpHorizontalRealShift (s : ℂ) (τ : ℝ) : ℂ :=
  s + (τ : ℂ)
```

最低限、次を使いやすい theorem surface として用意する。

```text
re(shift s τ) = re(s) + τ
im(shift s τ) = im(s)
centeredSigma(re(shift s τ)) = centeredSigma(re(s)) + τ
```

新しい `Complex.log` branch を導入しない。

---

# 4. Gate B — amplitude の horizontal-shift factorization

`q > 1`、任意 `s, τ` に対して、既存 real amplitude 定義から exact に

```text
RightAmplitude(q, centeredSigma(re(shift s τ)))
  = RightAmplitude(q, centeredSigma(re s)) * exp(+τ log q)

LeftAmplitude(q, centeredSigma(re(shift s τ)))
  = LeftAmplitude(q, centeredSigma(re s)) * exp(-τ log q)
```

を得る。

Lean 上の都合で factor の左右順序を変えてよい。

証明は `Real.exp_add` と既存 amplitude 定義を使う。

cycle は実方向 shift で不変:

```text
Cycle(q, im(shift s τ)) = Cycle(q, im s)
```

ここでも phase/argument 関数を使わない。

---

# 5. Gate C — signed log nodes

`q > 1` に対する二つの spectral node を定義する。

推奨:

```lean
noncomputable def cfzpPrimePowerPositiveLogNode (q : ℕ) : ℂ :=
  (Real.log (q : ℝ) : ℂ)

noncomputable def cfzpPrimePowerNegativeLogNode (q : ℕ) : ℂ :=
  -(Real.log (q : ℝ) : ℂ)
```

最低限、次を証明する。

```text
NegativeLogNode(q) = -PositiveLogNode(q)
q > 1 -> PositiveLogNode(q) ≠ 0
q > 1 -> NegativeLogNode(q) ≠ 0
q > 1 -> PositiveLogNode(q) ≠ NegativeLogNode(q)
conj(PositiveLogNode(q)) = PositiveLogNode(q)
conj(NegativeLogNode(q)) = NegativeLogNode(q)
```

`q > 1` は canonical support 上では既存

```lean
one_lt_of_mem_canonicalPrimePowerSupportUpTo
```

から供給できる。

---

# 6. Gate D — two signed coefficients

CFZP-006C/006D の scaled mode

```lean
cfzpCanonicalFunctionalReflectionScaledMode q s
```

を target とする。

略記:

```text
w_q = canonicalPrimePowerShadowCost q
K_q = cfzpPrimePowerCommonRadialCarrier q
δ_s = centeredSigma s.re
C_q(t) = cfzpPrimePowerCycleState q t
L_q = primeMirrorLeftAmplitude q δ_s
R_q = primeMirrorRightAmplitude q δ_s
ℓ_q = log q
```

plus coefficient の意味は

```text
c₊(q,s)
  = w_q * K_q * R_q * C_q(-s.im) / ℓ_q
```

minus coefficient の意味は

```text
c₋(q,s)
  = w_q * K_q * L_q * C_q(+s.im) / ℓ_q
```

である。

実装では cast / associativity の都合に合わせてよい。

重要:

```text
c₋ に minus sign を入れない。
```

`NegativeLogNode = -ℓ_q` が minus sign を供給する。

分母非零は `q > 1 -> Real.log q > 0` から処理する。

---

# 7. Gate E — load-bearing two-node Mellin feature identity

今回の最重要 theorem。

`q > 1` に対し、任意 `s : ℂ`, `τ : ℝ` で概念的に

```text
ScaledMode(q, shift(s,τ))
  = c₊(q,s) *
      (z₊(q) * exp(τ * z₊(q)))
    + c₋(q,s) *
      (z₋(q) * exp(τ * z₋(q)))
```

を exact に証明する。

ここで左辺は必ず既存

```lean
cfzpCanonicalFunctionalReflectionScaledMode
```

を使う。

右辺の exponential は `MellinQuadraticGramKernel` と同じ

```lean
Complex.exp ((τ : ℂ) * z)
```

の形へ揃える。

推奨証明経路:

1. `cfzpFunctionalReflectionModeDifference_eq_commonRadial_mul_phaseDisplacedAmplitude`
2. Gate A/B の horizontal shift
3. `Real.exp` と `Complex.exp` の既存 bridge
4. `q > 1` から `log q ≠ 0`
5. ring/field normalization

新しい `Complex.log` を使って `cpow` を直接展開する必要はない。

また `τ = 0` specialization として

```text
ScaledMode(q,s)
  = c₊(q,s) * z₊(q) + c₋(q,s) * z₋(q)
```

を theorem 化する。

---

# 8. Gate F — `Fin 2` Mellin feature package

既存 `mellinQuadraticBoxGramEnergy` は `Fin n` family を受け取る。

今回、一つの `q` について `Fin 2` package を作る。

推奨 API:

```text
cfzpPrimePowerSignedLogNodeFamily q : Fin 2 -> ℂ
cfzpPrimePowerSignedLogCoefficientFamily q s : Fin 2 -> ℂ
```

index convention は明記する。

```text
0 -> +log q
1 -> -log q
```

または逆でもよいが、module 内で固定する。

load-bearing theorem:

```text
ScaledMode(q, shift(s,τ))
  = sum_{k : Fin 2}
      coefficient(q,s,k) *
        (node(q,k) * exp(τ * node(q,k)))
```

これにより、一つの prime-power mode が既存 Mellin Gram feature map の exact 2-node instance になったことを確定する。

---

# 9. Gate G — per-mode Gram energy bridge

可能なら同じ checkpoint で、一つの `q` に限って既存 Gram energy を instantiate する。

推奨定義:

```text
cfzpPrimePowerSignedTwoNodeGramEnergy ε q s
```

意味:

```text
mellinQuadraticBoxGramEnergy
  ε
  (cfzpPrimePowerSignedLogNodeFamily q)
  (cfzpPrimePowerSignedLogCoefficientFamily q s)
```

`q > 1` に対し exact に

```text
TwoNodeGramEnergy(ε,q,s)
  = (2*ε)^(-1) *
      integral_{τ=-ε}^{ε}
        normSq(ScaledMode(q, shift(s,τ))) dτ
```

を証明する。

既存 `mellinQuadraticBoxGramEnergy` の定義と Gate F の identity を再利用し、Gram kernel positivity を再証明しない。

さらに `ε > 0` なら

```text
0 <= TwoNodeGramEnergy(ε,q,s)
```

を既存

```lean
mellinQuadraticBoxGramEnergy_nonneg
```

から得てよい。

この非負性は **一つの q の horizontal-box quadratic energy** に限る。

---

# 10. arithmetic coefficient normalization — optional audit

canonical support では `q = p^j`、`j > 0` に対して

```text
w_q = log p
log q = j * log p
```

なので、形式的には

```text
w_q / log q = 1 / j
```

となる。

これは classical prime-power coefficient `1/j` が signed-node coefficient に現れることを示す重要な補助観測である。

ただし Lean の `Real.log_pow` / cast normalization がこの checkpoint を不必要に重くする場合は **実装しなくてよい**。006E Green の必須条件にはしない。

---

# 11. 明示的 firewall

今回、次は行わない。

1. canonical support 全体を `Fin (2*N)` へ flatten/reindex しない。
2. `q,r` pair sum 全体を `mellinQuadraticBoxGramEnergy` と同一視しない。
3. CS38 の signed linear Mellin density を quadratic Gram energy と同一視しない。
4. `CompletionRemainder` と Gram energy を同一視しない。
5. off-diagonal interference の非負性を主張しない。
6. rectangle background の非負性を主張しない。
7. infinite Euler product / infinite prime sum を導入しない。
8. `Complex.arg` を使わない。
9. 新しい global `Complex.log` branch を導入しない。
10. RH / zero-set exclusion を主張しない。
11. `sorry` / `admit` / 新規 `axiom` を入れない。

今回得る positivity は、あくまで既存 Mellin Gram positivity を **一つの q の signed two-node feature** に instantiate したものだけである。

---

# 12. 次 checkpoint への Gap marker

今回の終了時点では、次の bridge は未実装として明示する。

推奨 marker:

```lean
inductive CfzpSignedPrimePowerFamilyToFullMellinGramBridgeGap : Prop
  | noFiniteCanonicalSignedSupportEnumerationProvided
```

必要なら top-edge geometry 側も別 marker にする。

次 checkpoint の候補は:

```text
canonicalPrimePowerSupportUpTo X × Fin 2
  -> one finite spectral family
  -> full shifted canonical source
  -> Mellin quadratic Gram energy
```

である。

その際、rectangle top edge の実変数 `u` を critical center からの horizontal coordinate

```text
τ = u - 1/2
```

へ移す geometry bridge を検討する。

---

# 13. 完了条件

最低限:

1. horizontal real shift API
2. left/right amplitude shift factorization
3. signed nodes `±log q`
4. node nonzero/distinct/real-conjugation properties for `q > 1`
5. plus/minus coefficients
6. shifted scaled mode の exact two-node feature identity
7. `τ = 0` specialization
8. `Fin 2` node/coefficient package
9. `Fin 2` sum と shifted scaled mode の exact equality
10. 可能なら per-mode `mellinQuadraticBoxGramEnergy` bridge + nonneg
11. full finite-support bridge は Gap marker のまま
12. `DkMath/RH.lean` public import
13. target module build Green
14. `lake build DkMath.RH` Green
15. nested `./lean-build.sh` Green
16. nested `./lean-test.sh` Green
17. `git diff --check` Green
18. new module に `sorry` / `admit` / `axiom` なし

完了したらここで止める。

次の canonical-support flattening / full Mellin Gram bridge へ勝手に進まないこと。
