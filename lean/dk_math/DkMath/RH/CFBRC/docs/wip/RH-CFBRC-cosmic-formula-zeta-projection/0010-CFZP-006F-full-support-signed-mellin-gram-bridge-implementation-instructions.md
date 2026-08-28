# CFZP-0010 — CFZP-006F full-support signed Mellin Gram bridge 実装指示書

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
e4914f2c39d963dc3cbdf6ecf62742baa233faa0
Add: CFZP-0009: CFZP-006E signed spectral-node factorization audit
```

CFZP-006E 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSignedSpectralNodeFactorizationAudit
```

CFZP-006E は各 canonical prime-power mode `q` を、exact に二つの Mellin spectral node

```text
+log q
-log q
```

へ持ち上げた。

さらに、`q > 1` に対し

```text
Σ k : Fin 2,
  coefficient(q,s,k) * node(q,k) * exp(τ * node(q,k))

= cfzpCanonicalFunctionalReflectionScaledMode q
    (cfzpHorizontalRealShift s τ)
```

を exact に持ち、per-mode の `mellinQuadraticBoxGramEnergy` bridge と非負性まで閉じている。

今回の CFZP-006F では、この `Fin 2` family を canonical finite prime-power support 全体で flatten し、**full finite PHZ functional-reflection source 自身を一つの Mellin Gram feature family として exact に同定する**。

---

# 1. 今回の数学的核心

canonical support を

```text
S_X := canonicalPrimePowerSupportUpTo X
```

とする。

各 `q ∈ S_X` は 006E により二つの node を持つ。

したがって full signed spectral index は自然に

```text
(q, k)
q ∈ S_X
k ∈ Fin 2
```

である。

この有限型を一つの `Fin N` へ reindex し、既存

```lean
mellinQuadraticBoxGramEnergy
mellinQuadraticBoxGramQuadraticForm
```

へ渡す。

目標となる exact identity は

```text
Σ full spectral index j,
  c_j * z_j * exp(τ z_j)

= cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
    (cfzpHorizontalRealShift s τ)
```

である。

従って full Gram energy は

```text
(2ε)^(-1) * ∫_{-ε}^{ε}
  normSq(
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (cfzpHorizontalRealShift s τ)) dτ
```

そのものになる。

これは 006D の fixed-point source mass

```text
normSq(Source_X(s))
```

とは別物である。

006F では **horizontal box average** までを exact に閉じる。`ε → 0` limit や CompletionRemainder との同一視は行わない。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaFullSignedMellinGramBridgeAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedMellinGramBridgeAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSignedSpectralNodeFactorizationAudit
import Mathlib.Tactic
```

必要なら `MellinQuadraticGramKernel` を明示 import してよいが、006E 経由で既に入っている場合は不要。

既存 `DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — canonical signed spectral index type

まず finite support の subtype を使う。

概念形:

```lean
abbrev CfzpCanonicalPrimePowerIndex (X : ℕ) :=
  {q : ℕ // q ∈ canonicalPrimePowerSupportUpTo X}

abbrev CfzpCanonicalSignedSpectralIndex (X : ℕ) :=
  CfzpCanonicalPrimePowerIndex X × Fin 2
```

名前は多少変更してよい。

重要なのは、`q` の membership proof を index 自身が保持すること。

これにより各 index で既存 theorem

```lean
one_lt_of_mem_canonicalPrimePowerSupportUpTo
```

から `1 < q` を取り出し、006E の per-mode theorem を安全に使える。

### optional cardinality audit

安価なら

```text
card(CfzpCanonicalSignedSpectralIndex X)
  = 2 * card(S_X)
```

または積の順序に応じた同値式を証明してよい。

これは必須ではない。

---

# 4. Gate B — raw finite-type node / coefficient family

`CfzpCanonicalSignedSpectralIndex X` 上で node と coefficient を定義する。

概念形:

```text
Node_X(q,k)
  := cfzpPrimePowerSignedLogNodeFamily q k

Coefficient_X,s(q,k)
  := cfzpPrimePowerSignedLogCoefficientFamily q s k
```

ここではまだ `Fin N` へ変換しなくてよい。

次の raw-index feature theorem を first-class theorem として閉じる。

```text
Σ i : CfzpCanonicalSignedSpectralIndex X,
  Coefficient_X,s(i) *
    (Node_X(i) * exp(τ * Node_X(i)))

= cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
    (cfzpHorizontalRealShift s τ)
```

証明では、有限型の積の sum を

```text
Σ q ∈ S_X, Σ k : Fin 2, ...
```

へ開き、各 `q` で 006E の

```lean
cfzpPrimePowerSignedLogFeatureFamily_sum_eq_scaledMode
```

を使う。

最後は

```lean
cfzpCanonicalFunctionalReflectionScaledMode
```

の定義と

```lean
cfzpCanonicalFunctionalReflectionLinearSourceUpTo
```

の定義を exact に合わせる。

新しい source weight を導入しない。

---

# 5. Gate C — `Fin N` flattening / reindex

既存 `mellinQuadraticBoxGramEnergy` は `Fin n → ℂ` family を要求する。

したがって raw finite index type を `Fin N` へ reindex する。

推奨方針:

```text
E_X : CfzpCanonicalSignedSpectralIndex X
      ≃ Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X))
```

`Fintype.equivFin` 等の Mathlib API を使ってよい。

次に Fin-indexed family を

```text
NodeFin_X(j) := Node_X(E_X.symm j)
CoefficientFin_X,s(j) := Coefficient_X,s(E_X.symm j)
```

として定義する。

reindex に依存する数学的内容を入れない。

次の theorem を exact に閉じる。

```text
Σ j : Fin N,
  CoefficientFin_X,s(j) *
    (NodeFin_X(j) * exp(τ * NodeFin_X(j)))

= cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
    (cfzpHorizontalRealShift s τ)
```

この theorem は Gate B の raw-index identity と有限和の Equiv reindex だけから出す。

### 重要

`Fintype.equivFin` の具体的 enumeration 順序には数学的意味を持たせない。

prime ordering / exponent ordering / plus-minus orderingを theorem の意味に混入させない。

---

# 6. Gate D — full canonical signed Mellin Gram energy

full-source Gram energy を定義する。

推奨:

```lean
noncomputable def cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
    (ε : ℝ) (X : ℕ) (s : ℂ) : ℝ :=
  mellinQuadraticBoxGramEnergy ε
    (cfzpCanonicalSignedLogNodeFinFamily X)
    (cfzpCanonicalSignedLogCoefficientFinFamily X s)
```

実名は既存 naming に合わせてよい。

load-bearing theorem:

```text
FullSignedGramEnergy(ε,X,s)

= (2 * ε)^(-1) *
    ∫ τ in (-ε)..ε,
      Complex.normSq(
        cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
          (cfzpHorizontalRealShift s τ))
```

証明は既存 `mellinQuadraticBoxGramEnergy` 定義または

```lean
mellinQuadraticBoxGramEnergy_eq_normalized_integral
```

と Gate C の full feature identityから行う。

complex cast が邪魔なら、実数定義を直接 unfold してよい。

### positivity

`0 < ε` の下で

```text
0 ≤ FullSignedGramEnergy(ε,X,s)
```

を証明する。

これは既存

```lean
mellinQuadraticBoxGramEnergy_nonneg
```

の direct reuse とする。

`X` の下限は不要であるべき。support が空でも Gram energy は 0 で非負。

---

# 7. Gate E — full Gram quadratic form surface

既存 Mellin Gram kernel との橋を明示するため、可能なら full quadratic form も定義する。

推奨:

```lean
cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm
```

内容:

```text
mellinQuadraticBoxGramQuadraticForm ε NodeFin CoefficientFin
```

`0 < ε` の下で既存 API から

```text
FullSignedGramQuadraticForm
  = (FullSignedGramEnergy : ℂ)

Im(FullSignedGramQuadraticForm) = 0

Re(FullSignedGramQuadraticForm)
  = FullSignedGramEnergy

0 ≤ Re(FullSignedGramQuadraticForm)
```

を閉じる。

これらは推奨 Gate。Lean API 上かなり安価なら実装する。

少なくとも `QuadraticForm = Energy` は欲しい。

---

# 8. Gate F — zero-shift recovery / 006D fixed sourceとの境界

`τ = 0` では full feature sum が元の finite source に戻る。

明示 theorem:

```text
FullSignedFeatureSum(X,s,0)
  = cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
```

さらに cheap なら

```text
Complex.normSq(FullSignedFeatureSum(X,s,0))
  = cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s
```

も閉じる。

これは 006D の

```text
FullPairSum = TotalSourceMass
```

への exact fixed-point 接続となる。

ただし次は **禁止**:

```text
FullSignedGramEnergy(ε,X,s)
  = TotalSourceMassUpTo X s
```

一般の `ε > 0` では left は horizontal box average、right は中心一点の mass である。

この equality は現時点ではない。

---

# 9. Gate G — optional source-labelled Mellin pair block

006D の `(q,r)` pair と Mellin Gram の signed-node pairを見比べるため、安価なら source-labelled block を定義してよい。

概念形:

```text
MellinPairBlock_ε(q,r,s)
  := Σ k : Fin 2, Σ l : Fin 2,
       c(q,k) * conj(c(r,l)) *
         mellinQuadraticBoxGramKernel ε z(q,k) z(r,l)
```

そして full quadratic form が

```text
Σ q ∈ S_X, Σ r ∈ S_X,
  MellinPairBlock_ε(q,r,s)
```

へ reindex できることを exact に証明できるなら有用。

ただしこれは optional。

**この block を 006D の `PairReal(q,r,s)` と同一視しない。**

前者は horizontal box averaged spectral Gram pair、後者は fixed-point `τ = 0` の real Hermitian pairである。

両者の接続には zero-width / approximate-identity audit が別途必要。

---

# 10. 今回閉じてはいけないもの

CFZP-006F では以下を禁止する。

- `FullSignedGramEnergy = CompletionRemainder`
- `FullSignedGramEnergy = RectangleBackground`
- `FullSignedGramEnergy = TopZetaMismatchScalar`
- `FullSignedGramEnergy = cfzpAggregateMirrorGapUpTo`
- `FullSignedGramEnergy = cfzpAggregateCarrierWeightedMirrorGapUpTo`
- `FullSignedGramEnergy = TotalSourceMassUpTo` for general `ε > 0`
- off-diagonal interference の非負性
- source remainder の非負性
- `SourceBig / SourceBody / SourceGap` の premature naming
- `ε → 0` limit の新規主張
- infinite Euler product
- zero-set / RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom`

今回の仕事は **full finite source の Mellin Gram family identification** だけである。

---

# 11. 成功条件

最低限、次が Green になれば CFZP-006F 完了とする。

```text
1. canonical support × Fin 2 の finite signed spectral index がある
2. raw finite-type full feature sum = shifted canonical linear source
3. Fin N への exact reindex がある
4. Fin-indexed full feature sum = shifted canonical linear source
5. full Mellin Gram energy = horizontal-box averaged shifted source normSq
6. 0 < ε -> full Mellin Gram energy ≥ 0
7. τ = 0 で元の canonical source を exact に回収
8. DkMath.RH public import
9. target module build Green
10. lake build DkMath.RH Green
11. nested ./lean-build.sh Green
12. nested ./lean-test.sh Green
13. git diff --check Green
14. 新規 module に sorry / admit / axiom なし
```

`QuadraticForm = Energy` surface と source-labelled Mellin pair block は可能なら追加する。

---

# 12. 次 Gate への判断材料

006F が Green になれば、次は **006G zero-width / centered-recovery audit** を検討する。

中心課題は

```text
horizontal-box Gram average
  ↓ ε → 0 ?
fixed-point TotalSourceMass
  = 006D FullPairSum
```

である。

ここで初めて既存 centered Mellin approximate-identity API が、full source feature に対して exact / limit bridge を与えられるかを監査する。

006G が閉じるまでは、Mellin Gram positivity を rectangle remainder や cosmic Gap の positivity と解釈しないこと。
