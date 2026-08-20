# CFZP-0008 — CFZP-006D off-diagonal pair / Gram-index audit 実装指示書

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
2b06c6cb67c1b77d7bcb06cbdc6dde7faa5bda96
Add: CFZP-0007: CFZP-006C functional quadratic companion audit
```

CFZP-006C 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit
```

CFZP-006C は次を exact に閉じている。

```text
FunctionalModeMass
  = CycleMass + SameHeightMass + ModeCross

SameHeightMass
  = carrier normSq * prime-mirror amplitude Gap

AggregateFunctionalQuadraticLedger
  = AggregateCycleLedger
    + CFZP-004 CarrierWeightedMirrorGap
    + AggregateModeCrossLedger

Im(s) = 0
  -> AggregateFunctionalQuadraticLedger = CarrierWeightedMirrorGap

Re(s) = 1/2
  -> AggregateFunctionalQuadraticLedger = AggregateCycleLedger

SquaredWeightDiagonal
  = sum_q normSq(ScaledMode_q)

TotalSourceMass
  = normSq(CanonicalFunctionalReflectionLinearSource)

TotalSourceMass
  = SquaredWeightDiagonal + CrossModeInterference
```

`CrossModeInterference` は差分定義で exact に保持されている。

今回の CFZP-006D では、この差分を有限 Hermitian pair sum として展開し、prime-power label 上の pair quadratic form と既存 Mellin Gram kernel の index semantics を明確に分離する。

---

# 1. 今回の目的

CFZP-006C で二つの quadratic layer が分離された。

第一は linear-weight diagonal ledger:

```text
sum_q w_q * normSq(D_q)
```

第二は actual finite linear source 全体の quadratic mass:

```text
normSq(sum_q w_q * D_q)
```

後者を展開すると、対角は

```text
sum_q w_q^2 * normSq(D_q)
```

となり、さらに異なる mode 間の interference が出る。

今回の目的は、この interference を単なる差分名ではなく

```text
q != r
```

の off-diagonal pair sum として exact に回収することである。

同時に、既存

```text
DkMath.Analysis.MellinQuadraticGramKernel
```

との意味論的境界を固定する。

重要なのは、今回作る pair index は

```text
prime-power label q, r
```

である一方、既存 Mellin Gram kernel の基本変数は

```text
spectral node z, w
```

であること。

したがって両者を名前だけで同一視しない。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaOffDiagonalPairGramAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit
import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic
```

`MellinQuadraticGramKernel` は比較対象として import する。

今回その positivity を CFZP source へ輸送したと主張してはならない。

---

# 3. A — scaled functional mode を pair kernel の原子にする

CFZP-006C の既存定義を再利用する。

```lean
cfzpCanonicalFunctionalReflectionScaledMode
```

概念的には

```text
a_q(s) := w_q * D_q(s)
```

である。

新しい別名を作る必要はない。

必要なら local notation を使ってよい。

---

# 4. B — real Hermitian pair kernel

prime-power pair `(q,r)` に対し、実数値 pair kernel を定義する。

推奨形:

```lean
noncomputable def cfzpCanonicalFunctionalReflectionPairReal
    (q r : ℕ) (s : ℂ) : ℝ :=
  (cfzpCanonicalFunctionalReflectionScaledMode q s *
    conj (cfzpCanonicalFunctionalReflectionScaledMode r s)).re
```

共役の向きを逆に選んでもよいが、後続 theorem の orientation を一貫させること。

期待 theorem:

```text
PairReal(q,r) = PairReal(r,q)
```

これは real Hermitian symmetry の bookkeeping 用であり、positivity theorem ではない。

対角では exact に

```text
PairReal(q,q) = normSq(ScaledMode_q)
```

を証明する。

さらに CFZP-006C の theorem を使い、

```text
PairReal(q,q)
  = w_q^2 * FunctionalModeMass_q
```

まで bridge してよい。

---

# 5. C — full finite pair quadratic sum

canonical support 上の full ordered pair sum を定義する。

推奨形:

```lean
noncomputable def cfzpCanonicalFunctionalReflectionFullPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    ∑ r ∈ canonicalPrimePowerSupportUpTo X,
      cfzpCanonicalFunctionalReflectionPairReal q r s
```

最重要 theorem:

```text
FullPairSumUpTo X s
  = cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s
```

すなわち

```text
sum_q sum_r Re(a_q * conj(a_r))
  = normSq(sum_q a_q)
```

を exact に閉じる。

### 実装上の注意

`normSq(sum ...)` を `simp` に丸投げして「和に分配」させない。

有限和の積の展開として証明する。

概念的には

```text
normSq(A) = Re(A * conj(A))
```

または既存 `Complex.normSq` API と `map_sum` / `Finset.sum_mul` / `Finset.mul_sum` を使う。

どの向きの conjugation API が最も安定するかは Lean に合わせてよい。

---

# 6. D — diagonal pair sum と squared-weight diagonal の一致

pair kernel の対角だけを集約する。

推奨定義:

```lean
noncomputable def cfzpCanonicalFunctionalReflectionDiagonalPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    cfzpCanonicalFunctionalReflectionPairReal q q s
```

要求 theorem:

```text
DiagonalPairSumUpTo X s
  = cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s
```

ここで CFZP-006C の squared-weight diagonal を再定義しない。

---

# 7. E — explicit off-diagonal pair sum

今回は `CrossModeInterference` を本当に off-diagonal pair sum として expose する。

推奨定義は `erase` を使う ordered pair sum。

```lean
noncomputable def cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    ∑ r ∈ (canonicalPrimePowerSupportUpTo X).erase q,
      cfzpCanonicalFunctionalReflectionPairReal q r s
```

outer sum の各 `q` は support member なので、`erase q` により diagonal を一度だけ除外できる。

要求 theorem 1:

```text
FullPairSumUpTo
  = DiagonalPairSumUpTo + OffDiagonalPairSumUpTo
```

要求 theorem 2:

```text
cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo X s
  = cfzpCanonicalFunctionalReflectionOffDiagonalPairSumUpTo X s
```

これが今回の load-bearing theorem である。

### 係数について

ordered pair sum なので `q,r` と `r,q` の両方が入る。

したがって、勝手に `2 * sum_{q<r}` へ変形しない。

必要なら symmetry theorem から後で導出できるが、今回不要。

---

# 8. F — weight-degree を pair level で明示する

pair kernel を展開すると係数は概念的に

```text
w_q * w_r
```

である。

必要 theorem:

```text
PairReal(q,r)
  = w_q * w_r * Re(D_q * conj(D_r))
```

対角では

```text
w_q * w_q
```

すなわち `w_q^2` になる。

これにより

```text
CFZP-004 carrier-weighted Gap ledger : weight degree 1
actual source normSq diagonal          : weight degree 2
```

という境界を theorem surface で見えるようにする。

ただし

```text
w_q^2 = w_q
```

を仮定・証明しようとしてはならない。

canonical shadow cost は一般に idempotent weight ではない。

---

# 9. G — positivity の正しい範囲

以下は nonnegative:

```text
TotalSourceMass
SquaredWeightDiagonal
FullPairSum
```

`FullPairSum` の非負性は `TotalSourceMass` との equality から得てよい。

一方、以下は符号不定のまま:

```text
OffDiagonalPairSum
CrossModeInterference
individual PairReal(q,r), q != r
```

off-diagonal に nonneg theorem を追加してはならない。

---

# 10. H — existing Mellin Gram との index-semantics audit

既存 general API:

```lean
DkMath.Analysis.mellinQuadraticBoxGramKernel
DkMath.Analysis.mellinQuadraticBoxGramEnergy
DkMath.Analysis.mellinQuadraticBoxGramQuadraticForm
```

は finite family の spectral nodes `z_j` と coefficients `c_j` を使う。

その positivity theorem:

```lean
mellinQuadraticBoxGramEnergy_nonneg
```

は既に Green である。

しかし今回の CFZP pair sum は固定された `s` における

```text
prime-power mode values D_q(s)
```

の Hermitian norm-square expansionである。

この二つは現時点では同一 object ではない。

今回、以下のような equality を provider なしで追加してはならない。

```text
CFZP FullPairSum = MellinQuadraticBoxGramEnergy
CFZP PairReal = mellinQuadraticBoxGramKernel
CFZP OffDiagonalPairSum = Mellin Gram off-diagonal
```

代わりに frontier marker を追加する。

例:

```lean
inductive CfzpPrimeModePairToMellinSpectralGramBridgeGap : Prop
  | noSourceDerivedIndexFeatureIdentificationProvided
```

名称は多少調整してよい。

### optional audit theorem

既存 Mellin Gram の theorem 名を import が見えることの確認として小さな wrapper を置いてもよいが、CFZP pair sum との equality は置かない。

---

# 11. I — existing 4B.3 quadraticization audit との関係

既存

```text
PascalCenteredXiPrimeSideQuadraticizationAudit
```

は source ledger が one-index linear surface であり、Mellin Gram が two-index quadratic form であることを既に記録している。

今回 CFZP-006D は、その古い frontier を prime-power pair algebra の側から一段具体化する。

```text
one-index canonical source
  -> exact q,r pair expansion
  -> full Hermitian finite pair sum
```

までは今回閉じる。

しかし

```text
q,r prime-mode pair family
  -> Mellin spectral-node Gram family
```

はまだ閉じない。

次の Gate で必要なら、source-derived feature map / reindexing / continuous contour family を調べる。

---

# 12. 今回禁止するもの

以下は禁止。

1. `CompletionRemainder = FullPairSum` と置く。
2. `CompletionRemainder >= 0` を Gram positivity から導く。
3. `OffDiagonalPairSum >= 0` を主張する。
4. `CrossModeInterference = 0` を仮定する。
5. `normSq(sum a_q) = sum normSq(a_q)` とする。
6. linear-weight diagonal と squared-weight diagonal を同一視する。
7. prime-power pair kernel を既存 Mellin Gram kernel と rename だけで同一視する。
8. CS24/25 ray energy と CFZP-004 amplitude ledger を同一視する。
9. `criticalMirror s = 1 - s` を一般に使う。
10. `Complex.arg` を新規 source bridge に使う。
11. global `Complex.log` branch を導入する。
12. infinite Euler product / cutoff limit / limit exchange を導入する。
13. RH / zero-set consequence を主張する。
14. `sorry` / `admit` / `axiom` を追加する。

---

# 13. 成功条件

Green-A:

- PairReal の Hermitian symmetry。
- diagonal pair が mode normSq と一致。
- full ordered pair sum が TotalSourceMass と一致。
- diagonal pair sum が SquaredWeightDiagonal と一致。
- explicit off-diagonal ordered pair sum を定義。
- FullPair = Diagonal + OffDiagonal。
- CrossModeInterference = OffDiagonalPairSum。
- pair weight が `w_q * w_r` と exact に展開される。
- FullPairSum の非負性。
- off-diagonal には sign theorem を追加しない。
- Mellin Gram との index/feature bridge は frontier として保持。

Green-B:

- full pair / diagonal decomposition は exact。
- `erase` を用いた explicit off-diagonal theorem の Lean proof engineering が閉じず、差分 off-diagonal までで停止。

ただし Green-B の場合も fake equality で埋めない。

Yellow:

- difference-defined CrossModeInterference を別名で rename しただけで、pair expansion がない。
- off-diagonal を非負と扱う。
- Mellin Gram と q-index pair sum を名前だけで同一視する。

Red:

- CompletionRemainder positivity をこの Gate で結論する。
- RH-equivalent theorem を source positivity provider として持ち込む。
- infinite / limit argument を未証明で導入する。

---

# 14. validation

最低限:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaOffDiagonalPairGramAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module に

```text
sorry
admit
axiom
```

が無いことを確認する。

Green 後にのみ `DkMath/RH.lean` へ public import を追加する。

---

# 15. 実装後停止位置

今回で止める。

次の CFZP-006E 候補は、この結果を見て選ぶ。

第一候補:

```text
prime-power q,r pair family
  -> source-derived Mellin feature family
  -> existing MellinQuadraticBoxGramKernel / GramEnergy
```

の exact index / feature bridge。

ただし 006D の実装結果から、既存 4B.3 continuous box feature のほうが正しい carrier であると判明した場合は、その object に合わせて 006E を再設計する。

`CompletionRemainder` との同一視はまだ行わない。
