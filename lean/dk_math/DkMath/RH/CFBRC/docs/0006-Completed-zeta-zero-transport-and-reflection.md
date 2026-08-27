# Completed zeta への零点移送と反射対称性

## 1. この文書の位置

`0004` では、Mathlib の標準 `riemannZeta` の非自明零点を CFBRC 零点へ写すための論理 bridge を整理した。

`0005` では、その bridge の別経路として有限 centered closure と finite eta realization を記録した。

この文書では、標準ゼータ零点を completed zeta へ移し、さらに functional equation により反射点 `1 - s` へ零点条件を運ぶ層を記録する。

対象 module は主に次である。

```text
DkMath.RH.CFBRC.ZeroLocusFactorBridge
DkMath.RH.CFBRC.CompletedZetaBridge
```

この段階で重要なのは、completed zeta の反射対称性を使っても、まだ `s.re = 1 / 2` は結論していないことである。

---

## 2. 零点集合を保つ一般 factor bridge

`ZeroLocusFactorBridge.lean` では、二つの複素関数 `F`, `G` が非零 multiplier を介して同一化されるとき、同じ domain 上で零点集合が一致するという一般構造を定義している。

```lean
structure TwoSidedNonzeroFactorBridge
    (Domain : ℂ → Prop) (F G : ℂ → ℂ) where
  leftMultiplier : ℂ → ℂ
  rightMultiplier : ℂ → ℂ
  factor_eq : ∀ {s : ℂ}, Domain s →
    leftMultiplier s * F s = rightMultiplier s * G s
  leftMultiplier_ne_zero : ∀ {s : ℂ}, Domain s → leftMultiplier s ≠ 0
  rightMultiplier_ne_zero : ∀ {s : ℂ}, Domain s → rightMultiplier s ≠ 0
```

この構造から、

```lean
TwoSidedNonzeroFactorBridge.zero_iff
```

が得られる。

数学的には、domain 内で

$$
L(s)F(s)=R(s)G(s)
$$

かつ

$$
L(s)\ne0,\qquad R(s)\ne0
$$

なら、

$$
F(s)=0\iff G(s)=0
$$

というだけの一般原理である。

これは CFBRC 固有ではなく、後から標準ゼータや completed zeta などの零点集合を安全に移送するための基礎部品である。

---

## 3. 非自明零点 domain

標準ゼータについては、

```lean
def RiemannZetaNontrivialDomain (s : ℂ) : Prop :=
  (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1
```

が定義される。

そして、

```lean
NontrivialRiemannZetaZero s
```

は、

```text
riemannZeta s = 0
かつ
RiemannZetaNontrivialDomain s
```

と定義的に一致する。

したがって、この文書で扱う「標準非自明零点」は、trivial negative-even zeros と pole point `1` を除外した標準ゼータ零点である。

---

## 4. CFBRC factorization contract

同じ一般 factor bridge を用いて、標準ゼータから CFBRC value への factorization contract も定義されている。

```lean
abbrev StandardZetaCFBRCFactorization
    (d : ℕ) (phase : ℂ → ℝ) :=
  TwoSidedNonzeroFactorBridge
    RiemannZetaNontrivialDomain
    riemannZeta
    (standardCFBRCValue d phase)
```

この factorization が実際に供給されれば、

```lean
standardZeta_map_zero_of_factorization
```

によって `map_zero` が得られ、さらに正次数なら

```lean
riemannHypothesis_of_standardZetaCFBRCFactorization
```

により `RiemannHypothesis` が得られる。

ここでも、factorization の「器」が完成していることと、その factorization 自体が証明済みであることは区別する。

---

## 5. 非自明零点では `s ≠ 0`

`CompletedZetaBridge.lean` では、最初に

```lean
theorem nontrivialRiemannZetaZero_ne_zero
```

を証明する。

これは `riemannZeta 0` が零ではないという Mathlib の既知事実を使い、標準非自明零点が `s = 0` ではありえないことを固定する。

この補題は completed zeta の定義式を安全に用いるための前提である。

---

## 6. `Gammaℝ` factor の非零

次に、

```lean
theorem gammaR_ne_zero_of_nontrivialRiemannZetaZero
```

によって、標準非自明零点 `s` では

$$
\Gamma_{\mathbb R}(s)\ne0
$$

が示される。

Gamma factor の零点は標準ゼータの trivial negative-even zero pattern と対応するため、非自明零点 domain の除外条件から非零性が得られる。

この補題により、standard zeta と completed zeta の間で multiplier による偽の零点が発生しないことが保証される。

---

## 7. standard zeta と completed zeta の零点同値

`CompletedZetaBridge.lean` の中心定理は、

```lean
theorem riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
```

である。

前提は、

```text
s ≠ 0
Gammaℝ s ≠ 0
```

である。

そのもとで、

$$
\zeta(s)=0
\iff
\Lambda(s)=0
$$

が得られる。

ここで `Λ` は Mathlib の `completedRiemannZeta` を表す。

したがって標準非自明零点に対しては、前節までの非零性から

```lean
theorem completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero
```

が直ちに従う。

---

## 8. functional equation による反射零点

completed zeta には、Mathlib の functional equation

$$
\Lambda(1-s)=\Lambda(s)
$$

がある。

DkMath では、これを零点条件として

```lean
theorem completedRiemannZeta_one_sub_eq_zero_iff (s : ℂ) :
    completedRiemannZeta (1 - s) = 0 ↔
      completedRiemannZeta s = 0
```

と固定している。

さらに標準非自明零点 `s` からは、

```lean
theorem completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero
```

によって

$$
\Lambda(1-s)=0
$$

も得られる。

つまり、標準非自明零点一つから、completed zeta 上では `s` と `1-s` の両方が零点として得られる。

---

## 9. ここで何が証明されたか

この段階で Lean Green として固定されているのは次の鎖である。

```text
NontrivialRiemannZetaZero s
        ↓
s ≠ 0
        ↓
Gammaℝ s ≠ 0
        ↓
riemannZeta s = 0
  ↔ completedRiemannZeta s = 0
        ↓
completedRiemannZeta s = 0
        ↓ functional equation
completedRiemannZeta (1 - s) = 0
```

これは標準ゼータ零点を completed-zeta symmetry world へ移送する確定 Core である。

---

## 10. まだ証明していないこと

重要なのは、

$$
\Lambda(s)=0
$$

と

$$
\Lambda(1-s)=0
$$

が同時に成立することだけでは、

$$
s=1-s
$$

は導けないことである。

したがって、

$$
s.re=\frac12
$$

も、この文書の定理群だけからは得られない。

functional equation は零点集合の反射対称性を与えるが、各零点が反射固定点でなければならないことまでは言わない。

この区別は RH 形式化において極めて重要である。

---

## 11. CFBRC との関係

`0003` では、CFBRC 側では

$$
\operatorname{offCriticalCFBRC}(d,\sigma,\Theta)=0
\iff
\sigma=\frac12
$$

が既に証明済みであった。

一方この `0006` では、標準ゼータ零点を completed zeta の反射対称な零点対へ移した。

したがって次の研究課題は、単なる functional reflection ではなく、completed-zeta zero geometry を CFBRC の centered zero geometry へ接続することである。

概念的には、

```text
standard zeta zero
  ↓
completed zeta zero pair
  ↓
centered / mirror geometry
  ↓
CFBRC centered zero
```

という橋が必要になる。

---

## 12. 状態分類

```text
Core:
  standard nontrivial zeta zero → completed-zeta zero
  Gammaℝ factor の非零
  completed-zeta functional reflection

Beam:
  completed-zeta symmetry を centered / mirror CFBRC geometry へ運ぶ経路

Gap:
  reflected zero pair が CFBRC zero condition を供給する load-bearing bridge

Obstruction:
  functional equation の対称性だけでは s = 1 - s は導けない
```

---

## 13. 次の文書への接続

次は、`criticalMirror` や centered mirror geometry を導入し、

```text
s
1 - s
critical mirror
Re(s) = 1 / 2 fixed point
```

の関係を Lean 上でどう固定しているかを記録する。

そこで初めて completed-zeta reflection と CFBRC centered coordinate の幾何が同じ図の中に入る。
