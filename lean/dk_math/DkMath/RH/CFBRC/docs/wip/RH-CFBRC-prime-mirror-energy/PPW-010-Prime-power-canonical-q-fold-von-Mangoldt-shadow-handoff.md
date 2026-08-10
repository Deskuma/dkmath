# PPW-010 — prime-power canonical q-fold / von-Mangoldt shadow 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-009-Prime-power-natural-cutoff-PHZ-finite-handoff.md
```

PPW-009 は Green 済み。追加済み module:

```text
DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
```

PPW-009 では自然数 cutoff

```text
p ^ (k + 1) ≤ X
```

を持つ有限 `(p,k)` pair-sum が完成した。

この checkpoint では、その pair-sum を canonical natural-number label

```text
q = p^j
```

へ折り畳み、有限 von-Mangoldt shadow weight を `q` の関数として固定する。

ここではまだ標準解析関数としての von Mangoldt 関数、`-ζ'/ζ`、無限級数、zeta zero、RH は扱わない。

---

## 2. PPW-009 レビュー結果

現在の有限 PHZ は exact に

$$
\operatorname{PHZ}_X(s)
:=
\sum_{p\le X,\ p\ \mathrm{prime}}
\sum_{k<X}
\mathbf 1_{p^{k+1}\le X}
(\log p) M_p(s)^{k+1}
$$

である。

また `PrimePowerLabel.vonMangoldtLogCost` を使った label-cost presentation も Green 化された。

一方、次の二点はまだ明示 theorem になっていない。

```text
1. M_p(s)^j = (p^j)^(-s) という natural label mode bridge
2. 同じ q に対する prime-power witness の base prime / exponent 一意性
```

PPW-010 はこの二点を Core 化し、`q`-indexed finite Dirichlet polynomial まで作る。

---

## 3. 新規 module

```text
DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalPrimePowerCanonicalFold.lean
```

公開 import は単体 Green 後に `DkMath/RH.lean` へ追加する。

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
import Mathlib.Tactic
```

Mathlib の prime-power / factorization API は実装時に検索し、存在する theorem を優先してよい。API 名を推測して新しい不要 lemma を増やさない。

---

## 4. Positive prime-power witness の一意性

### 4.1 まず base prime 一意性

数学的 Core:

$$
p^a=q^b,
\quad p,q\text{ prime},
\quad a,b>0
\Longrightarrow p=q.
$$

候補 theorem:

```lean
theorem prime_eq_of_pow_eq_pow
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (ha : 0 < a)
    (hb : 0 < b)
    (hpow : p ^ a = q ^ b) :
    p = q
```

証明方針は prime divisibility でよい。

```text
p ∣ p^a
→ p ∣ q^b
→ p ∣ q
→ p = q
```

既存 Mathlib theorem があればそれを使う。

### 4.2 exponent 一意性

base prime が同じなら `p > 1` なので、

$$
p^a=p^b\Longrightarrow a=b.
$$

候補:

```lean
theorem prime_pow_exponent_injective
    {p a b : ℕ}
    (hp : Nat.Prime p)
    (hpow : p ^ a = p ^ b) :
    a = b
```

### 4.3 witness pair 一意性

まとめて、

```lean
theorem primePower_witness_unique
    {p q a b n : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (ha : 0 < a)
    (hb : 0 < b)
    (hpw : n = p ^ a)
    (hqw : n = q ^ b) :
    p = q ∧ a = b
```

を固定する。

これは後の `q` fold の load-bearing theorem。

---

## 5. Prime-power mode を natural label mode へ接続

PPW-008/009 の mode は

```lean
eulerPrimePowerMode p j s = (eulerPrimePrimitiveMode p s)^j
```

である。

prime `p` と正指数 `j` に対して、

$$
M_p(s)^j=(p^j)^{-s}
$$

を exact に固定する。

候補 theorem:

```lean
theorem eulerPrimePowerMode_eq_natLabel_cpow_neg
    {p j : ℕ}
    (hp : Nat.Prime p)
    (hj : 0 < j)
    (s : ℂ) :
    eulerPrimePowerMode p j s =
      (((p ^ j : ℕ) : ℂ) ^ (-s))
```

`Complex.cpow` の normal form が重ければ、同じ数学内容を持つ `Complex.exp` / `Real.log` normal form を先に Core として置いてよい。

重要なのは branch-sensitive な一般複素 base の法則を仮定しないこと。ここで base は正の自然数 prime power である。

`PrimePowerLabel` 版も置く。

```lean
theorem eulerPrimePowerMode_eq_label_cpow_neg
    (L : PrimePowerLabel)
    (s : ℂ) :
    eulerPrimePowerMode L.p L.k s =
      ((L.q : ℂ) ^ (-s))
```

`L.eq_pow` を使う。

---

## 6. Canonical natural-number von-Mangoldt shadow

`q` だけから有限 shadow weight を読める関数を作る。

推奨設計は、prime-power witness の存在を判定し、存在時に一つ witness を選び、上の witness uniqueness により値が choice に依存しないことを証明するもの。

候補 predicate は既存:

```lean
DkMath.NumberTheory.PrimitiveSet.IsPrimePowerLabel q
```

候補定義:

```lean
noncomputable def primePowerBaseShadow (q : ℕ) : ℕ :=
  if hq : IsPrimePowerLabel q then
    Classical.choose hq
  else 1
```

ただし `Classical.choose hq` の型は witness の最初の成分になるので、実装上は helper structure / `choose` chain を使ってよい。

より自然なら、専用 witness structure を作って choice してよい。

```lean
noncomputable def canonicalPrimePowerShadowCost (q : ℕ) : ℝ :=
  if hq : IsPrimePowerLabel q then
    Real.log (primePowerBaseShadow q : ℝ)
  else 0
```

中心 theorem:

```lean
theorem canonicalPrimePowerShadowCost_eq_log_prime
    {q p k : ℕ}
    (hp : Nat.Prime p)
    (hk : 0 < k)
    (hq : q = p ^ k) :
    canonicalPrimePowerShadowCost q = Real.log (p : ℝ)
```

この theorem によって choice の内部表現を以後見せない。

さらに:

```lean
@[simp] theorem canonicalPrimePowerShadowCost_eq_zero_of_not_primePower

theorem canonicalPrimePowerShadowCost_nonneg
```

を置く。

この関数は「DkMath の finite von-Mangoldt shadow」であり、まだ Mathlib / classical analytic von Mangoldt function と同一視しない。

---

## 7. q-indexed finite PHZ

### 7.1 定義

canonical natural-number index で、

$$
\operatorname{PHZ}^{q}_X(s)
:=
\sum_{q=0}^{X}
\Lambda_{\mathrm{shadow}}(q)q^{-s}
$$

を有限和として定義する。

候補:

```lean
noncomputable def pascalPrimePowerPHZCanonicalUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (X + 1),
    (canonicalPrimePowerShadowCost q : ℂ) *
      ((q : ℂ) ^ (-s))
```

`q = 0,1` は shadow cost が 0 なので害がない。

### 7.2 pair-sum との一致

PPW-009 の

```lean
pascalPrimePowerPHZFiniteUpTo X s
```

と exact に一致させる。

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_canonical
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X s
```

これが PPW-010 の最重要 theorem。

証明には prime-power witness pair の一意性を使い、pair-sum から `q=p^k` への fold で重複計数がないことを明示する。

実装上 `Finset.map` / `Finset.image` / `sum_bij` のどれが自然かは Codex に任せる。

数学的に重要なのは、

```text
(p,k) representation が一意
→ q-index へ lossless fold
```

である。

---

## 8. `(X,X+1)` canonical shell

可能なら successor difference を q-index で固定する。

```lean
@[simp] theorem pascalPrimePowerPHZCanonicalUpTo_succ_sub
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZCanonicalUpTo (X + 1) s -
      pascalPrimePowerPHZCanonicalUpTo X s =
    (canonicalPrimePowerShadowCost (X + 1) : ℂ) *
      (((X + 1 : ℕ) : ℂ) ^ (-s))
```

これは自然数軸上の exact one-step decoder。

さらに prime-power / non-prime-power dichotomy:

```lean
theorem pascalPrimePowerPHZCanonical_succ_eq_of_primePower

theorem pascalPrimePowerPHZCanonical_succ_eq_of_not_primePower
```

が容易なら追加する。

---

## 9. Classical von Mangoldt との境界

PPW-010 で主張してよいもの:

```text
positive prime-power witness uniqueness
(p,k) mode → q=p^k natural mode
finite shadow cost q ↦ log p
pair-index PHZ ↔ canonical q-index PHZ
(X,X+1) exact natural-number shell
```

主張してはいけないもの:

```text
- canonicalPrimePowerShadowCost が既存 Mathlib の von Mangoldt function そのものである
- infinite Dirichlet series convergence
- -ζ'/ζ との equality
- analytic continuation into the critical strip
- zeta zero で PHZ が消える
- RH
```

特に `-ζ'/ζ` は zero-sensitive quantity だが、zeta zero では pole を持つ側であり、zero collapse として扱わない。

---

## 10. 次 checkpoint への出口

PPW-010 が Green になったら、PPW-011 で既存 Mathlib の von Mangoldt / logarithmic derivative API を監査する。

狙い:

```text
canonicalPrimePowerShadowCost q
  ↔ classical Λ(q)
```

を finite arithmetic theorem として先に固定し、その後 `Re(s) > 1` の安全領域で

$$
\sum_{q\ge1}\Lambda(q)q^{-s}
=
-\frac{\zeta'(s)}{\zeta(s)}
$$

へ接続する。

PPW-011 では API を先に調査し、既存 Mathlib theorem がある場合は再証明しない。

---

## 11. 推奨 build

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
lake build DkMath.RH
git diff --check
```

新規 module に `sorry` / `axiom` / `admit` を入れない。

証明工学上の theorem name、`Finset` fold 方法、`Complex.cpow` normal form は Codex に調整を任せるが、witness uniqueness と lossless q-fold の数学内容は弱めない。
