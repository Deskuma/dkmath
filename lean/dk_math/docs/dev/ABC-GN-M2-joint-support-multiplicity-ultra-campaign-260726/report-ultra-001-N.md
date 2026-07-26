# Ultra-001N Report — weighted GN depth-mass bad set

Date: 2026-07-26

## 判定

有限素数族の weighted GN depth mass と threshold bad set を正式化し、
平均 theorem から明示的 Markov cardinality bound を証明した。

```text
pointwise weighted depth mass       complete
finite threshold bad set            complete
mass nonnegativity                  complete
q-sensitive finite-family average   complete
Markov bad-set cardinality          complete
distinguished target escape         open
```

実装は `DkMath.ABC.GNDepthMassBadSet` に分離した。

## 1. Mass と bad set

```lean
noncomputable def GNDepthMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ

noncomputable def GNDepthMassBadSet
    (Q : Finset ℕ) (p b X : ℕ) (threshold : ℝ) : Finset ℕ
```

定義は、

```text
GNDepthMassAt Q p b a
  = ∑ q ∈ Q, padicValNat q (GN p a b) * log q

GNDepthMassBadSet Q p b X threshold
  = {a ∈ Icc 0 X | threshold < GNDepthMassAt Q p b a}.
```

`Q` の各要素が素数なら `GNDepthMassAt_nonneg` が mass の非負性を与える。

## 2. q-sensitive average

```lean
theorem sum_GNDepthMassAt_over_interval_le
```

は `q ∈ Q` について `q` が素数、`q ∤ p`、`q ∤ b` なら、

```text
∑ a ∈ Icc 0 X, GNDepthMassAt Q p b a
  ≤
∑ q ∈ Q,
  (p - 1) *
    ((X + 1) / (q - 1) + Nat.log q (p * (X+b)^p)) *
      log q.
```

Ultra-001L の `X+1` density ではなく、Ultra-001M の
`(X+1)/(q-1)` refinement を使用している。

## 3. Markov bad-set theorem

まず、

```lean
theorem card_GNDepthMassBadSet_le_sum
```

で正の `threshold` に対し、

```text
card(BadSet)
  ≤
(∑ a ∈ Icc 0 X, GNDepthMassAt Q p b a) / threshold
```

を証明した。続く、

```lean
theorem card_GNDepthMassBadSet_le
```

は average bound を代入し、

```text
card(BadSet)
  ≤
(∑ q ∈ Q,
  (p - 1) *
    ((X + 1)/(q - 1) + log_q(p(X+b)^p)) * log q)
  / threshold
```

という完全に明示的な有限評価を与える。

従って、

```text
bad points are sparse
```

は Lean theorem になった。

## 4. 境界

cardinality bound は、指定された ABC triple の coordinate が bad set の
外にあることを意味しない。次の未解決点は、

```text
structure-preserving finite probe/orbit
  → not every probe is bad
  → one good probe
  → transport its bound back to the target triple
```

という deterministic target-escape / compensation 原理である。`p` と最終
budget の定数を triple ごとに変えてはならない。

## Local verification

```text
lake build DkMath.ABC.GNDepthMassBadSet   success (8363 jobs)
lake build DkMath.ABC                     success (8383 jobs)
lake build DkMath                         success (8753 jobs)
representative axiom audit                propext / Classical.choice / Quot.sound only
new production code                      no sorry / axiom / native_decide
git diff --check                         clean
```

full build に表示される既存 research module の `sorry` warning は今回の
変更によるものではない。

push、PR 更新、CI 起動・確認は行っていない。
