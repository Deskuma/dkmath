# PUU-L001 Finite Prime-Basis Reservation Escape

## Goal

新 branch の最初の checkpoint として、Legendre や unit-scale へ進む前に、有限 prime basis が全座席を予約できないことを exact finite theorem として Lean 固定する。

この checkpoint の数学的核は Euclid 型である。

```text
finite prime basis S
  ↓
M(S) := product S
  ↓
M(S)+1 is not divisible by any p ∈ S
  ↓
M(S)+1 has a prime divisor q
  ↓
q ∉ S
```

ここでは `Primorial` という名前を canonical first-primes product に限定して温存してよい。任意 finite prime set の product は `PrimeBasisProduct` などの名前で実装すること。

---

## 0. Recommended module

```text
DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape
```

recommended file:

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/FiniteReservationEscape.lean
```

必要なら facade:

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse.lean
```

を新設し import を追加する。

Mathlib の既存 Finset product / prime divisor API を優先して利用し、既存 DkMath Legendre module には依存しないこと。

---

# 1. Finite prime basis

最小限の predicate / product を定義する。

推奨形:

```lean
/-- Every member of `S` is prime. -/
def IsFinitePrimeBasis (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Nat.Prime p

/-- Product of a finite prime basis. -/
def finitePrimeBasisProduct (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p
```

命名は repository convention に合わせて調整可。

必要な basic packet:

```text
p ∈ S
→ p ∣ finitePrimeBasisProduct S
```

empty basis も許可してよい。その場合 product は `1`。

---

# 2. Reservation predicate

有限 basis による予約を明示する。

推奨:

```lean
/-- `n` is reserved by at least one prime scale from `S`. -/
def ReservedByPrimeBasis (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ S, p ∣ n
```

必要なら simp theorem:

```lean
reservedByPrimeBasis_iff
```

ここでは `n = 0` の一般論を深掘りしない。

---

# 3. Escape point

推奨:

```lean
def finitePrimeBasisEscapePoint (S : Finset ℕ) : ℕ :=
  finitePrimeBasisProduct S + 1
```

まず exact local exclusion:

```lean
theorem member_not_dvd_finitePrimeBasisEscapePoint
    {S : Finset ℕ} {p : ℕ}
    (hS : IsFinitePrimeBasis S)
    (hp : p ∈ S) :
    ¬ p ∣ finitePrimeBasisEscapePoint S
```

`hS` が不要なら theorem statement から落としてよい。ただし `p ≠ 1` を得るため prime hypothesis が必要なら basis predicate を利用する。

次に global form:

```lean
theorem finitePrimeBasisEscapePoint_not_reserved
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) :
    ¬ ReservedByPrimeBasis S (finitePrimeBasisEscapePoint S)
```

さらに:

```lean
theorem one_lt_finitePrimeBasisEscapePoint
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) :
    1 < finitePrimeBasisEscapePoint S
```

empty basis も含めて `1 < 1+1` なので成立するはず。

---

# 4. New prime divisor

`finitePrimeBasisEscapePoint S > 1` から prime divisor を取る。

必須 target:

```lean
theorem exists_new_prime_divisor_of_finitePrimeBasis
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ finitePrimeBasisEscapePoint S ∧
      q ∉ S
```

`q ∉ S` は、もし `q ∈ S` なら section 3 の exclusion に反することで閉じる。

この theorem が PUU-L001 の主定理。

---

# 5. No finite complete reservation

読みやすい consumer を追加する。

必須:

```lean
theorem finitePrimeBasis_not_globally_reserving
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) :
    ∃ n : ℕ,
      1 < n ∧
      ¬ ReservedByPrimeBasis S n
```

witness は escape point でよい。

さらに prime form:

```lean
theorem finitePrimeBasis_has_prime_outside
    (S : Finset ℕ)
    (hS : IsFinitePrimeBasis S) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∉ S
```

これは主定理から divisor 条件を落とすだけ。

**注意:** `Nat.infinite_setOf_prime` 等を使って証明しない。有限 basis から escape point を構成して証明すること。この branch の生成則として使うためである。

---

# 6. Basis-smooth / support containment interface

PowerSwap と unit-scale refinement への次 checkpoint の入口だけ用意する。

factorization data structure を大きく作らず、最小 predicate でよい。

推奨:

```lean
/-- Every prime divisor of `n` belongs to `S`. -/
def PrimeSupportContainedIn (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ n → q ∈ S
```

必須 false-beam theorem:

```lean
theorem newPrime_mul_not_primeSupportContainedIn
    {S : Finset ℕ} {q k : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hk : 0 < k) :
    ¬ PrimeSupportContainedIn S (q * k)
```

証明は `q ∣ q*k` を witness として直接閉じる。

これは後続で

```text
old basis only の scale refinement / PowerSwap fiber
```

が新 prime factor `q` を消せないことへ接続する最小 API である。

optional:

```lean
finitePrimeBasisEscapePoint_not_primeSupportContainedIn
```

を section 4 の `q` witness から導いてよい。

---

# 7. Arithmetic regressions

小さい concrete witnesses を 2–3 個だけ置いてよい。

例:

```text
S = {2,3}
product = 6
escape = 7
```

注意: この checkpoint では `5` を `2,3` basis の Euclid escape と呼ばない。`5` は primorial wheel `mod 6` の survivor seat であり、`M+1=7` の Euclid escape とは別概念である。この二つを混同しないこと。

この区別は後続の PrimorialWheel checkpoint で重要になる。

---

# 8. Documentation semantics

module docstring / report では次を明示する。

- `prime` はこの checkpoint では通常の `Nat.Prime`。
- Unit Universe 相対 primitive はまだ定義しない。
- finite reservation escape は「有限既知 prime scale だけでは全自然数 seat を予約できない」という finite theorem。
- `M(S)+1` は wheel の最小 survivor を主張するものではない。
- PowerSwap bridge はまだ行わない。
- Legendre / square shell は一切使わない。

---

# 9. Report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-finite-reservation-escape-260827.md
```

記録するもの:

1. 定義した basis / reservation / escape / support predicate
2. `M+1` exclusion
3. new prime divisor theorem
4. finite global reservation impossibility
5. `q*k` support-persistence false beam
6. 次 checkpoint への接続

---

# 10. Non-goals

PUU-L001 では以下をしない。

- `UnitUniverse` の実数定義
- `u₁,u₂` common lattice
- `3u₁ = 15u₂` の relative composite witness
- PowerSwap import / bridge
- canonical primorial `2*3*5*...`
- reduced residue wheel
- reflection / fractal / lift
- square anchor
- Legendre
- analytic prime counting

---

# Outcome rubric

## A+

以下がすべて閉じる:

- finite prime basis product
- reservation predicate
- exact `M+1` non-reservation
- prime divisor `q ∉ S`
- finite global reservation impossibility
- `PrimeSupportContainedIn`
- `q ∉ S → q*k` cannot be supported only by `S`
- facade / report

## A

主定理 `exists_new_prime_divisor_of_finitePrimeBasis` まで閉じ、support-containment interface のみ engineering が残る。

## B

`M+1` non-reservation まで。

## E

Mathlib / Nat product / divisibility engineering blocker。

## C

数学的 statement mismatch。

---

# STOP

PUU-L001 では **Finite Reservation Escape** までで停止する。

次 checkpoint で初めて、正の unit `u₁,u₂` と同一 absolute point の異なる integer coordinate を定義し、

```text
prime coordinate in one universe
composite coordinate in another universe
```

を Lean に固定する。
