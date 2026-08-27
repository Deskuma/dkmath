# Ultra-001F Report — Exact order and deep-lift boundary

Date: 2026-07-26  
Status: **local order packet complete / uniform exclusion unavailable**

## Exact order packet

Module:

```text
DkMath.ABC.GNPrimeSupportOrder
```

Theorems:

```lean
Triple.exists_gnRatioUnit_orderOf_eq_prime
Triple.prime_dvd_sub_one_of_mem_GNNonExceptionalSupport
Triple.mod_eq_one_of_mem_GNNonExceptionalSupport
```

素数指数 `p` と non-exceptional support prime `q` に対し、
`ZMod q` の unit:

```text
r = T.c / T.b
```

は:

```text
orderOf r = p
p ∣ q - 1
q % p = 1
```

を満たす。`hpOdd` と `0 < T.b` は不要である。

## Deep-lift lane の判定

exact order や primitive/fresh 性だけでは high lift を排除できない。
既存の kernel-clean tombstone:

```lean
DkMath.NumberTheory.GcdNext.noLift_GN_of_primitive_prime_factor_is_false
```

は:

```text
p = 3
T = (2, 3, 5)
q = 7
GN 3 2 3 = 49
```

を与える。ここで `q` は fresh、non-exceptional、`q ≡ 1 mod p` だが
`q^2 ∣ GN` である。

simple-root / Hensel uniqueness は root lift の一意性であって、任意深度への
lift の不存在ではない。従って local valuation cap をこの packet から導く
攻撃は停止する。

## Dependency audit

新規 order module は research theorem を import/use しない。代表 theorem の
axiom audit は:

```text
propext
Classical.choice
Quot.sound
```

のみである。
