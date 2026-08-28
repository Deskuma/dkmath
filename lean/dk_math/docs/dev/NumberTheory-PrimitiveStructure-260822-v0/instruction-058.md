# instruction-058 — PRIM-L043 Far-Triple Half-Scale Cofactor / Old-Support Return Lean Judgment

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- Lean / Mathlib: 現行 checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L042` は Outcome A として受理済み。

L042 では canonical residual triple

```text
(r,(q,s))
```

に canonical prime

```text
p := paritySafeCanonicalSupportPrime n r
```

を戻すことで

```text
p < q < s
p*q*s ∣ n^2+r
```

を得て、triple product modulus `m := p*q*s` を square-waveへ transportした。
さらに `m ≤ 2*n` / `2*n < m` の near/far split を構成し、far keyでは wave occupancy `≤ 1` を証明済み。

今回は **far triple の complementary cofactor** を取り出し、square-shell geometry が与える half-scale compression と old-support return を Lean に固定する。

これは `SquareOffsetsFullyCovered` の smaller-anchor reconstruction ではない。`descent` という語を使う場合も「cofactor scale descent / compression」に限定し、Legendre obstruction 自体が smaller anchor に降りるとは主張しない。

---

## 1. 新規 module

推奨:

```text
DkMath/NumberTheory/Legendre/ParitySafeTripleFarCofactor.lean
```

最低 import:

```lean
import DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate
```

必要なら Primitive / quotient support の既存 API を追加 import してよいが、既存定義を複製しないこと。

facade:

```text
DkMath/NumberTheory/Legendre.lean
```

へ import を追加する。

---

## 2. PRIM-L043.1 — canonical far-triple cofactor

canonical residual incidence

```lean
hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n
```

に対し

```lean
p := paritySafeCanonicalSupportPrime n r
m := p * q * s
```

とする。

far 仮定は、可能なら L042 の finite key membership をそのまま使う。

```lean
(p, (q, s)) ∈ paritySafeTripleGateFarTriples n
```

または同値な

```lean
2 * n < p * q * s
```

を使ってよい。

complementary cofactor を定義する。

```lean
def paritySafeFarTripleCofactor (n r q s : ℕ) : ℕ :=
  (n ^ 2 + r) /
    (paritySafeCanonicalSupportPrime n r * q * s)
```

名前・引数順は Lean 実装に合わせて調整可。

### 必須 exact factorization

far residual incidence について少なくとも次を閉じる。

```text
0 < t
m * t = n^2 + r
```

ここで `t` は上記 cofactor。

既存

```text
p*q*s ∣ n^2+r
```

を再利用し、手作業で因数分解を再証明しないこと。

---

## 3. PRIM-L043.2 — half-scale shell compression

L042 の shell bound

```text
n^2+r ≤ n^2+2*n = n*(n+2)
```

と far condition

```text
2*n < m
```

から、cofactor `t` に対し次を証明する。

主 theorem:

```text
2 * t < n + 2
```

可能ならさらに consumer-friendly な形を追加する。

```text
2 * t ≤ n + 1
```

および triple residual が存在することで十分大きい `n` を回収し、

```text
t < n
```

まで閉じる。

`n ≥ 7` 等の補助 bound が必要なら、`p < q < s` と active odd primes から導出してよい。

### 数学的意味

far triple obstruction は cofactor を anchor 未満、より強く概ね half-scale へ押し戻す。

```text
large triple product > shell width
        ↓
small complementary factor t
        ↓
2*t < n+2
```

これは L042 の `far wave ≤ 1` とは独立に useful な shell consequence である。

---

## 4. PRIM-L043.3 — reduced-residue inheritance

parity-safe complete point は

```text
Nat.Coprime (2*n) (n^2+r)
```

を持つ。

`n^2+r = m*t` から cofactor 側へ coprimality を移し、必ず

```text
Nat.Coprime (2*n) t
```

を証明する。

可能なら同時に

```text
Odd t
Nat.Coprime n t
```

も API として回収する。

ここで新しい解析的議論は不要。`Nat.coprime_mul_iff_right` 等の既存 elementary API を使う。

---

## 5. PRIM-L043.4 — every cofactor prime returns to the active old world

`t` の任意の prime divisor `u` に対して、far residual incidence のもとで次を証明する。

概念形:

```lean
Nat.Prime u → u ∣ t →
  u ∈ squareAnchorOddActivePrimes n ∧
  u ∈ paritySafeActiveSupport n r
```

必要な成分:

```text
u ≤ t < n
u ≠ 2
¬ u ∣ n
u ∣ n^2+r
```

を exact に回収する。

特に `u` は「新しい外部 prime」ではなく、同じ anchor の parity-safe active old-prime world へ戻る。

### Optional stronger packaging

既存 `PrimeScaleGeneratedBy` が自然に使えるなら、

```text
PrimeScaleGeneratedBy (squareAnchorOddActivePrimes n) t
```

に相当する theorem を追加してよい。

ただし型・predicate の都合で不自然なら、上記 universal prime-divisor theorem を正本とする。

---

## 6. PRIM-L043.5 — `t = 1` / `1 < t` exact split

far residual incidence について cofactor を二分する。

### Case A: terminal exact triple

```text
t = 1
```

なら

```text
n^2+r = p*q*s
```

を exact に返す theorem を用意する。

### Case B: nontrivial small cofactor

```text
1 < t
```

なら prime divisor theorem から

```text
∃ u, Nat.Prime u ∧ u ∣ t ∧
  u ∈ squareAnchorOddActivePrimes n ∧
  u ∈ paritySafeActiveSupport n r
```

を返す。

その `u` を `p,q,s` と比較して、次の **depth-or-new-direction closure** を形式化する。

望ましい theorem shape:

```text
p^2 ∣ n^2+r
∨ q^2 ∣ n^2+r
∨ s^2 ∣ n^2+r
∨ ∃ u,
    u ∈ squareAnchorOddActivePrimes n ∧
    u ≠ p ∧ u ≠ q ∧ u ≠ s ∧
    p*q*s*u ∣ n^2+r
```

完全にこの順序・結合である必要はない。

重要なのは、`1 < t` が

```text
existing triple direction repeats
    → prime-power depth
```

または

```text
new active direction appears
    → fourth distinct direction
```

へ exact に戻ること。

### 非目標

ここから fourth-direction hypergraph / k-tuple hierarchy を構築しない。

この theorem は **既存 direction/depth obstruction への return bridge** として止める。

---

## 7. PRIM-L043.6 — far cofactor is NOT an injective coordinate

cofactor cardinalityだけで far residual incidence を数えないこと。

次の concrete false beam を、実装負荷が過大でなければ Lean theorem として固定する。

```text
n = 25
r₁ = 2
r₂ = 38
```

complete points:

```text
25^2 + 2  = 627 = 3 * 11 * 19
25^2 + 38 = 663 = 3 * 13 * 17
```

両 seat は parity-safe candidate で、canonical prime は `3`。

conceptually:

```text
(r₁,(11,19)) ∈ residual triples
(r₂,(13,17)) ∈ residual triples
```

かつ両 product は far:

```text
50 < 3*11*19
50 < 3*13*17
```

そして両 cofactor は

```text
t₁ = 1
t₂ = 1
```

で一致する。

従って

```text
far residual incidence → small cofactor t
```

は一般に injective ではない。

この false beam が Lean 上で重すぎる場合、少なくとも report に arithmetic verification と「cofactor injection を主張しない」判断を明記する。

---

## 8. stronger-beam judgment

report では次を明示判定する。

1. far triple cofactor は universally `2*t < n+2` まで縮むか。
2. `Nat.Coprime (2*n) t` は exact に transfer できるか。
3. `t` の全 prime divisors は同じ parity-safe active world に戻るか。
4. `1<t` は depth-or-new-direction closure まで Lean で閉じるか。
5. cofactor は residual incidence の injective coordinate ではないことを確認できるか。
6. この checkpoint から smaller-anchor `SquareOffsetsFullyCovered t` や Legendre descent は得られたか。
   - 通常は **No** とする。
   - 実際に theorem が得られた場合のみ主張する。

---

## 9. Outcome 判定

### Outcome A — HALF-SCALE COFACTOR COMPRESSION / OLD-SUPPORT RETURN

以下が成立:

- exact factorization `m*t = n^2+r`
- half-scale bound `2*t < n+2`
- `Coprime (2*n) t`
- every prime divisor of `t` returns to active support
- `t=1` terminal triple / `1<t` depth-or-new-direction closure

### Outcome B — HALF-SCALE COFACTOR ONLY

factorization・half-scale・coprimalityまでは通るが、prime-divisor return / closure を clean に閉じられない。

### Outcome C — PROPOSED HALF-SCALE CLAIM FALSE

`2*t<n+2` 等に反例があれば最小反例を形式化して停止する。

---

## 10. report

作成:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-far-triple-half-scale-cofactor-260826.md
```

最低限:

- Outcome
- theorem surface
- half-scale derivation
- reduced-residue inheritance
- old-support return
- depth/new-direction closure
- false beam `(25,2)` / `(25,38)` の判定
- Legendre / full descent 未到達の境界

---

## 11. build / audit

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeTripleFarCofactor
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean source:

```text
sorry
admit
axiom
native_decide
```

禁止 placeholder と trailing whitespace を監査する。

full repository build は不要。

---

## 12. 非目標

- `LegendreConjecture` の証明
- smaller-anchor full-cover reconstruction
- generic infinite descent
- fourth / fifth / general k-direction hypergraph
- PNT / Mertens / Rosser--Schoenfeld / Jacobsthal / analytic sieve
- RH / CFBRC
- far cofactor map の injectivity

今回の狙いは、L042 の far triple を

```text
large product wave
    ↓
small complementary cofactor
    ↓
active old-world return
    ↓
depth or new direction
```

へ exact に閉じることだけである。
