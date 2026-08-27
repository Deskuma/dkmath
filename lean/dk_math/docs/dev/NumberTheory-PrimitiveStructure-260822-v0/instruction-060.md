# instruction-060 — PRIM-L045 Far-Triple Cofactor Prime-Support Complement / Local Ownership

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `ccd2421a17e6eb191183342fb141cd7e071421d1`
- Lean / Mathlib: 現行 checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L044` は **Outcome A — HALF-SCALE RETURN / DEPTH RECHARGE FRONTIER** として受理する。

L044 で得たもの:

```text
far residual triple (r,(q,s))
p := paritySafeCanonicalSupportPrime n r
t := paritySafeFarTripleCofactor n r q s

0 < t
p*q*s*t = n^2+r
t < n
Nat.Coprime (2*n) t

t ∈ squareAnchorCoprimeBaseOffsets n

Prime u ∧ u|t
  -> u ∈ paritySafeHalfScaleActivePrimes n
  -> u ∈ paritySafeActiveSupport n r
```

さらに `1<t` の場合、`p^2/q^2/s^2` の三 depth branch は L018 の実在 prime-square incidenceへ recharge 済みで、残りは fourth distinct half-scale direction witness である。

一方、`(62,41)` / `(62,83)` の arithmetic false beam により、cofactor `t` または一個の returned prime `u` を **global injective charge key** として扱うことはできない。

今回の目的は、この非単射を避けるために **cofactor の全 prime support** を有限集合として保持し、固定 seat / fixed canonical triple においてそれが「選択済み三方向を除いた残り support」を表すことを exact に証明することである。

generic fourth/fifth/k-direction hypergraph は作らない。

---

## 1. 数学的核

far packet では

```text
n^2+r = p*q*s*t
```

である。

`p,q,s` は distinct active old primes であり、L044 により `t` の任意の prime divisor も同じ active supportへ戻る。

従って cofactor の prime support

```text
PrimeSupp(t) := Nat.primeFactors t
```

を使えば、期待される exact support decomposition は

```text
paritySafeActiveSupport n r
  = insert p (insert q (insert s (Nat.primeFactors t)))
```

である。

これは depth が存在しても成立する。例えば `p|t` なら右辺で `p` が重複するだけで、Finset の `insert` が吸収する。

さらに三方向に depth が無い、すなわち

```text
¬ p^2 | n^2+r
¬ q^2 | n^2+r
¬ s^2 | n^2+r
```

なら `p,q,s` は `Nat.primeFactors t` に入れない。

したがってこの branch では

```text
(paritySafeActiveSupport n r).card
  = 3 + (Nat.primeFactors t).card
```

まで exact に落とせるはずである。

より強く、Lean bookkeeping が素直なら

```text
Nat.primeFactors t
  = (((paritySafeActiveSupport n r).erase p).erase q).erase s
```

または canonical quotient co-supportを使った同値な complement identity を狙う。

この complement identity が得られれば、L041 の residual pair `(q,s)` に対して、cofactor prime support は

```text
fixed support - {p,q,s}
```

そのものとなる。

これが今回の ownership core である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
```

ファイル:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarTripleCofactorSupport.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge
```

だけを試す。

`Nat.primeFactors` 用に追加 import が必要なら Mathlib の最小 import を追加してよい。既存 DkMath の無関係な ABC 層などは import しない。

facade:

```text
DkMath.NumberTheory.Legendre
```

へ新 module を import する。

---

## 3. 最小 theorem surface

### L045.1 cofactor prime support

必要なら total def を置く。

```lean
noncomputable def paritySafeFarTripleCofactorPrimeSupport
    (n r q s : ℕ) : Finset ℕ :=
  Nat.primeFactors (paritySafeFarTripleCofactor n r q s)
```

名称は既存 style に合わせて微調整可。

far packet 下で membership characterization を置く。

概念形:

```lean
theorem mem_paritySafeFarTripleCofactorPrimeSupport
    (hinc ...)
    (hfar ...) :
    u ∈ paritySafeFarTripleCofactorPrimeSupport n r q s ↔
      Nat.Prime u ∧ u ∣ paritySafeFarTripleCofactor n r q s := by
  ...
```

`Nat.mem_primeFactors` が `t ≠ 0` を含む形なら、L043 packet の `0<t` で消す。

### L045.2 full-support half-scale return

個別 `u` theorem の Finset 版を作る。

```lean
theorem paritySafeFarTripleCofactorPrimeSupport_subset_halfScale
    (hinc ...)
    (hfar ...) :
    paritySafeFarTripleCofactorPrimeSupport n r q s ⊆
      paritySafeHalfScaleActivePrimes n := by
  ...
```

同時に candidate support への subset も置く。

```lean
theorem paritySafeFarTripleCofactorPrimeSupport_subset_activeSupport
    (hinc ...)
    (hfar ...) :
    paritySafeFarTripleCofactorPrimeSupport n r q s ⊆
      paritySafeActiveSupport n r := by
  ...
```

これは L044 の prime-divisor return を pointwise に使えばよい。

### L045.3 exact active-support decomposition — 主定理

`p := paritySafeCanonicalSupportPrime n r` とする。

```lean
theorem paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport
    {n r q s : ℕ}
    (hinc : (r,(q,s)) ∈ paritySafeCanonicalResidualTripleIncidences n)
    (hfar : (paritySafeCanonicalSupportPrime n r,(q,s)) ∈
      paritySafeTripleGateFarTriples n) :
    paritySafeActiveSupport n r =
      insert (paritySafeCanonicalSupportPrime n r)
        (insert q
          (insert s
            (paritySafeFarTripleCofactorPrimeSupport n r q s))) := by
  ...
```

証明方針:

- `⊇`:
  - `p,q,s` は L041/L042 packet から active support membership。
  - cofactor prime support は L045.2 subset。
- `⊆`:
  - `u ∈ paritySafeActiveSupport n r` なら `u` は prime かつ `u | n^2+r`。
  - L043 factorization `p*q*s*t = n^2+r` を使う。
  - prime divisibility of product を分解して、`u=p ∨ u=q ∨ u=s ∨ u|t`。
  - 最後は `Nat.mem_primeFactors` へ戻す。

ここで `u≤n` を改めて証明する必要はない。active support membership 側から既に prime packet が得られる。

### L045.4 no-depth complement/cardinality

三方向 no-depth を仮定する。

```lean
(hpdepth : ¬ (paritySafeCanonicalSupportPrime n r)^2 ∣ n^2+r)
(hqdepth : ¬ q^2 ∣ n^2+r)
(hsdepth : ¬ s^2 ∣ n^2+r)
```

まず

```text
p ∉ cofactorPrimeSupport
q ∉ cofactorPrimeSupport
s ∉ cofactorPrimeSupport
```

を証明する。

理由: 例えば `p|t` なら `n^2+r=p*q*s*t` と distinctness から `p^2|n^2+r`。

この nonmembership と `p<q<s` を使い、少なくとも次の cardinal identity を閉じる。

```lean
theorem paritySafeActiveSupport_card_eq_three_add_cofactorPrimeSupport_card
    ... :
    (paritySafeActiveSupport n r).card =
      3 + (paritySafeFarTripleCofactorPrimeSupport n r q s).card := by
  ...
```

`Nat` 側の加算順は Lean が通りやすい形に変更可。

### L045.5 exact complement identity — strongly preferred

Finset bookkeeping が局所的に閉じるなら、今回の strongest beam として exact complement を追加する。

候補:

```lean
theorem paritySafeFarTripleCofactorPrimeSupport_eq_activeSupport_erase_three
    ... :
    paritySafeFarTripleCofactorPrimeSupport n r q s =
      (((paritySafeActiveSupport n r).erase
        (paritySafeCanonicalSupportPrime n r)).erase q).erase s := by
  ...
```

あるいは L041 の erased canonical quotient co-support `E` を使い、

```text
PrimeSupp(t) = (E.erase q).erase s
```

の方が自然ならそちらを採用してよい。

**重要:** exact complement が Lean bookkeeping のためだけに極端に重くなるなら、L045.4 cardinal identityまでで Outcome B として止める。generic combinatorics moduleを大きく増築しない。

---

## 4. local ownership / injectivity

exact complement identity が得られた場合だけ、次を試す。

固定 `n,r` と canonical `p` の下で、二つの no-depth far residual pair

```text
(q₁,s₁)
(q₂,s₂)
```

が同じ cofactor prime support を持つなら、canonical ordering `q<s` を利用して

```text
q₁=q₂ ∧ s₁=s₂
```

を示せるか確認する。

概念形:

```lean
theorem paritySafeFarTripleCofactorPrimeSupport_local_injective
    ...
    (hsupp :
      paritySafeFarTripleCofactorPrimeSupport n r q₁ s₁ =
      paritySafeFarTripleCofactorPrimeSupport n r q₂ s₂) :
    q₁ = q₂ ∧ s₁ = s₂ := by
  ...
```

これは **global injectivity ではない**。

key は実質

```text
(r, PrimeSupp(t))
```

であり、`r` を忘れてはならない。L044 false beam は異なる seats が同じ `t=7` / `u=7` を持つことを示しているため、prime support単独の global key化は禁止。

この local injectivity が 20〜30行程度の Finset 操作で閉じるなら採用する。

重い場合は今回は実装せず、report に「exact complement obtained; local injectivity is next direct consumer」と記録して停止する。

---

## 5. false beam / sanity checks

L044 の `(62,41)/(62,83)` false beam は維持する。

今回、新たな反例探索は必須ではない。

ただし次の誤読を防ぐ。

```text
same PrimeSupp(t)
  -> same residual pair
```

は **seat `r` を固定しない限り false の可能性が高い**。

L044 の二例ではどちらも `PrimeSupp(t)={7}` なので、global support-key injectivityを主張してはならない。

---

## 6. 禁止事項 / 非目標

今回は以下を行わない。

- fourth/fifth/k-direction hypergraph の新設
- cofactor value `t` 単独の global injectivity
- one returned prime `u` 単独の global injectivity
- cofactor prime support単独（seatを忘れたもの）の global injectivity
- smaller-anchor `SquareOffsetsFullyCovered t`
- induction / infinite descent
- residual mass の global cardinal contradiction
- PNT / analytic sieve / RH / Jacobsthal への逃避
- Legendre conjecture の証明宣言

---

## 7. Outcome 判定

### Outcome A — EXACT COFACTOR-SUPPORT COMPLEMENT / LOCAL OWNERSHIP

最低条件:

1. cofactor prime support Finset を定義または canonical に参照。
2. 全 prime support が half-scale active world / same candidate supportへ返る。
3. active support が `{p,q,s} ∪ PrimeSupp(t)` と exact に分解される。
4. no-depth branch で `support.card = 3 + PrimeSupp(t).card` が閉じる。
5. exact erase-complement identity、または同等の local ownership theoremが得られる。

local injectivityまで閉じれば **Outcome A+** と report してよい。

### Outcome B — EXACT SUPPORT DECOMPOSITION ONLY

3 と 4 までは閉じたが exact erase-complement / local injectivity が Finset bookkeeping 上重い場合。

これは失敗ではない。次 checkpoint を internal complement combinatorics の micro-layer に限定する。

### Outcome C — SUPPORT DECOMPOSITION FAILS

`paritySafeActiveSupport` に `p,q,s,t` factorizationで説明できない prime direction が残る、または current API では factorizationから active-support equalityへ戻れない場合。

この場合は無理に補題を追加せず、具体的な欠損 theorem / false beam を report して停止する。

---

## 8. 検証

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について:

```text
sorry
admit
axiom
native_decide
```

を監査する。

既存の repository-wide `sorry` は今回の判定対象外。

---

## 9. report

新規 report 候補:

```text
primitive-parity-safe-far-triple-cofactor-support-complement-260826.md
```

必須記録:

- Outcome A/A+/B/C
- exact support decomposition の成否
- no-depth cardinal identity の成否
- exact erase-complement の成否
- local injectivity の成否
- L044 false beamとの整合性
- smaller-anchor descent / global injectivityを主張していないこと

今回の狙いは、

```text
one returned prime u
  -> noninjective ownership
```

から

```text
entire cofactor prime support
  -> exact seat-local complement
  -> recoverable local ownership
```

へ進むことである。
