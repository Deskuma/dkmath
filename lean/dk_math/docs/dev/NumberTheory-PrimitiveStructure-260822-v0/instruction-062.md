# instruction-062 — PRIM-L047 Far Product-Wave Exact Selector / Reduced Cofactor + Canonical Minimum

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `dd35fdd5a48d83fcf269d65930b7b024171cbfd9`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L046` は **Outcome A+ — ACTUAL NEAR/FAR SPLIT / LOCAL COFACTOR-WAVE BUDGET** として受理する。

L046 までで、actual far residual incidence

```text
(r,(q,s))
p := paritySafeCanonicalSupportPrime n r
m := p*q*s
t := paritySafeFarTripleCofactor n r q s
```

について

```text
m > 2*n
m*t = n^2+r
0 < t
2*t < n+2
t < n
Nat.Coprime (2*n) t
```

があり、さらに

```text
(r,(q,s)) ↦ (t,r)
```

は injective で、far residual card は finite cofactor-wave budget 以下となった。

一方 L042 には product-side upper incidence

```text
(key,r)
key = (p,(q,s))
r ∈ squareWaveOffsets n (p*q*s)
```

が既にあるが、これは **upper universe** であり、実際の canonical residual incidence ではない wave hit も含む。

今回の目的は、L046 の cofactor information を L042 product-wave sideへ戻し、actual far residual incidence を product-wave hit 上の **exact finite selector** として同定することである。

新しい generic sieve / hypergraph は作らない。

---

## 1. 数学的核

far triple gate key

```text
key = (p,(q,s))
m = p*q*s
```

は三つの distinct active odd primes からなるので

```text
Nat.Coprime (2*n) m
```

である。

さらに wave hit

```text
r ∈ squareWaveOffsets n m
```

なら

```text
m | n^2+r
```

であり、quotient

```text
t := (n^2+r) / m
```

を取れば

```text
m*t = n^2+r
```

である。

far 条件 `2*n < m` と shell width `1 ≤ r ≤ 2*n` から、この **任意の far product-wave hit** に対して

```text
0 < t
2*t < n+2
```

まで従う。これは actual residual incidence に限定しない product-wave arithmetic である。

そして `m` 自身が `2*n` と coprime なので、

```text
Nat.Coprime (2*n) (n^2+r)
  ↔ Nat.Coprime (2*n) t
```

である。

L037 の reduced-residue characterization と合わせると、far product-wave hit 上では

```text
r ∈ squareAnchorOddPointCoprimeOffsets n
  ↔ Nat.Coprime (2*n) t
```

となるはずである。

これが **reduced cofactor selector**。

残る actual-residual 条件は canonical ownership である。

key の `p` が

```text
p = paritySafeCanonicalSupportPrime n r
```

なら、wave factorization `p*q*s | n^2+r` と key packet の active/distinctness から

```text
q,s ∈ erased canonical quotient co-support
```

へ戻せるはずである。

従って far key / wave hit の下で

```text
Nat.Coprime (2*n) t
p = paritySafeCanonicalSupportPrime n r
```

を課せば、

```text
(r,(q,s)) ∈ paritySafeCanonicalFarResidualTripleIncidences n
```

が復元できることを狙う。

つまり今回の strongest beam は

```text
actual far residual incidence
  ↔ far product-wave hit
       + reduced cofactor quotient
       + canonical-minimum ownership
```

である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeFarProductWaveSelector.lean
```

import はまず

```lean
import DkMath.NumberTheory.Legendre.ParitySafeFarCofactorWave
```

だけを使う。

facade `DkMath.NumberTheory.Legendre` へ import する。

---

## 3. L047.1 far product-wave quotient

far product key と seat から quotient を取る local def を置く。

候補:

```lean
def paritySafeFarProductWaveCofactor
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) (r : ℕ) : ℕ :=
  (n ^ 2 + r) / paritySafeTripleProductModulus key
```

名称は既存 style に合わせて微調整可。

far key + wave hit packet を証明する。

概念形:

```lean
theorem paritySafeFarProductWaveCofactor_packet
    {n p q s r : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p*q*s)) :
    let t := paritySafeFarProductWaveCofactor n (p,(q,s)) r
    0 < t ∧
      p*q*s*t = n^2+r ∧
      2*t < n+2 := by
  ...
```

`m > 2*n`、`r ≤ 2*n`、`m*t = point` を使う。

必要なら `n>0` は far key の active-prime packetから得る。

---

## 4. L047.2 product modulus is reduced

far key の product modulus自体が reduced unit であることを theorem 化する。

```lean
theorem paritySafeTripleGateFarProductModulus_coprime_two_mul
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n) :
    Nat.Coprime (2*n) (p*q*s) := by
  ...
```

既存 `activePrime_reducedResidue_packet` と `Nat.coprime_mul_iff_*` を使う。

この theorem は far に限らず triple gate 全体で言えるなら、より自然な名称で gate theorem にしてよい。ただし今回 module 内で閉じ、無関係な refactor はしない。

---

## 5. L047.3 reduced-cofactor ↔ parity-safe seat — 第一主定理

far key + wave hit の下で quotient `t` を使い、

```lean
theorem paritySafeFarProductWave_mem_candidate_iff_cofactor_coprime
    {n p q s r : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hr : r ∈ squareWaveOffsets n (p*q*s)) :
    r ∈ squareAnchorOddPointCoprimeOffsets n ↔
      Nat.Coprime (2*n)
        (paritySafeFarProductWaveCofactor n (p,(q,s)) r) := by
  ...
```

証明の核:

1. wave hit から `m*t = n^2+r`。
2. key から `Coprime (2*n) m`。
3. よって `Coprime (2*n) (m*t) ↔ Coprime (2*n) t`。
4. `m*t = point` で rewrite。
5. L037

   ```text
   mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue
   ```

   へ接続する。

これは今回必須。

---

## 6. L047.4 selected far product-wave offsets

keyごとの exact selector Finset を定義する。

候補:

```lean
noncomputable def paritySafeCanonicalFarProductWaveOffsets
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : Finset ℕ :=
  (squareWaveOffsets n (paritySafeTripleProductModulus key)).filter
    (fun r =>
      Nat.Coprime (2*n)
        (paritySafeFarProductWaveCofactor n key r) ∧
      key.1 = paritySafeCanonicalSupportPrime n r)
```

far key 以外に対しても total Finset でよい。

membership simp theoremを置く。

**重要:** candidate membershipを重ねて filter しない。L047.3 により reduced-cofactor 条件と同値なので、selector の意味を二重化しない。

---

## 7. L047.5 selector → actual residual incidence — 最重要 reverse theorem

far key `(p,(q,s))` と

```text
r ∈ paritySafeCanonicalFarProductWaveOffsets n (p,(q,s))
```

から

```text
(r,(q,s)) ∈ paritySafeCanonicalFarResidualTripleIncidences n
```

を復元する。

必要な流れ:

1. selector membershipから wave hit, quotient coprime, `p = canonicalPrime n r`。
2. L047.3 で `r` は parity-safe candidate。
3. key packetから `p,q,s` は active odd primes、`p<q<s`。
4. wave hitから `p*q*s | n^2+r`。
5. よって各 `p,q,s | point`。
6. candidate + divisibility から `p,q,s ∈ paritySafeActiveSupport n r`。
7. canonical equalityで `p` は selected support prime。
8. factorization / quotient APIを使い、distinct `q,s` が

   ```text
   (squareQuotientAnchorNondivisorSupport n p r).erase p
   ```

   に入ることを示す。
9. `q<s` と合わせて `paritySafeCanonicalResidualTripleIncidences` membershipを構成。
10. hkey の far membershipを付けて actual far residual membershipへ。

既存 theorem があれば必ず再利用する。q/s の quotient divisibilityのためだけに generic factorization libraryを増築しない。

もし reverse directionで不足 lemma が一つだけ明確なら、local private lemmaとして切ってよい。

---

## 8. L047.6 actual residual → selector — forward theorem

こちらは軽いはずである。

```lean
theorem paritySafeCanonicalFarResidual_mem_productWaveSelector
    {n r q s : ℕ}
    (hfar : (r,(q,s)) ∈ paritySafeCanonicalFarResidualTripleIncidences n) :
    r ∈ paritySafeCanonicalFarProductWaveOffsets n
      (paritySafeCanonicalSupportPrime n r,(q,s)) := by
  ...
```

使うもの:

- L046 actual far membership packet
- L042 product-wave membership
- L043/L046 cofactor factorization
- product-wave quotient = L043 far cofactor の equality
- L043 `Nat.Coprime (2*n) t`
- canonical equality `rfl`

product-wave quotient と `paritySafeFarTripleCofactor` の equality を local theoremとして先に置くとよい。

概念形:

```lean
theorem paritySafeFarProductWaveCofactor_eq_farTripleCofactor
    ... :
    paritySafeFarProductWaveCofactor n
      (paritySafeCanonicalSupportPrime n r,(q,s)) r =
    paritySafeFarTripleCofactor n r q s := by
  ...
```

---

## 9. L047.7 exact incidence model / exact cardinal sum — strongest beam

selected product-wave incidence setを置く。

```lean
noncomputable def paritySafeCanonicalFarProductWaveIncidences
    (n : ℕ) : Finset ((ℕ × (ℕ × ℕ)) × ℕ) :=
  (paritySafeTripleGateFarTriples n).product (squareOffsets n) |>.filter
    (fun hit => hit.2 ∈ paritySafeCanonicalFarProductWaveOffsets n hit.1)
```

`squareOffsets` は selector wave membershipから従うので、proof が楽なら product universeとして残してよい。

actual far residual incidenceとの map

```text
(r,(q,s)) ↦ ((canonicalPrime n r,(q,s)),r)
```

について、L047.5/L047.6 を使って **image equality または Finset.card_bij** を閉じる。

目標:

```lean
theorem paritySafeCanonicalFarProductWaveIncidences_card_eq_farResidual
    (n : ℕ) :
    (paritySafeCanonicalFarProductWaveIncidences n).card =
      (paritySafeCanonicalFarResidualTripleIncidences n).card := by
  ...
```

さらに key fiber の sumへ exact に展開する。

```lean
theorem paritySafeCanonicalFarResidual_card_eq_productWaveSelector_sum
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      ∑ key ∈ paritySafeTripleGateFarTriples n,
        (paritySafeCanonicalFarProductWaveOffsets n key).card := by
  ...
```

これが今回の strongest target。

L042 の far wave card ≤ 1 の subset として

```lean
theorem paritySafeCanonicalFarProductWaveOffsets_card_le_one
    {n key} (hkey : key ∈ paritySafeTripleGateFarTriples n) :
    (paritySafeCanonicalFarProductWaveOffsets n key).card ≤ 1 := by
  ...
```

も数行なら追加する。

---

## 10. canonical-minimum exclusion form — optional A+

selector の canonical equalityを、より arithmetic な「smaller active wave を全部避ける」形へ rewrite できるか確認する。

概念:

```text
p = canonicalSupportPrime n r
↔
p ∈ activeSupport n r
  ∧ ∀ a ∈ squareAnchorOddActivePrimes n, a < p → a ∉ activeSupport n r
```

product wave hitにより `p ∈ activeSupport` は既に供給できる。

従って selector が

```text
product wave hit
+ reduced cofactor
+ no smaller active divisor hit
```

という有限 exclusion conditionへ落ちれば、**Outcome A+** とする。

ただしこの equivalence のために min' API bookkeeping が大きくなるなら今回は実装しない。generic sieve moduleは作らない。

---

## 11. 今回の意味

L042 では

```text
actual residual incidence
  -> product-wave upper incidence
```

だった。

L046 で cofactor `t` の reduced same-anchor return が得られたため、今回

```text
actual far residual incidence
  <-> far product-wave hit
       + quotient t is reduced mod 2*n
       + p is the actual canonical minimum at the hit seat
```

へ exact 化する。

これは新しい解析的 sieve ではない。
既存 finite wave upper universe の **不要 hit を exact ownership 条件で除く**だけである。

---

## 12. 禁止事項 / 非目標

今回は以下を行わない。

- harmonic / `O(n log n)` evaluation
- PNT / Mertens / Rosser / Jacobsthal / analytic sieve / RH
- generic fourth/fifth/k-direction hypergraph
- smaller-anchor `SquareOffsetsFullyCovered t`
- induction / infinite descent
- global contradiction / Legendre proof declaration
- repository-wide factorization refactor
- selector cardinal の closed-form prime-count estimate

---

## 13. Outcome 判定

### Outcome A+ — EXACT FAR PRODUCT-WAVE SELECTOR / CANONICAL EXCLUSION

最低条件:

1. far product-wave quotient packet。
2. `candidate ↔ quotient coprime (2*n)`。
3. selector Finset。
4. selector → actual far residual reverse theorem。
5. actual far residual → selector forward theorem。
6. selected product-wave incidence card = actual far residual card。
7. exact key-fiber sum。
8. optional canonical-minimum exclusion formまで閉じた。

### Outcome A — EXACT FAR PRODUCT-WAVE SELECTOR

1〜7 が閉じ、8 は未実装。

### Outcome B — REDUCED SELECTOR UPPER FRONTIER

`candidate ↔ quotient coprime` と actual → selector は閉じたが、selector → actual の quotient-co-support reconstruction が current API 不足で閉じない。

この場合は不足 theorem を一つ特定し、そこで止める。generic workaroundを増築しない。

### Outcome C — SELECTOR FALSE

reduced quotient + canonical equalityだけでは actual residual incidenceを復元できない具体的 counterexample / missing mathematical condition が見つかった場合。

その条件を false beam として report し、定義を膨らませず停止する。

---

## 14. 検証

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について

```text
sorry
admit
axiom
native_decide
```

を監査する。

既存 repository-wide placeholder は今回の判定対象外。

---

## 15. report

新規 report候補:

```text
primitive-parity-safe-far-product-wave-exact-selector-260826.md
```

必須記録:

- Outcome A+/A/B/C
- reduced-cofactor ↔ parity-safe candidate の exact theorem
- reverse reconstruction が成立したか
- actual far residual card と selected product-wave card の関係
- exact fiber sum が閉じたか
- canonical-minimum exclusion formの成否
- stronger theoremが失敗した場合は不足条件 / false beam
- non-goals を越えていないこと
