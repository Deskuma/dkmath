# instruction-069 — PRIM-L054 Exact Recharge Dual-Base / Reverse Reconstruction

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `2055c97207e63e25fcba9fb80e638b5d27f4b31a`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L053` は **Outcome A+ — ODD-SHELL PRIME CAPACITY** として受理する。

L053 までで recharge surviving key

```text
key := (p,(q,s))
b   := p*q
t   := paritySafeFarProductWaveNextQuotient n key
```

について、

```text
key ↦ (b,t)
```

は injective であり、さらに

```text
s = paritySafeRechargeOddShellQuotient n b t
```

まで third prime が算術関数へ消去された。

現在は

```text
Recharge.card ≤ PrimeAdmissibleDualBasePairs.card
```

という upper-capacity theorem である。

しかし L053 の `PrimeAdmissibleDualBasePairs` は意図的に次を捨てている。

```text
b = p*q という ordered active-prime pair witness
p < q < s
canonical-minimum roughness:
  a < p, a active → a ∤ t
```

今回の bounded target は、この三情報を `(b,t)` 座標へ戻し、
**prime-admissible upper universe を actual recharge image そのものへ exact に sharpen すること**である。

解析的 counting、sieve、descent へは進まない。

---

## 1. 数学的核

L053 で

```text
s := OddShellQuotient(n,b,t)
```

は固定済みである。

そこで `(b,t)` が actual recharge coordinate になるために残る有限条件は、
概念的に次だけである。

```text
1. (b,t) は L053 prime-admissible
2. b = p*q
3. p は triple-gate prime
4. q は active prime
5. p < q < s
6. t は p より小さい active prime では割れない
```

ここで `s` は自由変数ではなく selector である。

この条件から key `(p,(q,s))` を作る。

L053 prime-admissible から既に

```text
n^2 < (b*t)*s ≤ n^2 + 2*n
2*n < b*s
b,t ∈ paritySafeFarCofactorBaseOffsets n
```

がある。

`b=p*q` を代入すると

```text
n^2 < (p*q*s)*t ≤ n^2 + 2*n
2*n < p*q*s
```

となる。

far modulus `m=p*q*s` は shell width `2*n` より大きいので、この shell hit の quotient は一意であり、

```text
t = n^2 / m + 1
  = paritySafeFarProductWaveNextQuotient n (p,(q,s)).
```

従って、

- shell upper → `ParitySafeFarProductKeyFitsShell`
- `t ∈ base` → `Coprime (2*n) t`
- rough witness → canonical-minimum exclusion

をそのまま `ParitySafeFarProductKeySurvives` へ戻せる。

さらに `n < b*t` と `b ≤ n` より `1 < t` なので、構成した key は recharge key である。

したがって今回狙う strongest statement は

```text
RechargeDualBaseImage = ExactRechargeDualBasePairs
```

という Finset equality である。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeExactDualBase.lean
```

最初は

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector
```

だけを試す。

完成後 facade

```text
DkMath.NumberTheory.Legendre
```

へ import を追加する。

---

## 3. L054.1 — exact pair witness

薄い Prop を置く。

```lean
/-- Ordered-prime and roughness witness carried by an exact recharge coordinate. -/
def ParitySafeRechargeExactPairWitness
    (n b t p q : ℕ) : Prop :=
  p ∈ paritySafeTripleGatePrimes n ∧
  q ∈ squareAnchorOddActivePrimes n ∧
  p < q ∧
  p * q = b ∧
  q < paritySafeRechargeOddShellQuotient n b t ∧
  ∀ a ∈ squareAnchorOddActivePrimes n,
    a < p →
      ¬ a ∣ t
```

association は Lean が扱いやすい形へ変更してよい。

この witness は generic semiprime API ではない。L054 の recharge coordinate 専用とする。

---

## 4. L054.2 — exact dual-base Finset

L053 universe を filter する。

```lean
noncomputable def paritySafeRechargeExactDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargePrimeAdmissibleDualBasePairs n).filter
    (fun bt =>
      ∃ p q,
        ParitySafeRechargeExactPairWitness n bt.1 bt.2 p q)
```

membership theorem:

```lean
@[simp] theorem mem_paritySafeRechargeExactDualBasePairs
    {n b t : ℕ} :
    (b,t) ∈ paritySafeRechargeExactDualBasePairs n ↔
      (b,t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ∧
      ∃ p q,
        ParitySafeRechargeExactPairWitness n b t p q := by
  ...
```

必須 refinement:

```lean
theorem paritySafeRechargeExactDualBasePairs_subset_primeAdmissible
    (n : ℕ) :
    paritySafeRechargeExactDualBasePairs n ⊆
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  ...
```

card inequality は安ければ追加してよい。

---

## 5. L054.3 — far shell quotient を `t` に戻す局所補題

reverse reconstruction で唯一 arithmetic が必要な箇所である。

推奨 theorem:

```lean
private theorem paritySafeRecharge_nextQuotient_eq_of_far_shell
    {n p q s t : ℕ}
    (hfar : (p,(q,s)) ∈ paritySafeTripleGateFarTriples n)
    (hshell :
      n ^ 2 < (p*q*s) * t ∧
      (p*q*s) * t ≤ n ^ 2 + 2*n) :
    paritySafeFarProductWaveNextQuotient n (p,(q,s)) = t := by
  ...
```

数学:

```text
m := p*q*s
2*n < m
n^2 < m*t ≤ n^2+2*n < n^2+m
```

従って

```text
t = n^2/m + 1.
```

L049 の private arithmetic helper と同じ核でよい。private なので、必要なら今回だけ数行で再構成する。

repo-wide Nat division lemma へ一般化しない。

別 route として、

```text
r := m*t - n^2
```

を `squareWaveOffsets` へ入れ、L049 の `paritySafeFarProductWaveCofactor_eq_nextQuotient` を使ってもよい。

Lean が短い方を採用する。

---

## 6. L054.4 — actual recharge image → exact pair

必須 key-level theorem:

```lean
theorem paritySafeRechargeDualBaseKey_mem_exact
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeExactDualBasePairs n := by
  ...
```

`key=(p,(q,s))` とする。

使うもの:

- L053 `paritySafeRechargeDualBaseKey_mem_primeAdmissible`
- far gate packet から
  - `p ∈ paritySafeTripleGatePrimes n`
  - `q ∈ squareAnchorOddActivePrimes n`
  - `p < q < s`
- L053 `thirdPrime_eq_oddShellQuotient`
- survival predicate の roughness
- `b=p*q` は definitionally true

これで exact witness を構成する。

続けて image subset:

```lean
theorem paritySafeRechargeDualBaseImage_subset_exact
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargeExactDualBasePairs n := by
  ...
```

---

## 7. L054.5 — exact pair → recharge key reverse reconstruction

今回の主定理。

推奨 statement:

```lean
theorem mem_paritySafeRechargeExactDualBasePairs_iff_exists_recharge_key
    {n b t : ℕ} :
    (b,t) ∈ paritySafeRechargeExactDualBasePairs n ↔
      ∃ key ∈ paritySafeRechargeSurvivingFarProductKeys n,
        paritySafeRechargeDualBaseKey n key = (b,t) := by
  ...
```

forward direction が新規 reverse reconstruction。

### 推奨 proof spine

`(b,t) ∈ exact` から:

1. `prime-admissible` packet を展開。
2. witness `p,q` を取得。
3. `s := paritySafeRechargeOddShellQuotient n b t` と置く。
4. witness と prime-admissible から

   ```text
   p ∈ tripleGatePrimes
   q ∈ active
   s ∈ active
   p < q < s
   ```

   を得て `paritySafeTripleGateTriples` membership。
5. prime-admissible の `2*n < b*s` と `p*q=b` から far membership。
6. shell packet を `p*q=b` で rewrite。
7. L054.3 で

   ```text
   nextQuotient n (p,(q,s)) = t
   ```

   を得る。
8. `ParitySafeFarProductKeySurvives` を構成:
   - fit: shell upper + quotient equality
   - coprime: `t ∈ paritySafeFarCofactorBaseOffsets n`
   - roughness: exact witness
9. `mem_paritySafeSurvivingFarProductKeys`。
10. recharge を示す。

    `prime-admissible` の over-anchor packet から

    ```text
    b ≤ n
    n < b*t
    ```

    があるため `t=1` は不可能。base positivity と合わせて `1<t`。
11. `mem_paritySafeRechargeSurvivingFarProductKeys`。
12. dual key equality:

    ```text
    (p*q, nextQuotient) = (b,t)
    ```

    を `p*q=b` と L054.3 で閉じる。

reverse direction は L054.4 と `Finset.mem_image` 相当の既存情報で短く閉じる。

### 重要

ここで candidate pair から **任意の key** を作るのではない。
exact witness が与える ordered `(p,q)` と selector `s` を使う。

---

## 8. L054.6 — image exact equality

strongest mandatory theorem:

```lean
theorem paritySafeRechargeDualBaseImage_eq_exactDualBasePairs
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n =
      paritySafeRechargeExactDualBasePairs n := by
  ...
```

`ext (b,t)` で、

```text
image membership
↔ ∃ recharge key, dualKey = (b,t)
↔ exact membership
```

を使う。

これが今回の主成果である。

L052/L053 は upper capacity だったが、L054 では actual recharge image の exact arithmetic description になる。

---

## 9. L054.7 — exact cardinality

image card = recharge card は L052 にあるので、L054.6 から

```lean
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_exactDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      (paritySafeRechargeExactDualBasePairs n).card := by
  ...
```

を必須とする。

向きは逆でもよいが、public API として上の向きを推奨する。

さらに L050 exact split と合成し、

```lean
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_exactDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDualBasePairs n).card := by
  ...
```

を mandatory とする。

これは今回、upper bound ではなく **exact global rearrangement** である。

---

## 10. arithmetic boundary witnesses

L053 prime-admissible universe がまだ actual image より広い理由を、小さい数値例で固定してよい。

### witness A — pair-product structure が不足

```text
n=8, b=5, t=3
selector=5
```

`b=5` は単一 prime であり、ordered distinct prime pair `p<q`, `p*q=b` を持たない。

Finset membership 全展開が重ければ、数値 selector と factor shape のみでよい。

### witness B — order `q<s` が不足

```text
n=17
b=15=3*5
t=7
selector=3
```

pair-product 自体はあるが、`q=5 < s=3` が失敗する。

### witness C — roughness が不足

```text
n=44
b=35=5*7
t=3
selector=19
```

ここでは ordered pair と `q<s` は成立するが、smaller active prime `3<5` が `t=3` を割る。

最低一つでよい。A+ を狙うなら B または C まで固定すると境界が明瞭。

---

## 11. strongest interpretation

L053:

```text
Recharge
  ↪ PrimeAdmissibleDualBasePairs
```

L054:

```text
Recharge
  ≃ ExactRechargeDualBasePairs
```

cardinality の意味では、

```text
Recharge.card = ExactRechargeDualBasePairs.card
```

まで戻る。

つまり recharge key の全自由度

```text
(p,q,s,t)
```

は、最終的に

```text
(b,t)
```

へ圧縮されたまま、失った情報を exact finite predicates として復元できる。

この checkpoint が閉じれば、次に数えるべき対象は upper universe ではなく、
**actual recharge image と同値な exact arithmetic pair universe** になる。

---

## 12. 禁止事項 / 非目標

今回は以下を行わない。

- generic semiprime / least-prime-factor library の構築
- exact pair universe の closed-form cardinality
- `base.card ^ 2` coarse bound を主成果にする
- prime counting / PNT / Mertens / Brun / Selberg sieve
- asymptotic density
- terminal branch の新しい counting
- smaller anchor / descent / induction
- `gcd b t = 1`, `b=t`, `b<t`, `t<b` の無根拠な主張
- `p ∤ t`, `q ∤ t`
- `t` の primality / squarefreeness
- global contradiction
- Legendre conjecture / RH proof claim

reverse reconstruction は **recharge exact coordinate に限定**する。

---

## 13. Outcome 判定

### Outcome A+ — EXACT RECHARGE DUAL-BASE

1. exact witness Prop
2. exact dual-base Finset + membership
3. local far-shell quotient recovery
4. actual dual key ∈ exact pairs
5. exact pair → recharge key reverse reconstruction
6. dual-base image = exact pairs
7. recharge card = exact-pair card
8. far residual = terminal + exact-pair card
9. refinement relation to L053
10. arithmetic boundary witness

### Outcome A — EXACT IMAGE

1–8 を完成。
refinement/card relationまたは boundary witness の一部のみ省略。

### Outcome B — REVERSE RECONSTRUCTION ONLY

exact pair から recharge key は復元できるが、Finset equality / card transport が Lean surface 上 disproportionate。
その場合は reverse theorem を公開して report し停止する。

### Outcome C — FALSE

上記 exact predicate を満たす `(b,t)` から recharge key を復元できない具体的 counterexample が出た場合。

その場合は、欠けている条件を witness とともに report し、predicate を勝手に弱めず停止する。

---

## 14. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeExactDualBase
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

---

## 15. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-exact-dual-base-260826.md
```

最低限:

1. Outcome
2. exact witness / exact Finset
3. quotient recovery proof spine
4. reverse reconstruction
5. image equality
6. exact cardinality / global decomposition
7. boundary witness
8. 非目標
9. validation

を記録する。
