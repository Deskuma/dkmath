# instruction-067 — PRIM-L052 Recharge Dual-Base Injection / Over-Anchor Capacity

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `1eeb09f222c07616ae8f05d4c6b96580c6b1dee4`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L051` は **Outcome A — PAIR-PRODUCT RETURN / EXACT FIBER** として受理する。

L051 までで recharge surviving key

```text
key := (p,(q,s))
b   := p*q
t   := paritySafeFarProductWaveNextQuotient n key
```

について、

```text
b ∈ paritySafeFarCofactorBaseOffsets n
t ∈ paritySafeFarCofactorBaseOffsets n
p < q < s
n^2 < b*s*t ≤ n^2 + 2*n
```

という dual reduced-base return が得られた。

今回の bounded target は、この二座標 `(b,t)` が recharge key 全体を一意に決定することを証明し、recharge cardinality を有限な over-anchor dual-base pair universe へ単射することだけである。

---

## 1. 数学的核 A — dual product は anchor を越える

recharge key では `s` は active prime なので `s ≤ n`。
一方、shell point は

```text
n^2 < b*s*t.
```

もし

```text
b*t ≤ n
```

なら

```text
b*s*t = (b*t)*s ≤ n*n = n^2
```

となり矛盾する。

従って mandatory theorem:

```lean
theorem paritySafeRechargeSurvivingFarProductKey_anchor_lt_pairProduct_mul_nextQuotient
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    n < (p*q) * paritySafeFarProductWaveNextQuotient n (p,(q,s)) := by
  ...
```

必要なら先に shell packet を切ってよい。

```lean
theorem paritySafeRechargeSurvivingFarProductKey_dualProduct_shell_packet
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    n ^ 2 <
        ((p*q) * paritySafeFarProductWaveNextQuotient n (p,(q,s))) * s ∧
      ((p*q) * paritySafeFarProductWaveNextQuotient n (p,(q,s))) * s ≤
        n ^ 2 + 2*n := by
  ...
```

既存 next-seat / cofactor packet / shell-fit を再利用し、generic division theory は増やさない。

---

## 2. 数学的核 B — same `(b,t)` なら `s` は一意

二つの recharge key が同じ pair-product `b` と next quotient `t` を持つとする。

各 third prime は active odd prime なので、`s₁ ≠ s₂` なら大小を入れ替えて

```text
s₁ + 2 ≤ s₂
```

とできる。

また section 1 より

```text
n < b*t
```

なので

```text
2*n < 2*(b*t).
```

両 key の shell packet は

```text
n^2 < (b*t)*sᵢ ≤ n^2 + 2*n.
```

`s₁ + 2 ≤ s₂` なら

```text
(b*t)*s₁ + 2*(b*t) ≤ (b*t)*s₂,
```

左辺は shell 上端を越えるため矛盾する。

したがって fixed `(b,t)` では third prime `s` は一意。

private helper でも public theorem でもよいが、最終 injection から再利用しやすい形を優先する。

候補:

```lean
theorem paritySafeRecharge_thirdPrime_eq_of_pairProduct_eq_of_nextQuotient_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁,(q₁,s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (h₂ : (p₂,(q₂,s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hb : p₁*q₁ = p₂*q₂)
    (ht : paritySafeFarProductWaveNextQuotient n (p₁,(q₁,s₁)) =
      paritySafeFarProductWaveNextQuotient n (p₂,(q₂,s₂))) :
    s₁ = s₂ := by
  ...
```

この theorem 自体は `p,q` の一致を必要としない。共通 `b` と共通 `t`、および `s` の odd-prime spacing だけを使うのが strongest interpretation。

---

## 3. 数学的核 C — pair-product から ordered `(p,q)` を復元

L051 optional A+ は未実装だったので、今回は dual coordinate injection に必要な範囲だけ回収する。

local/private helper でよい。

```lean
private theorem ordered_prime_pair_eq_of_mul_eq
    {p₁ q₁ p₂ q₂ : ℕ}
    (hp₁ : Nat.Prime p₁) (hq₁ : Nat.Prime q₁)
    (hp₂ : Nat.Prime p₂) (hq₂ : Nat.Prime q₂)
    (hlt₁ : p₁ < q₁) (hlt₂ : p₂ < q₂)
    (hmul : p₁*q₁ = p₂*q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  ...
```

L046 の private helper と同型でよい。generic factorization API へ昇格しない。

public consumer 候補:

```lean
theorem paritySafeRecharge_firstPair_eq_of_pairProduct_eq
    {n p₁ q₁ s₁ p₂ q₂ s₂ : ℕ}
    (h₁ : (p₁,(q₁,s₁)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (h₂ : (p₂,(q₂,s₂)) ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hb : p₁*q₁ = p₂*q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  ...
```

今回はこれを key-level injection の部品として使う。

---

## 4. dual-base coordinate と over-anchor universe

新規 module 候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeDualBaseCapacity.lean
```

最初は

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct
```

だけを試す。

coordinate:

```lean
def paritySafeRechargeDualBaseKey
    (n : ℕ) (key : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (key.1 * key.2.1,
    paritySafeFarProductWaveNextQuotient n key)
```

finite target universe:

```lean
noncomputable def paritySafeRechargeOverAnchorDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  ((paritySafeFarCofactorBaseOffsets n).product
    (paritySafeFarCofactorBaseOffsets n)).filter
      (fun bt => n < bt.1 * bt.2)
```

membership simp theorem:

```lean
@[simp] theorem mem_paritySafeRechargeOverAnchorDualBasePairs ... :
  (b,t) ∈ paritySafeRechargeOverAnchorDualBasePairs n ↔
    b ∈ paritySafeFarCofactorBaseOffsets n ∧
    t ∈ paritySafeFarCofactorBaseOffsets n ∧
    n < b*t := by
  ...
```

そして mandatory return:

```lean
theorem paritySafeRechargeDualBaseKey_mem_overAnchor
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeOverAnchorDualBasePairs n := by
  ...
```

L051 の二つの base-return theorem と section 1 を合成するだけにする。

---

## 5. mandatory main theorem — dual coordinate injectivity

最重要 theorem:

```lean
theorem paritySafeRechargeDualBaseKey_injectiveOn
    (n : ℕ) :
    Set.InjOn (paritySafeRechargeDualBaseKey n)
      (paritySafeRechargeSurvivingFarProductKeys n :
        Set (ℕ × (ℕ × ℕ))) := by
  ...
```

推奨 spine:

1. two recharge memberships `h₁`, `h₂` と coordinate equality `hcoord`。
2. `Prod.fst` / `Prod.snd` から
   - `p₁*q₁ = p₂*q₂`
   - `t₁ = t₂`
3. section 3 で `p₁=p₂`, `q₁=q₂`。
4. section 2 で `s₁=s₂`。
5. nested `Prod.ext` で key equality。

**重要:** injectivity は recharge domain 上のみ。terminal key や一般 far key へ拡張しない。

---

## 6. finite image と capacity bound

image を explicit に置くなら:

```lean
noncomputable def paritySafeRechargeDualBaseImage (n : ℕ) :
    Finset (ℕ × ℕ) :=
  (paritySafeRechargeSurvivingFarProductKeys n).image
    (paritySafeRechargeDualBaseKey n)
```

mandatory:

```lean
theorem paritySafeRechargeDualBaseImage_subset_overAnchor
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargeOverAnchorDualBasePairs n := by
  ...
```

```lean
theorem paritySafeRechargeDualBaseImage_card_eq_recharge
    (n : ℕ) :
    (paritySafeRechargeDualBaseImage n).card =
      (paritySafeRechargeSurvivingFarProductKeys n).card := by
  ...
```

injectivity から `Finset.card_image_of_injOn` を使う。

したがって第一 capacity theorem:

```lean
theorem paritySafeRechargeSurvivingFarProductKeys_card_le_overAnchorDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card ≤
      (paritySafeRechargeOverAnchorDualBasePairs n).card := by
  ...
```

ここが今回の main cardinal output。

---

## 7. global far-residual capacity consumer

L050 の exact split

```text
FarResidual.card = Terminal.card + Recharge.card
```

へ section 6 の recharge bound を入れる。

mandatory strongest consumer:

```lean
theorem paritySafeCanonicalFarResidual_card_le_terminal_add_overAnchorDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeOverAnchorDualBasePairs n).card := by
  ...
```

これは L051 の exact rearrangementから、実際の finite capacity upper bound へ戻る checkpoint である。

---

## 8. optional A+ — coarse product bound

安ければ product-filter subset から

```lean
theorem paritySafeRechargeOverAnchorDualBasePairs_card_le_base_sq
    (n : ℕ) :
    (paritySafeRechargeOverAnchorDualBasePairs n).card ≤
      (paritySafeFarCofactorBaseOffsets n).card ^ 2 := by
  ...
```

または multiplication 表記で

```text
base.card * base.card
```

でもよい。

これを global consumer と合成してもよいが、今回の本命は filtered over-anchor universe の方である。粗い square bound のために proof surface を膨らませない。

---

## 9. arithmetic boundary witnesses

型付き recharge membership まで数値展開する必要はない。

coordinate 一方だけでは key を決めないことを示す arithmetic beam を置くなら次が使える。

### same `b`, different `t`

```text
37^2 + 56 = 3*5*19*5
37^2 + 26 = 3*5*31*3
```

両方で `b=3*5=15` だが cofactor/quotient は `5` と `3`。

### same `t`, different `b`

```text
32^2 + 11 = 3*5*23*3
32^2 + 47 = 3*7*17*3
```

両方で `t=3` だが pair-product は `15` と `21`。

これらは arithmetic witness に限定し、実際の recharge Finset membership まで主張しない。

意味:

```text
b alone では不足
t alone でも不足
(b,t) together が今回の candidate coordinate
```

---

## 10. 今回の strongest interpretation

L051:

```text
recharge key
  ↦ b=p*q ∈ reduced base
  ↦ t=t₀  ∈ reduced base
```

L052:

```text
recharge key
  ↦ (b,t)
  ∈ base × base
  with n < b*t
```

そして odd-prime spacing + shell width により

```text
same (b,t)
  → same ordered (p,q)
  → same s
  → same recharge key
```

となる。

したがって third prime `s` は独立な cardinal coordinate ではなくなり、recharge mass は二つの same-anchor reduced-base coordinates だけで有限制御される。

---

## 11. 禁止事項 / 非目標

今回は以下を行わない。

- terminal key を dual-base injection に混ぜる
- `b` 単独または `t` 単独の injectivity
- `b=t` の否定
- `b≤t` / `t≤b` の一般主張
- `gcd b t = 1` の無根拠な主張
- `p ∤ t`, `q ∤ t`
- `t` の prime / squarefree 性
- dual-base pair から smaller anchor を作ること
- smaller-anchor `SquareOffsetsFullyCovered`
- induction / infinite descent
- generic graph / hypergraph
- analytic sieve / PNT / Mertens / harmonic asymptotic
- over-anchor pair cardinality の closed form
- global contradiction
- Legendre conjecture / RH の proof claim

---

## 12. Outcome 判定

### Outcome A+ — DUAL-BASE KEY INJECTION / CAPACITY

以下を全て閉じる。

1. recharge key で `n < (p*q)*t₀`
2. fixed `(b,t)` で third prime `s` が一意
3. ordered prime-pair product uniqueness
4. `paritySafeRechargeDualBaseKey`
5. over-anchor dual-base finite universe
6. recharge key → over-anchor universe
7. recharge-domain `InjOn`
8. image card = recharge card
9. recharge card ≤ over-anchor dual-base card
10. global far-residual capacity consumer
11. optional coarse base-square boundまたは arithmetic boundary witness のどちらか一つ以上

### Outcome A — DUAL-BASE INJECTION

1–10 を閉じる。optional 11 は未実装。

### Outcome B — THIRD-PRIME UNIQUENESS GAP

1, 3–6 は閉じるが、same `(b,t)` から `s₁=s₂` を出す際に Lean API 上の具体的な一補題が不足する。

その場合は不足する最小 theorem shape を report に明記して停止する。generic order library の大規模 refactor はしない。

### Outcome C — COORDINATE COLLISION

実際に異なる recharge key が同じ `(b,t)` を持つ arithmetic counterexample が成立する場合。

その具体例を report に固定し、injectivity を主張せず停止する。

---

## 13. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source のみ:

```text
sorry
admit
axiom
native_decide
```

を監査する。

facade:

```text
DkMath.NumberTheory.Legendre
```

へ新 module import を追加する。

report 候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-parity-safe-recharge-dual-base-injection-capacity-260826.md
```

---

## 14. 停止条件

今回の checkpoint は

```text
recharge key
  → over-anchor dual reduced-base pair
  → injective finite coordinate
  → cardinal capacity
```

で止める。

その先の over-anchor pair universe 自体の exact cardinal evaluation、symmetry、valuation/depth split、smaller-anchor interpretation は **次 checkpoint 以降** に回す。
