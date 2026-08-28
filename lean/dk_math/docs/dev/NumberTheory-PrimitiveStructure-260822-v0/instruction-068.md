# instruction-068 — PRIM-L053 Odd Shell Quotient / Prime-Admissible Dual-Base Capacity

## 0. 作業先

- repository: `Deskuma/dkmath`
- branch: `wip/number-theory-primitive-structure-260822-v2`
- base HEAD at review: `a5da06e62ddcbee953d2de206c203e502257e4ac`
- Lean / Mathlib: current checkout (`Lean 4.32.2`) を維持する。upgrade しない。

前 checkpoint `PRIM-L052` は **Outcome A — DUAL-BASE INJECTION** として受理する。

L052 までで recharge surviving key

```text
key := (p,(q,s))
b   := p*q
t   := paritySafeFarProductWaveNextQuotient n key
```

について、

```text
b ∈ paritySafeFarCofactorBaseOffsets n
t ∈ paritySafeFarCofactorBaseOffsets n
n < b*t
n^2 < (b*t)*s ≤ n^2 + 2*n
s ∈ squareAnchorOddActivePrimes n
```

が成立し、さらに

```text
key ↦ (b,t)
```

は recharge domain 上で injective になった。

現在の capacity は

```text
Recharge.card ≤ OverAnchorDualBasePairs.card
```

だが、`OverAnchorDualBasePairs` はまだ粗い。今回の bounded target は、
**fixed `(b,t)` から shell 内で許される odd quotient を算術的に一意化し、
その quotient が実際に active prime で shell に入る pair だけへ capacity universe を縮めること**である。

`base.card ^ 2` の coarse bound を追加する checkpoint ではない。

---

## 1. 数学的核 — shell quotient は連続する高々二候補

`c := b*t` と置く。

L052 の over-anchor 条件から

```text
n < c
```

なので

```text
2*n < 2*c.
```

shell は

```text
n^2 < c*s ≤ n^2 + 2*n
```

である。

最初に `n^2` を越える `c` の倍数の quotient を

```text
k := n^2 / c + 1
```

とすると、任意の shell quotient `s` は

```text
k ≤ s ≤ k+1
```

を満たす。

理由:

1. `n^2 < c*s` から `n^2 / c < s`、よって `k ≤ s`。
2. `k` 自体が `n^2` を越える最初の quotient。
3. もし `k+2 ≤ s` なら、`c*(k+2)` は `c*k` より `2*c` 以上先にある。
4. `2*c > 2*n` なので shell 上端 `n^2+2*n` を越える。

従って候補は連続する二整数

```text
k, k+1
```

だけである。

recharge の third prime `s` は odd prime なので、この二候補のうち odd な方しか取れない。

これを今回 explicit selector にする。

---

## 2. 新規 module

候補:

```text
DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector
```

file:

```text
lean/dk_math/DkMath/NumberTheory/Legendre/ParitySafeRechargeOddShellSelector.lean
```

最初は

```lean
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDualBaseCapacity
```

だけを試す。

完成後 facade

```text
DkMath.NumberTheory.Legendre
```

へ import を追加する。

---

## 3. L053.1 — odd shell selector

薄い定義を置く。

```lean
/-- The unique odd candidate among the at-most-two shell quotients for `b*t`. -/
def paritySafeRechargeOddShellQuotient
    (n b t : ℕ) : ℕ :=
  let k := n ^ 2 / (b * t) + 1
  if Odd k then k else k + 1
```

`Odd` の `Decidable` / unfolding が重い場合は、同値な `% 2` 実装へ変更してよい。

例:

```lean
if k % 2 = 1 then k else k + 1
```

ただし public theorem では `Odd` と接続できる形にする。

必須:

```lean
theorem paritySafeRechargeOddShellQuotient_odd
    {n b t : ℕ}
    (hbt : 0 < b * t) :
    Odd (paritySafeRechargeOddShellQuotient n b t) := by
  ...
```

`hbt` が不要なら外してよい。

---

## 4. L053.2 — at-most-two quotient lemma

今回の first main arithmetic lemma。

推奨 statement:

```lean
theorem paritySafeRecharge_shellQuotient_eq_next_or_succ
    {n b t s : ℕ}
    (hover : n < b * t)
    (hshell :
      n ^ 2 < (b * t) * s ∧
      (b * t) * s ≤ n ^ 2 + 2 * n) :
    s = n ^ 2 / (b * t) + 1 ∨
      s = n ^ 2 / (b * t) + 2 := by
  ...
```

向きは `s = ...` / `... = s` のどちらでもよい。

証明 spine:

1. `hover` から `0 < b*t`。
2. 下側 shell inequality を `Nat.div_lt_iff_lt_mul` 系で quotient lower bound へ変換。
3. `k := n^2/(b*t)+1` を置く。
4. `k ≤ s`。
5. `k+2 ≤ s` を仮定。
6. quotient/remainder の基本不等式から `n^2 < (b*t)*k` または必要十分な lower relation を得る。
7. `2*n < 2*(b*t)` と shell upper を合わせて矛盾。
8. `s ≤ k+1`。
9. `omega` で二候補へ。

Mathlib の division normal form が重い場合、局所 helper を作ってよい。
一般的な division theory module へ昇格しない。

---

## 5. L053.3 — odd quotient uniqueness

必須 theorem:

```lean
theorem paritySafeRecharge_shellOddQuotient_eq_selector
    {n b t s : ℕ}
    (hover : n < b * t)
    (hshell :
      n ^ 2 < (b * t) * s ∧
      (b * t) * s ≤ n ^ 2 + 2 * n)
    (hsodd : Odd s) :
    s = paritySafeRechargeOddShellQuotient n b t := by
  ...
```

推奨:

1. L053.2 で `s=k ∨ s=k+1`。
2. `Odd k` で場合分け。
3. `k` odd なら `k+1` は even なので `s=k`。
4. `k` not odd なら consecutive parity から `k+1` odd、`s=k+1`。

既存 parity API が使いにくければ `Nat.even_or_odd` / `%2` / `omega` を局所使用してよい。

---

## 6. L053.4 — recharge third prime is the selector

key-level strongest consumer:

```lean
theorem paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient
    {n p q s : ℕ}
    (hkey : (p,(q,s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    s = paritySafeRechargeOddShellQuotient n (p*q)
      (paritySafeFarProductWaveNextQuotient n (p,(q,s))) := by
  ...
```

使うもの:

- L052 `anchor_lt_pairProduct_mul_nextQuotient`
- L052 `dualProduct_shell_packet`
- far gate / active prime packet から `Odd s`
- L053.3

この theorem で third prime `s` を existential/key coordinate から arithmetic function `(n,b,t) ↦ s` へ移す。

---

## 7. L053.5 — prime-admissible dual-base universe

`OverAnchorDualBasePairs` をさらに filter する。

```lean
noncomputable def paritySafeRechargePrimeAdmissibleDualBasePairs
    (n : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeOverAnchorDualBasePairs n).filter
    (fun bt =>
      let s := paritySafeRechargeOddShellQuotient n bt.1 bt.2
      s ∈ squareAnchorOddActivePrimes n ∧
      n ^ 2 < (bt.1 * bt.2) * s ∧
      (bt.1 * bt.2) * s ≤ n ^ 2 + 2 * n ∧
      2 * n < bt.1 * s)
```

最後の

```text
2*n < b*s
```

は original far modulus `p*q*s` の条件を pair-product 座標へ移したもの。

今回 `q < s` や `b=p*q` の独立 witness までは universe に入れない。
それは次段で必要なら sharpen する。

membership theorem:

```lean
@[simp] theorem mem_paritySafeRechargePrimeAdmissibleDualBasePairs
    {n b t : ℕ} :
    (b,t) ∈ paritySafeRechargePrimeAdmissibleDualBasePairs n ↔
      (b,t) ∈ paritySafeRechargeOverAnchorDualBasePairs n ∧
      let s := paritySafeRechargeOddShellQuotient n b t
      s ∈ squareAnchorOddActivePrimes n ∧
      n ^ 2 < (b*t)*s ∧
      (b*t)*s ≤ n ^ 2 + 2*n ∧
      2*n < b*s := by
  ...
```

association / formatting は Lean が扱いやすい形へ調整してよい。

---

## 8. L053.6 — actual recharge image lands in refined universe

必須:

```lean
theorem paritySafeRechargeDualBaseKey_mem_primeAdmissible
    {n : ℕ} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  ...
```

key を `(p,(q,s))` に分解し、

- L052 over-anchor membership
- L053.4 `s = selector`
- `s` active
- L052 shell packet
- far key condition `2*n < p*q*s`

を投入する。

続けて image subset:

```lean
theorem paritySafeRechargeDualBaseImage_subset_primeAdmissible
    (n : ℕ) :
    paritySafeRechargeDualBaseImage n ⊆
      paritySafeRechargePrimeAdmissibleDualBasePairs n := by
  ...
```

---

## 9. L053.7 — refined capacity

L052 で image card = recharge card は既にあるので、今回の新規 subset から

```lean
theorem paritySafeRechargeSurvivingFarProductKeys_card_le_primeAdmissibleDualBasePairs
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card ≤
      (paritySafeRechargePrimeAdmissibleDualBasePairs n).card := by
  ...
```

を必須とする。

さらに global consumer:

```lean
theorem paritySafeCanonicalFarResidual_card_le_terminal_add_primeAdmissibleDualBase
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card ≤
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargePrimeAdmissibleDualBasePairs n).card := by
  ...
```

L052 の `OverAnchorDualBasePairs` bound より strictly stronger な theorem statement である。

「strict cardinal inequality」を全 n で証明する必要はない。

---

## 10. L053.8 — refinement relation

strongly preferred:

```lean
theorem paritySafeRechargePrimeAdmissibleDualBasePairs_subset_overAnchor
    (n : ℕ) :
    paritySafeRechargePrimeAdmissibleDualBasePairs n ⊆
      paritySafeRechargeOverAnchorDualBasePairs n := by
  ...
```

および

```lean
theorem paritySafeRechargePrimeAdmissibleDualBasePairs_card_le_overAnchor
    (n : ℕ) :
    (paritySafeRechargePrimeAdmissibleDualBasePairs n).card ≤
      (paritySafeRechargeOverAnchorDualBasePairs n).card := by
  ...
```

これは L052 capacity を今回の capacity が refinement していることの公開記録。

---

## 11. arithmetic false beams

最低一つ、`OverAnchor` だけでは actual key を表せないことを arithmetic witness で固定する。

推奨例:

```text
n = 62
b = 33 = 3*11
t = 3
b*t = 99 > 62
odd shell selector = 39
62^2 < 99*39 ≤ 62^2 + 2*62
39 is composite
```

数値確認:

```text
62^2 = 3844
99*39 = 3861
62^2 + 124 = 3968
39 = 3*13
```

例えば:

```lean
theorem paritySafeRechargeOddShellSelector_composite_false_beam :
    62 < 33 * 3 ∧
      paritySafeRechargeOddShellQuotient 62 33 3 = 39 ∧
      62 ^ 2 < (33 * 3) * 39 ∧
      (33 * 3) * 39 ≤ 62 ^ 2 + 2 * 62 ∧
      ¬ Nat.Prime 39 := by
  norm_num [paritySafeRechargeOddShellQuotient]
```

もし `Odd`-based `if` の simplification が重ければ、同趣旨の別例へ変更可。

第二 witness を置くなら、`selector` が prime でも shell fit を失う例を選んでよい。

```text
n=17, b=5, t=5
b*t=25>17
selector=13 prime
25*13=325 > 17^2+34=323
```

目的は、

```text
OverAnchor
```

だけでも、

```text
selector prime
```

だけでも insufficient であることを固定すること。

---

## 12. 今回の strongest interpretation

L052:

```text
recharge key
  ↪ (b,t) ∈ Base(n)^2
             with n < b*t
```

L053:

```text
recharge key
  ↪ (b,t)
      ↓
  s := OddShellQuotient(n,b,t)
      ↓
  s is active prime
  b*t*s is actually inside shell
  b*s is far
```

つまり third prime `s` は、もはや自由座標ではない。

```text
s = explicit arithmetic selector(n,b,t)
```

として消去される。

L052 の injectivity は「同じ `(b,t)` なら同じ `s`」だった。
L053 はさらに、その `s` の値そのものを arithmetic function として公開する。

これにより、capacity universe は

```text
all over-anchor reduced-base pairs
```

から

```text
odd-shell selector が prime として実際に shell/far 条件を満たす pairs
```

だけへ縮む。

---

## 13. 禁止事項 / 非目標

今回は以下を行わない。

- `base.card ^ 2` の coarse estimate を主成果にしない
- prime counting / PNT / Mertens / Brun / Selberg sieve
- candidate universe の asymptotic density
- `b=p*q` の independent semiprime witness filter の一般化
- candidate pair から recharge key への reverse surjection
- exact equality `Recharge.card = PrimeAdmissiblePairs.card`
- generic least-prime-factor framework
- `t` の primality / squarefreeness
- `gcd b t = 1`, `b=t`, `b<t`, `t<b` の無根拠な主張
- `p ∤ t`, `q ∤ t`
- smaller anchor / descent / induction
- global contradiction
- Legendre conjecture / RH proof claim

今回の universe は依然 **upper capacity universe** である。

---

## 14. Outcome 判定

### Outcome A+ — ODD-SHELL PRIME CAPACITY

1. explicit odd shell selector
2. at-most-two quotient lemma
3. odd shell quotient uniqueness
4. actual recharge third prime = selector
5. prime-admissible dual-base Finset
6. actual dual image subset
7. refined recharge capacity
8. refined global far-residual capacity
9. refinement relation to L052 over-anchor universe
10. arithmetic false beam

### Outcome A — ODD-SHELL SELECTOR

1–8 と false beam を完成。
refinement card theorem の一部だけ未実装。

### Outcome B — ARITHMETIC SELECTOR ONLY

selector と actual `s=selector` は閉じるが、prime-admissible Finset / capacity transport が Lean surface 上不自然。
その場合は report して停止する。

### Outcome C — FALSE

`n < b*t` と shell 条件下でも odd third quotient が一意化できない具体的 counterexample が出た場合。
その witness を形式化して停止する。

---

## 15. validation

最低限:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeOddShellSelector
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

build 済みなら結果を report に記録する。

---

## 16. report

候補:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
primitive-parity-safe-recharge-odd-shell-prime-capacity-260826.md
```

最低限:

1. Outcome
2. selector 定義
3. at-most-two shell quotient proof spine
4. odd uniqueness
5. actual third prime equality
6. prime-admissible capacity universe
7. recharge/global capacity theorem
8. false beam
9. 非目標
10. validation

を記録する。
