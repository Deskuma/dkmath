# Note: Review: Ultra-001-S2

# 戦況判定

**Ultra-001S、完全討伐。** ⚔️🧙‍♀️✨️

いやはや、本当に二周目は速い（笑）

一周目の旧 ABC 塔では、

```text
padic valuation
→ layer-cake
→ 幾何級数
→ Chernoff
→ tail
```

を手探りで構築していた。

今回は既に地図・武器・失敗例があるため、

```text
GN exact factorization
→ Hensel uniqueness
→ CRT
→ excess-active profile
→ Euler product
→ q^(-3/2) envelope
```

まで一直線に進めた。

S2 では、予告した経路そのままに、公比 $3/4$ の有限幾何級数から、

$$\operatorname{GNExcessLocalDensityTail}\left(p,q,K,\frac12\right)\le\frac{4(p-1)}{q^{3/2}}$$

を証明し、`htail` 仮定を完全に除去している。これで small-profile 側の定数は $Q,b,X$ に依存せず、指数 $p$ のみに依存する。

PR #69 は現在、21 commits、41 files、11299 additions、mergeable。
Lean CI run 388 も成功している。✔

---

## 現在の完成形

small side について、無条件に、

$$\sum_{a=0}^{X}\exp\left(\frac12E_Q(a)\right)\le2(X+1)C_p+\operatorname{LargeBoundary}(Q,p,b,X)$$

を得た。

ここで、

```text
E_Q(a)
  = finite prime family Q 上の
    non-exceptional valuation excess

C_p
  = GNExcessHalfEulerConstant p

LargeBoundary
  = active modulus が X+1 を超える profile の寄与
```

じゃ。

したがって、

```text
local multiplicity decay
finite CRT density
finite Euler factorization
infinite summable envelope
```

は全部閉じた。

残っているのは、式の右端に明示的に立っている、

```lean
GNExcessLargeBoundaryProfileSum
```

だけ。

---

## 第2ボスの正体

target point において、

```text
N := GNNonExceptionalPart p a b
```

とする。

active excess profile が作る modulus を $M$ とすると、その正体は、

$$M=\prod_{v_q(N)\ge2}q^{v_q(N)}$$

じゃ。

つまり、$N$ のうち **重複して現れる素数について、その prime-power を丸ごと集めた整数** である。

旧 ABC 塔の言葉へ戻すと、

$$M=\operatorname{piSqRad}(N)\operatorname{sqTail}(N)$$

さらに既存の、

$$\operatorname{sqTail}(N)=\operatorname{piSqRad}(N)\operatorname{twoTail}(N)$$

を代入すれば、

$$M=\operatorname{piSqRad}(N)^2\operatorname{twoTail}(N)$$

となる。

ここで、

```text
piSqRad(N)
  = valuation ≥ 2 の異なる素数の積

twoTail(N)
  = valuation 第3層以後

M
  = 平方殻を含む全 repeated prime-power part
```

じゃ。

したがって large profile、

$$X+1<M$$

とは、

> **区間長を超える巨大な非例外 squareful divisor が、GN の中に存在する**

ということになる。

これは単なる Chernoff の境界誤差ではない。

Cyclotomic / GN 的には、

```text
多数または高深度の Hensel lift が
一つの GN 値へ同時集積した状態
```

であり、一般化された **Wieferich 集積核** と読むことができる。

---

## large profile は二体へ分裂する

$$\log M=2\log\operatorname{piSqRad}(N)+\log\operatorname{twoTail}(N)$$

なので、$X+1<M$ なら必ず、

$$\frac14\log(X+1)<\log\operatorname{piSqRad}(N)$$

または、

$$\frac12\log(X+1)<\log\operatorname{twoTail}(N)$$

のどちらかが成立する。

冪の形では、

$$\left(X+1\right)^{1/4}<\operatorname{piSqRad}(N)$$

または、

$$\left(X+1\right)^{1/2}<\operatorname{twoTail}(N)$$

じゃ。

つまり第2ボスは、さらに、

```text
Repeated-support heavy
  valuation ≥ 2 の異なる素数が多すぎる

Deep-tail heavy
  valuation 第3層以後が深すぎる
```

へ分裂する。

これはまさに旧 ABC 塔が `piSqRad` と `twoTail` を別々に扱っていた理由だった。

二周目にして、旧塔のラスボス部屋へ裏口から戻ってきたわけじゃ（笑）

---

## さらに得られる境界 weight の圧縮

active prime の個数を $r$ とする。

各 active prime $q$ は non-exceptional GN prime なので、

$$q\equiv1\pmod p$$

を満たす。

従って $p<q$ であり、

$$(p-1)^r\le\operatorname{piSqRad}(N)$$

となる。

また、

$$\exp\left(\frac12E\right)=\operatorname{sqTail}(N)^{1/2}$$

なので、large boundary の一 profile weight は、

$$(p-1)^r\exp\left(\frac12E\right)\le\operatorname{piSqRad}(N)\operatorname{sqTail}(N)^{1/2}$$

さらに $\operatorname{piSqRad}(N)\le\operatorname{sqTail}(N)$ より、

$$(p-1)^r\exp\left(\frac12E\right)\le M^{3/4}$$

まで圧縮できる。

これはまだ large sum の吸収ではないが、

```text
root-address charge × exponential excess
```

を、

```text
large squareful divisor の 3/4 乗
```

へ一本化する強い診断になる。

---

## わざと立てた第3隠れボスのフラグ

はい。すでに姿が見えておる（笑）

large boundary を仮に平均的に吸収できたとしても、得られるのは、

```text
bad coordinates は少ない
```

という density / moment theorem じゃ。

しかし `ABCGNOddPrimeJointContract ε` が要求するのは、

```text
全 positive coprime Triple に対する
同じ p, ρ, C の pointwise bound
```

である。

したがって隠れボスは、

> **平均・密度・有限例外候補から、全 Triple の uniform contract へどう戻すか**

じゃ。

RPG表示すると、

```text
Boss 1:
  local geometric tail
  → S2 で討伐

Boss 2:
  large squareful GN divisor
  → 現在の主戦場

Hidden Boss 3:
  average / density
  → uniform pointwise ABC contract
```

となる。

もっと恐ろしいことを言えば、以前推論した通り、

```text
ABC statement
  ↔
Nonempty (ABCGNOddPrimeJointContract ε)
```

が成立する可能性が極めて高い。

逆方向は $p=3$ を固定すれば、

$$GN_3(a,b)\le3(a+b)^2$$

から比較的短く作れる。

つまり隠れボス3は、別の新敵ではなく、**ABC 本体が鎧を着替えて再登場するイベント**かもしれぬ🤣

---

## ダブルBrain 次作戦

次は二本を並行させるのがよい。

### Brain A：U-001T — large boundary packet の exact 算術化

新モジュール候補：

```text
DkMath.ABC.GNExcessLargeBoundaryPacket
```

ここでは「吸収」を急がず、large profile が返す整数を完全に固定する。

主定義候補：

```lean
def repeatedPrimePowerPart (n : ℕ) : ℕ :=
  ∏ q ∈ n.factorization.support.filter
      (fun q => 2 ≤ n.factorization q),
    q ^ n.factorization q

def GNNonExceptionalRepeatedPart
    (p a b : ℕ) : ℕ :=
  repeatedPrimePowerPart
    (GNNonExceptionalPart p a b)
```

主定理：

```lean
repeatedPrimePowerPart_eq_piSqRad_mul_sqTail

repeatedPrimePowerPart_eq_piSqRad_sq_mul_twoTail

repeatedPrimePowerPart_dvd_self

rad_repeatedPrimePowerPart_eq_piSqRad
```

target profile との接続：

```lean
GNExcessJointDepthModulus_at_intervalFamily_eq_repeatedPart
```

さらに packet：

```lean
structure GNNonExceptionalLargeBoundaryPacket
    (p a b X : ℕ) where
  modulus : ℕ
  modulus_eq :
    modulus =
      GNNonExceptionalRepeatedPart p a b
  modulus_dvd_GN :
    modulus ∣ GN p a b
  modulus_dvd_nonExceptionalPart :
    modulus ∣ GNNonExceptionalPart p a b
  interval_lt_modulus :
    X + 1 < modulus
  squareful :
    ∀ q, q ∣ modulus → q ^ 2 ∣ modulus
  support_order :
    ∀ q, q ∣ modulus → Nat.Prime q →
      q % p = 1
```

その上に、

```lean
GN_largeBoundary_piSqRad_or_twoTail
GN_largeBoundary_rootCharge_le_piSqRad
GN_largeBoundary_weight_half_le_rpow_three_quarters
```

を置く。

### Brain B：contract と ABC の逆橋

別モジュール候補：

```text
DkMath.ABC.GNJointContractEquivalence
```

まず ABC statement を仮定として受け取る。

```lean
def ABCRawBound (ε : ℝ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ a b c : ℕ,
      a + b = c →
      Nat.Coprime a b →
      (c : ℝ) ≤
        K * (rad (a * b * c) : ℝ) ^ (1 + ε)
```

そして、

```lean
theorem GNOddPrimeJointContract_of_ABCRawBound
    {ε : ℝ}
    (hε : 0 < ε)
    (Habc : ABCRawBound ε) :
    Nonempty (ABCGNOddPrimeJointContract ε)
```

を $p=3$ 固定で作る。

逆は既存 endpoint から出るため、

```lean
theorem ABCRawBound_iff_nonempty_GNOddPrimeJointContract
    {ε : ℝ}
    (hε : 0 < ε) :
    ABCRawBound ε ↔
      Nonempty (ABCGNOddPrimeJointContract ε)
```

が狙える。

これが通れば、

```text
large-boundary absorption は
単なる技術的残件なのか

それとも ABC と同等級の核心なのか
```

を Lean 上で正確に判定できる。

---

## Codex 次指示

```text
Continue Ultra-001 with checkpoint U-001T.

Primary goal:
Turn every large excess profile into an exact non-exceptional squareful
divisor packet, reconnect it to the legacy piSqRad / sqTail / twoTail
coordinates, and expose the two genuine large-boundary branches.

Do not attempt to absorb the large-boundary sum yet.

Part A — generic repeated prime-power part

1. Define a generic natural-number object containing the full prime powers
   whose valuations are at least two:

   repeatedPrimePowerPart n
     = ∏ q with 2 ≤ factorization n q,
         q ^ factorization n q.

2. Prove for n ≠ 0:

   repeatedPrimePowerPart n
     = piSqRad n * sqTail n

   repeatedPrimePowerPart n
     = (piSqRad n)^2 * twoTail n

3. Prove:

   repeatedPrimePowerPart n ∣ n

   rad (repeatedPrimePowerPart n) = piSqRad n

   piSqRad n ∣ sqTail n.

Part B — exact GN specialization

4. Define:

   GNNonExceptionalRepeatedPart p a b :=
     repeatedPrimePowerPart
       (GNNonExceptionalPart p a b).

5. For the canonical interval family and the target excess profile, prove:

   GNExcessJointDepthModulus Q excess
     =
   GNNonExceptionalRepeatedPart p a b.

6. Prove that this modulus divides both:

   GNNonExceptionalPart p a b
   GN p a b.

Part C — large-boundary packet

7. Package the exact target data in:

   GNNonExceptionalLargeBoundaryPacket.

   Include:
   - exact repeated-part identity;
   - divisibility into GN and the non-exceptional part;
   - interval length < modulus;
   - every support prime occurs to depth at least two;
   - every support prime is a non-exceptional GN prime;
   - exact-order consequence q % p = 1.

Part D — legacy pincer

8. From

   X + 1 < repeatedPrimePowerPart N

   and

   repeatedPrimePowerPart N
     = (piSqRad N)^2 * twoTail N

   prove the logarithmic dichotomy:

   (1/4) * log (X + 1) < log (piSqRad N)
   or
   (1/2) * log (X + 1) < log (twoTail N).

9. Add real-rpow forms only after the logarithmic form is stable.

Part E — address-charge diagnosis

10. Prove that for the active support:

    (p - 1) ^ active.card ≤ piSqRad N.

11. At t = 1/2, prove the profile boundary weight estimate:

    rootAddressCharge * exp ((1/2) * excessMass)
      ≤ (repeatedPrimePowerPart N : ℝ) ^ (3/4).

This is a diagnosis theorem only. Do not sum the RHS over profiles and do not
claim large-boundary absorption.

Part F — equivalence audit, separate file if practical

12. Define a reusable ABCRawBound ε predicate matching abc_main.

13. Using the fixed exponent p = 3 and the elementary bound

    GN 3 a b ≤ 3 * (a + b)^2,

    prove:

    ABCRawBound ε →
      Nonempty (ABCGNOddPrimeJointContract ε).

14. Combine with the existing contract-to-ABC endpoint to prove the
    equivalence, if no hidden API obstruction appears.

Boundaries:

- No claim that large boundary is controlled.
- No claim of M3 summability.
- No claim of deterministic target escape.
- No removal of abc_main_axiom.
- Preserve all U-001A through U-001S endpoints.

Report:
report-ultra-001-T.md

Branch outcomes:

A. Exact repeated-part packet, pincer, and equivalence audit complete.
B. Packet and pincer complete; ABC-to-contract reverse bridge isolated.
C. Exact smallest factorization or real-rpow API obstruction recorded.
```

## 戦線地図

```text
U-001S
  small Euler side                  complete

U-001T
  large repeated-part identity      next
  squareful divisor packet          next
  piSqRad / twoTail pincer          next
  ABC ↔ contract equivalence audit  next

U-001U
  repeated-support-heavy branch     future
  deep-twoTail-heavy branch         future

Hidden Boss
  density → uniform contract        waiting

abc_main_axiom removal              not reached
```

**第二周は確実に速い。**

だが、わざと立てたフラグどおり、城の地下に、

```text
GENERALIZED WIEFERICH ACCUMULATION
```

と書かれた扉が見えておる🤣

🧙‍♀️✨️ **次は扉を開ける前に、扉そのものを Lean の structure に封印する。進軍再開じゃ。**
