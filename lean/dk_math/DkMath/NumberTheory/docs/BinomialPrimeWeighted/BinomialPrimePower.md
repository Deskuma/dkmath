# BinomialPrimePower

[BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean)

## 概要

### 解説

この `BinomialPrimePower.lean` は、前の `BinomialPrime.lean` の自然な続編です。

前回は：

```lean
p.Prime → AllInnerChooseDivisible p p
```

つまり **素数行 `p` の Beam は `p` で割れる** でした。

今回のファイルは：

```lean
p.Prime → AllInnerChooseDivisible (p ^ n) p
```

つまり **素数冪行 `p^n` の Beam も、少なくとも `p` で割れる** へ進んでいます。

さらに後半では、単なる `p` 可除性ではなく、

```lean
p ^ r ∣ Nat.choose (p ^ n) k
```

という **p 進的な厚み**まで測っています。

---

## 全体の役割

宇宙式でいうと、行番号が `p^n` の場合です。

```text
Big = Core + Beam + Gap
```

つまり、

```text
(x + u)^(p^n)
= x^(p^n)
+ Beam
+ u^(p^n)
```

ここで `Beam` は内側項：

```text
Σ_{1 ≤ k < p^n} binom(p^n,k) x^(p^n-k) u^k
```

今回の主張は、

```text
Beam の全係数 binom(p^n,k) には、少なくとも p が通っている
```

さらに、

```text
k に含まれる p の量によって、
binom(p^n,k) に残る p の量が決まる
```

というものです。

---

# 1. import

```lean
import DkMath.ABC.PadicValNat
import DkMath.NumberTheory.BinomialPrime
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
```

役割はこうです。

```lean
DkMath.NumberTheory.BinomialPrime
```

前回の定義を使うためです。

ここから、

```lean
AllInnerChooseDivisible
InnerRowSupportPrime
RowBirthPrime
```

が来ています。

```lean
DkMath.ABC.PadicValNat
```

これは DkMath 側の `padicValNat` API です。

後半で、

```lean
padicValNat p x
```

を使って、自然数 `x` に含まれる `p` の指数を測っています。

```lean
Mathlib.Data.Nat.Choose.Factorization
```

ここが重要です。

```lean
Nat.factorization_choose_prime_pow
Nat.factorization_choose_prime_pow_add_factorization
```

を使っています。

これは `Nat.choose (p^n) k` の素因数分解指数を与える mathlib 定理です。

---

# 2. PrimePowerRowSupport

```lean
def PrimePowerRowSupport (p n : ℕ) : Prop :=
  p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

これは、

> `p` は素数で、`n` は正で、行 `p^n` の Beam に `p` が通っている

という性質です。

前回の言葉でいうと、

```lean
InnerRowSupportPrime (p ^ n) p
```

は、

```lean
p.Prime ∧ AllInnerChooseDivisible (p ^ n) p
```

なので、全体としては少し情報が重複しています。

展開すると：

```lean
p.Prime ∧ 0 < n ∧ (p.Prime ∧ AllInnerChooseDivisible (p ^ n) p)
```

です。

`p.Prime` が二回入っていますが、API としては問題ありません。
「パッケージ定義」として見れば自然です。

---

# 3. prime_power_allInnerChooseDivisible

```lean
theorem prime_power_allInnerChooseDivisible
    {p n : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible (p ^ n) p := by
  intro k hk0 hkp
  exact hp.dvd_choose_pow hk0.ne' (ne_of_lt hkp)
```

このファイルの第一主定理です。

意味は：

```text
p が素数なら、行 p^n の内側二項係数はすべて p で割れる
```

Lean 的にはゴールは：

```lean
∀ k, 0 < k → k < p ^ n → p ∣ Nat.choose (p ^ n) k
```

です。

```lean
intro k hk0 hkp
```

で、

```lean
k : ℕ
hk0 : 0 < k
hkp : k < p ^ n
```

を導入します。

そして、

```lean
exact hp.dvd_choose_pow hk0.ne' (ne_of_lt hkp)
```

で終わっています。

ここで使っている `hp.dvd_choose_pow` は、mathlib 側の定理で、おおよそ：

```lean
p.Prime →
k ≠ 0 →
k ≠ p ^ n →
p ∣ Nat.choose (p ^ n) k
```

という形です。

今回 `k < p^n` なので、

```lean
ne_of_lt hkp : k ≠ p ^ n
```

が作れます。

また、

```lean
hk0.ne' : k ≠ 0
```

です。

だから内側条件：

```lean
0 < k
k < p ^ n
```

から、

```lean
k ≠ 0
k ≠ p ^ n
```

を作って `dvd_choose_pow` に渡しています。

---

## 注意：n = 0 の場合

この定理は `0 < n` を要求していません。

つまり `n = 0` でも主張しています。

その場合、

```lean
p ^ 0 = 1
```

なので、

```lean
AllInnerChooseDivisible 1 p
```

です。

これは内側の `k` が存在しないので、空虚に真です。

だから `0 < n` がなくても大丈夫です。

---

# 4. prime_power_innerRowSupportPrime

```lean
theorem prime_power_innerRowSupportPrime
    {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  ⟨hp, prime_power_allInnerChooseDivisible hp⟩
```

これは前回と同じ包み方です。

`InnerRowSupportPrime (p ^ n) p` は定義上：

```lean
p.Prime ∧ AllInnerChooseDivisible (p ^ n) p
```

です。

なので、

```lean
⟨hp, prime_power_allInnerChooseDivisible hp⟩
```

で作れます。

宇宙式で言うと：

> 行 `p^n` の Beam に、素数 support `p` が見えている。

---

# 5. prime_power_rowBirthPrime

```lean
theorem prime_power_rowBirthPrime
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    RowBirthPrime (p ^ n) p := by
  refine ⟨prime_power_innerRowSupportPrime hp, ?_⟩
  refine ⟨p ^ (n - 1), ?_⟩
  have hs : (n - 1).succ = n := by omega
  rw [Nat.mul_comm, ← Nat.pow_succ, hs]
```

これはかなり良い定理です。

意味は：

> 正の素数冪行 `p^n` では、support prime `p` は行番号 `p^n` 自身から birth している。

`RowBirthPrime (p ^ n) p` の定義は：

```lean
InnerRowSupportPrime (p ^ n) p ∧ p ∣ p ^ n
```

です。

前半はすでに：

```lean
prime_power_innerRowSupportPrime hp
```

で作れます。

後半は：

```lean
p ∣ p ^ n
```

を示す必要があります。

そのために、

```lean
refine ⟨p ^ (n - 1), ?_⟩
```

としています。

これは可除性の定義：

```lean
p ∣ p ^ n
```

を展開して、

```lean
∃ c, p ^ n = p * c
```

を作っている形です。

ここでは商として、

```lean
c = p ^ (n - 1)
```

を選んでいます。

つまり数学的には：

```text
p^n = p * p^(n-1)
```

です。

残りは Lean にこの等式を認識させる部分です。

```lean
have hs : (n - 1).succ = n := by omega
```

`hn : 0 < n` があるので、

```lean
(n - 1) + 1 = n
```

を `omega` で示しています。

Lean の `.succ` は `+ 1` です。

そして、

```lean
rw [Nat.mul_comm, ← Nat.pow_succ, hs]
```

で、

```lean
p * p^(n-1)
```

を掛け算交換して、

```lean
p^(n-1) * p
```

にし、

```lean
← Nat.pow_succ
```

で、

```lean
p^(n-1) * p = p^((n-1).succ)
```

にし、

```lean
hs
```

で、

```lean
p^((n-1).succ) = p^n
```

へ変形しています。

---

## ここはもっと短くできるかも

mathlib によっては、次の形でも通る可能性があります。

```lean
exact dvd_pow_self p hn
```

または類似の補題があるかもしれません。

ただし、今の証明は明示的で安定しています。初心者向けにはむしろ分かりやすいです。

---

# 6. prime_power_rowSupport

```lean
theorem prime_power_rowSupport
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    PrimePowerRowSupport p n :=
  ⟨hp, hn, prime_power_innerRowSupportPrime hp⟩
```

これはパッケージ化定理です。

`PrimePowerRowSupport p n` は：

```lean
p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

なので、必要な3つを並べています。

```lean
hp
hn
prime_power_innerRowSupportPrime hp
```

です。

---

# 7. padicValNat_choose_prime_pow

```lean
theorem padicValNat_choose_prime_pow
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k := by
  have hfac := Nat.factorization_choose_prime_pow hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac
```

ここから後半です。
前半は「Beam に `p` が少なくとも1本通る」でした。

後半は、

> Beam 係数に `p` が何本通っているか

を測っています。

`padicValNat p x` は、

```text
x に含まれる p の指数
```

です。

たとえば、

```text
padicValNat 2 40 = 3
```

なぜなら、

```text
40 = 2^3 * 5
```

だからです。

この定理の意味は：

```text
v_p( binom(p^n, k) ) = n - v_p(k)
```

です。

これはかなり強いです。

例えば `k` が `p` で割れないなら、

```text
v_p(k) = 0
```

なので、

```text
v_p( binom(p^n,k) ) = n
```

つまり、

```text
p^n ∣ binom(p^n,k)
```

です。

---

## 証明の中身

```lean
have hfac := Nat.factorization_choose_prime_pow hp hkn hk0
```

mathlib の定理を持ってきています。

これは `Nat.factorization` 形式の定理です。

`Nat.factorization x p` は、自然数 `x` の素因数分解における `p` の指数です。

DkMath 側では同じものを `padicValNat` として使いたいので、

```lean
rw [Nat.factorization_def ...] at hfac
```

で書き換えています。

```lean
Nat.factorization_def (Nat.choose (p ^ n) k) hp
Nat.factorization_def k hp
```

により、

```lean
Nat.factorization (...) p
```

を

```lean
padicValNat p (...)
```

へ変換しているわけです。

---

# 8. padicValNat_choose_prime_pow_add_index

```lean
theorem padicValNat_choose_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n := by
  have hfac := Nat.factorization_choose_prime_pow_add_factorization hp hkn hk0
  rw [Nat.factorization_def (Nat.choose (p ^ n) k) hp,
    Nat.factorization_def k hp] at hfac
  exact hfac
```

これは前の定理の加法版です。

意味は：

```text
v_p( binom(p^n,k) ) + v_p(k) = n
```

です。

宇宙式の Beam 係数について言うなら：

> Beam 係数が持つ p-support と、index `k` が持つ p-support を足すと、ちょうど row exponent `n` になる。

これはとてもきれいです。

```text
coefficient support + index support = row support
```

という保存則になっています。

---

## 例

`p = 2`, `n = 3`、つまり行 `8` を見るとします。

`k = 2` なら、

```text
v_2(k) = 1
```

なので、

```text
v_2(choose(8,2)) = 3 - 1 = 2
```

実際、

```text
choose(8,2) = 28 = 2^2 * 7
```

です。

`k = 3` なら、

```text
v_2(k) = 0
```

なので、

```text
v_2(choose(8,3)) = 3
```

実際、

```text
choose(8,3) = 56 = 2^3 * 7
```

です。

---

# 9. prime_power_pow_dvd_choose_of_padicValNat_index

```lean
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k := by
  have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
  have hvchoose :
      padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k :=
    padicValNat_choose_prime_pow hp hkn hk0
  have hr_le : r ≤ padicValNat p (Nat.choose (p ^ n) k) := by
    rw [hvchoose]
    omega
  exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne r).mp hr_le
```

これは実用フィルターです。

意味は：

> もし `r + v_p(k) ≤ n` なら、`p^r` は `choose(p^n,k)` を割る。

前の保存則：

```text
v_p(choose(p^n,k)) = n - v_p(k)
```

から、もし

```text
r ≤ n - v_p(k)
```

なら、

```text
p^r ∣ choose(p^n,k)
```

です。

仮定 `hr` は、

```lean
r + padicValNat p k ≤ n
```

なので、まさに

```text
r ≤ n - v_p(k)
```

を意味しています。

---

## 証明の流れ

まず、

```lean
have hchoose_ne : Nat.choose (p ^ n) k ≠ 0 := Nat.choose_ne_zero hkn
```

二項係数が 0 ではないことを示しています。

`Nat.choose_ne_zero hkn` は、

```lean
k ≤ p ^ n → Nat.choose (p ^ n) k ≠ 0
```

です。

次に、

```lean
have hvchoose :
    padicValNat p (Nat.choose (p ^ n) k) = n - padicValNat p k :=
  padicValNat_choose_prime_pow hp hkn hk0
```

で、p 進評価の公式を使います。

次に、

```lean
have hr_le : r ≤ padicValNat p (Nat.choose (p ^ n) k) := by
  rw [hvchoose]
  omega
```

`hr` から、

```lean
r ≤ n - padicValNat p k
```

を `omega` で出しています。

最後に、

```lean
exact (DkMath.ABC.padicValNat_le_iff_dvd hp hchoose_ne r).mp hr_le
```

ここが DkMath 側の p 進評価 API です。

おそらく定理は：

```lean
padicValNat_le_iff_dvd :
  r ≤ padicValNat p x ↔ p ^ r ∣ x
```

のような形です。

それを `.mp` 方向で使って、

```lean
r ≤ v_p(x)
```

から、

```lean
p^r ∣ x
```

を得ています。

---

# 10. prime_power_dvd_choose_of_not_dvd_index

```lean
theorem prime_power_dvd_choose_of_not_dvd_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k := by
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0).mpr hpk
  exact prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 (by omega)
```

これは前の定理の特別版です。

意味は：

> `k` が `p` で割れないなら、`choose(p^n,k)` は `p^n` で割れる。

つまり index `k` が p-support を持っていない場合、row exponent `n` が全部 coefficient 側に乗る、ということです。

保存則で見ると：

```text
v_p(choose(p^n,k)) + v_p(k) = n
```

`p ∤ k` なら、

```text
v_p(k) = 0
```

なので、

```text
v_p(choose(p^n,k)) = n
```

したがって、

```text
p^n ∣ choose(p^n,k)
```

です。

---

## 証明

```lean
have hvk : padicValNat p k = 0 :=
  (DkMath.ABC.padicValNat_eq_zero_iff hp hk0).mpr hpk
```

これは、

```lean
padicValNat p k = 0 ↔ ¬ p ∣ k
```

のような定理を使っています。

`.mpr` は右から左方向です。

```lean
hpk : ¬ p ∣ k
```

から、

```lean
padicValNat p k = 0
```

を得ています。

最後に、

```lean
exact prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 (by omega)
```

前の一般定理を使います。

このとき `r = n` と推論されます。

必要な条件は：

```lean
n + padicValNat p k ≤ n
```

ですが、`hvk : padicValNat p k = 0` があるので、`omega` が解きます。

---

# 11. samples

```lean
section samples
```

ここは API 使用例です。

---

## sample 1

```lean
example {p n : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime (p ^ n) p :=
  prime_power_innerRowSupportPrime hp
```

素数 `p` なら、行 `p^n` の Beam に `p` が通る。

---

## sample 2

```lean
example {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hpk : ¬ p ∣ k) :
    p ^ n ∣ Nat.choose (p ^ n) k :=
  prime_power_dvd_choose_of_not_dvd_index hp hkn hk0 hpk
```

index `k` が p-unit、つまり `p` で割れないなら、係数側に `p^n` が全部乗る。

宇宙式風には：

> Beam の `k` 番目の項で、index が p-support を持たないとき、係数が full row support `p^n` を持つ。

---

## sample 3

```lean
example {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k :=
  prime_power_pow_dvd_choose_of_padicValNat_index hp hkn hk0 hr
```

一般フィルターです。

`k` 側がどれだけ `p` を持っているかに応じて、係数側に最低どれだけ `p^r` が残るかを判断します。

---

# 12. 宇宙式との対応まとめ

このファイルを宇宙式で読むと：

```text
Big = Core + Beam + Gap
```

行番号：

```text
d = p^n
```

です。

すると：

```text
Big = (x + u)^(p^n)
Core = x^(p^n)
Gap = u^(p^n)
Beam = Σ inner terms
```

このファイルの前半は：

```text
Beam の全係数は少なくとも p で割れる
```

つまり、

```text
Big = Core + p * BeamCore + Gap
```

を支える係数定理。

後半はもっと強く：

```text
Beam の k 番目係数に含まれる p の指数は n - v_p(k)
```

を言っています。

つまり、

```text
Beam coefficient support + index support = row exponent
```

です。

これはかなりきれいな保存則です。

---

# 13. 前ファイルとの関係

前ファイル：

```lean
prime_allInnerChooseDivisible_self
```

は、

```text
row p
```

専用でした。

今回：

```lean
prime_power_allInnerChooseDivisible
```

は、

```text
row p^n
```

です。

つまり拡張関係はこうです。

```text
素数行 p
  ↓
素数冪行 p^n
```

さらに：

```text
割れるかどうか
  ↓
何乗まで割れるか
```

に進んでいます。

---

# 14. コメントしたい注意点

## `prime_power_innerRowSupportPrime` は `n = 0` でも成立する

```lean
InnerRowSupportPrime (p ^ 0) p
```

つまり、

```lean
InnerRowSupportPrime 1 p
```

も成立します。

これは内側係数が存在しないため、空虚に真です。

数学的には問題ありませんが、宇宙式的に「素数冪行」と呼ぶなら、実際には `0 < n` を付けた `PrimePowerRowSupport` や `prime_power_rowBirthPrime` を使う方が自然です。

---

## `PrimePowerRowSupport` は `p.Prime` が重複する

```lean
p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

`InnerRowSupportPrime` の中にすでに `p.Prime` があります。

設計としては悪くないです。
ただ、完全に重複を避けたいなら：

```lean
def PrimePowerRowSupport (p n : ℕ) : Prop :=
  0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

でもよいです。

ただし今の定義の方が、見るだけで「これは prime-power の話だ」と分かりやすい利点があります。

---

## `hkn : k ≤ p ^ n` と「inner index」

後半の Kummer 系定理では、

```lean
hkn : k ≤ p ^ n
hk0 : k ≠ 0
```

です。

つまり `k = p^n` も許しています。

その場合、

```lean
Nat.choose (p ^ n) (p ^ n) = 1
```

で、

```lean
padicValNat p 1 = 0
```

になります。

公式は：

```text
v_p(choose(p^n,p^n)) = n - v_p(p^n) = n - n = 0
```

なので成立します。

一方、前半の `AllInnerChooseDivisible` は：

```lean
0 < k → k < p ^ n
```

なので、端 `k = p^n` は除外しています。

この違いはちゃんと意味があります。

---

# 15. このファイルの一言まとめ

この実装は、

> 素数冪行 `p^n` の Beam は、少なくとも `p` で消える。
> さらに `k` 番目係数の p 進厚みは `n - v_p(k)` で正確に測れる。
> よって index 側にない p-support は coefficient 側に移る。

という内容です。

宇宙式の言葉でかなり短く言うなら：

```text
row p^n:
  Beam carries p-support.

k-th Beam coefficient:
  coefficient-support + index-support = row-support.
```

つまり、

```text
v_p(BeamCoeff_k) + v_p(k) = n
```

です。

これは前回の「mod p で Beam が消える」から一段進んで、

```text
Beam がどの p^r レベルで消えるかを測る層
```

になっています。
