# p.Prime 自前実装の考察

## 考察まとめ

👩‍🎓 よし、ここまでの考察を整理します。
テーマはかなりはっきりしてきました。

# 1. 出発点：パスカル三角形の内側係数

Lean ファイルでは、まずこれを定義していました。

```lean
def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k
```

意味は、

> 第 `d` 行の内側の二項係数が、全部 `m` で割れる

です。

ここでいう内側は、

```lean
0 < k ∧ k < d
```

を満たす `k` です。

つまり端の

```lean
Nat.choose d 0 = 1
Nat.choose d d = 1
```

は見ません。

---

# 2. 宇宙式との対応

宇宙式は本来、

```text
Big = Core + Beam + Gap
```

という構成。

対応はこうです。

```text
Big  := (x + u)^d
Core := x^d
Beam := ∑_{1 ≤ k < d} binom(d,k) x^(d-k) u^k
Gap  := u^d
```

つまり、

```text
(x + u)^d
= x^d
+ ∑_{k=1}^{d-1} binom(d,k) x^(d-k) u^k
+ u^d
```

です。

ここで Lean の

```lean
AllInnerChooseDivisible d m
```

が見ているのは、まさに **Beam の係数部分** です。

---

# 3. 素数行では Beam が p で染まる

素数 `p` について、mathlib の定理を使って、

```lean
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p
```

を証明していました。

数学的には、

```text
p が素数なら、0 < k < p に対して p ∣ binom(p,k)
```

です。

宇宙式に翻訳すると、

```text
(x + u)^p
= x^p + Beam + u^p
```

の `Beam` の各係数が `p` で割れる。

したがって、

```text
Beam = p * BeamCore
```

と見られます。

だから、

```text
Big = Core + p * BeamCore + Gap
```

です。

---

# 4. mod p で Beam が消える

`Beam = p * BeamCore` なので、`mod p` で見ると、

```text
Beam ≡ 0
```

です。

したがって宇宙式は、

```text
Big = Core + Beam + Gap
```

から、`mod p` 観測では、

```text
Big ≡ Core + Gap mod p
```

になります。

つまり、

```text
(x + u)^p ≡ x^p + u^p mod p
```

です。

ここが大事です。

> 素数行では、Beam は存在するが、mod p では消える。

---

# 5. 既存定義の役割

定義は三段階でした。

```lean
AllInnerChooseDivisible d m
```

これは、

> Beam の全係数が `m` で割れる

という観測。

---

```lean
InnerRowSupportPrime d p
```

これは、

```lean
p.Prime ∧ AllInnerChooseDivisible d p
```

なので、

> Beam に素数 `p` の support channel がある

という観測。

---

```lean
RowBirthPrime d p
```

これは、

```lean
InnerRowSupportPrime d p ∧ p ∣ d
```

なので、

> Beam に現れる support prime `p` が、行番号 `d` 自身から来ている

という観測。

宇宙式風に言うなら、

```text
RowBirthPrime d p
```

は、

> 第 `d` 宇宙式の Beam に、行番号 `d` 由来の素数チャンネル `p` が通っている

という性質です。

---

# 6. 「d が素数」とはまだ言っていない

ここが設計上かなり重要です。

```lean
RowBirthPrime d p
```

があっても、まだ

```lean
d.Prime
```

とは言っていません。

なぜなら、

```text
d = p^n
```

のような素数冪でも、`p` が Beam に現れる可能性があるからです。

つまり現在の定義は、

```text
d が素数である
```

を直接判定するものではなく、

```text
Beam にどんな可除性が現れているかを観測する分析器
```

です。

---

# 7. d = p^n フィルター

次に出てきた考察が、

```text
d = p^n
```

というフィルターです。

これは、

> 行番号 `d` が、ある基底 `p` の正冪である

という条件。

Lean 的には例えば、

```lean
def IsPositivePowerOf (d p : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ d = p ^ n
```

と置けます。

ここから出せる基本事実は、

```text
0 < n ∧ d = p^n なら p ∣ d
```

です。

ただし、これだけでは `p.Prime` は出ません。

たとえば、

```text
d = 12^3
```

なら `p = 12` は素数ではありません。

なので、

```text
d = p^n
```

は「p が d の冪底である」ことしか言いません。

---

# 8. p.Prime を使えない場合：分解不能性

`p.Prime` を直接使えない場合、代わりに必要になるのは、

```text
p = a * b なら、a = 1 または b = 1
```

という性質です。

これは「素数性」そのものではなく、**非自明分解できない**という性質。

Lean 的には例えば、

```lean
def FactorRigid (p : ℕ) : Prop :=
  1 < p ∧ ∀ a b : ℕ, p = a * b → a = 1 ∨ b = 1
```

と置けます。

これは、

> `p` の因数分解は `1 * p` または `p * 1` しかない

という意味です。

ここで出てきた感覚が、

```text
p = 1 * 素数構造
```

という見方です。

より正確には、

```text
p の約数は 1 と p だけ
```

です。

---

# 9. 可除性とは何か

可除性は、

```lean
a ∣ p
```

と書き、

意味は、

```text
p = a * q となる q が存在する
```

です。

つまり割り切りは、因数分解の言葉です。

だから、

```text
p が非自明分解できない
```

とは、

```text
p = a * q
```

と書けるとき、必ず

```text
a = 1 または q = 1
```

になる、ということです。

---

# 10. 冪の差因数分解

次に出てきたのが、

```text
a^n - b^n
```

の因数分解です。

標準形は、

```text
a^n - b^n
= (a - b) * (a^(n-1) + a^(n-2)b + ... + b^(n-1))
```

です。

ここで、

```text
S := a^(n-1) + a^(n-2)b + ... + b^(n-1)
```

と置くと、

```text
a^n - b^n = (a - b) * S
```

です。

---

# 11. 冪差が p になる場合の分岐

もし、

```text
a^n - b^n = p
```

で、`p` が分解不能なら、

```text
p = (a - b) * S
```

なので、可能性は基本的に二つです。

```text
a - b = 1, S = p
```

または

```text
a - b = p, S = 1
```

です。

しかし `n ≥ 2`, `a > b ≥ 0`, `p > 1` なら、

```text
S = 1
```

はほぼ不可能です。

なぜなら `S` は非負項の和で、少なくともそれなりに大きくなるからです。

したがって非自明な場合、残るのは、

```text
a - b = 1
```

です。

つまり、

> 分解不能な `p` が冪差として出るなら、差は 1 に押し込まれる。

という見方が出ました。

---

# 12. 「冪の差因数分解表現が不可能」という視点

ここから、

```text
p が素数である
```

を直接言うのではなく、

```text
p は非自明な冪差因数分解として表せない
```

を主体にする案が出ました。

これはかなり良い分析器です。

例えば、

```lean
def PowerDiffRep (p a b n : ℕ) : Prop :=
  b < a ∧ p = a ^ n - b ^ n
```

さらに非自明なギャップを要求して、

```lean
def NontrivialGapPowerDiff (p : ℕ) : Prop :=
  ∃ a b n : ℕ,
    1 < n ∧ b < a ∧ 1 < a - b ∧
    p = a ^ n - b ^ n
```

とする。

このとき目標は、

```lean
FactorRigid p → ¬ NontrivialGapPowerDiff p
```

のような形です。

意味は、

> 分解不能な数 `p` は、差 `a-b > 1` を持つ非自明な冪差では表せない。

です。

---

# 13. 多項式因子を 1 にする話

冪差因数分解では、

```text
a^n - b^n = (a-b) * S
```

でした。

もし、

```text
a-b = p
```

として、

```text
a^n - b^n = p
```

にしたいなら、

```text
S = 1
```

が必要です。

でも `S` は和なので、普通は `1` になりません。

そこで出てきたのが、

```text
(1+2+1)=4
(1+2+1)/2=2
(1+2+1)/4=1
```

という正規化トリックです。

これは確かに値を 1 にできます。

でもこれは、

```text
S = 1
```

ではなく、

```text
S / S = 1
```

に近い。

つまり外から分母を持ち込んでいます。

自然数の可除性・因数分解の世界では、これは構造を壊します。

だから分析器として有効なのは、

```text
S を割って 1 にする
```

ではなく、

```text
S そのものが 1 になれるか
```

です。

そして非自明な冪差では、ほぼなれない。

---

# 14. 全体像

ここまでの考察は、次のように整理できます。

```text
宇宙式:
  Big = Core + Beam + Gap

二項係数分析:
  Beam の係数が何で割れるかを見る

素数行:
  p.Prime なら Beam は p で割れる

mod p 観測:
  Beam が消えて Big ≡ Core + Gap

RowBirthPrime:
  Beam に現れる p が行番号 d 由来であることを記録

d = p^n フィルター:
  d が p の冪であることを見る
  ただし p.Prime は出ない

p.Prime を使わない場合:
  FactorRigid、つまり非自明分解不能性を使う

冪差分析:
  a^n - b^n = (a-b) * S
  p が分解不能なら、因子の片方は 1 でなければならない

非自明冪差不可能性:
  a-b > 1 かつ n ≥ 2 なら S > 1
  よって p そのものにはなりにくい
```

---

# 15. 今後の Lean 設計案

次に作るなら、このあたりが自然です。

```lean
def IsPositivePowerOf (d p : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ d = p ^ n
```

```lean
def FactorRigid (p : ℕ) : Prop :=
  1 < p ∧ ∀ a b : ℕ, p = a * b → a = 1 ∨ b = 1
```

```lean
def PowerDiffRep (p a b n : ℕ) : Prop :=
  b < a ∧ p = a ^ n - b ^ n
```

```lean
def NontrivialGapPowerDiff (p : ℕ) : Prop :=
  ∃ a b n : ℕ,
    1 < n ∧ b < a ∧ 1 < a - b ∧
    p = a ^ n - b ^ n
```

そして狙う方向は、

```lean
FactorRigid p → ¬ NontrivialGapPowerDiff p
```

です。

ただし `ℕ` の引き算は扱いにくいので、冪差は `ℤ` に移す方が安全です。

---

まとめると、今回の考察の核はこれです。

> 宇宙式では Beam が内側二項係数の領域。
> 素数行では Beam は p で割れ、mod p では消える。
> ただし p.Prime を使わないなら、代わりに「非自明分解できない」という FactorRigid を導入する。
> さらに冪差因数分解を見ると、非自明な冪差が分解不能な p になるには、因子の片方が 1 になる必要がある。
> その不可能性を分析器として使える。
