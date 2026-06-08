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

---

## p^n フィルター

ここからですよねぇ。
Kummerの定理、p^n フィルター。
可除性構造のみで素数の原始を捕まえられるか。

はい、ここが Kummer 入口です。

可除性構造だけで見える範囲はかなり強いですが、整理するとこうです。

- `AllInnerChooseDivisible d p` は「段 `d` の内側係数がすべて `p` を含む」という支持構造を捕まえる。
- ただしこれは `d = p` だけでなく `d = p^n` でも成立する。
- したがって「素数段そのもの」を捕まえるには不足。
- しかし「段 `d` が `p` 系の素数冪段である」ことを捕まえる方向には非常に自然。

ここで Kummer / factorization が効きます。

```lean
Nat.factorization_choose_prime_pow
```

の形で、概念的には

```text
v_p (choose (p^n) k) = n - v_p(k)
```

が使えます。

つまり `0 < k < p^n` なら `v_p(k) < n` なので、内側係数は必ず `p` で割れる。
さらに `p ∤ k` なら `v_p(k) = 0` なので、

```text
p^n ∣ choose (p^n) k
```

まで見える。

ここが `p^n` フィルターですね。

Lean 実装としては次の一手がよさそうです。

```lean
def PrimePowerRowSupport (d p : ℕ) : Prop :=
  ∃ n, 0 < n ∧ d = p ^ n ∧ InnerRowSupportPrime d p
```

または、より直接に

```lean
def PrimePowerInnerFilter (p n : ℕ) : Prop :=
  p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

そして最初の定理はこれです。

```lean
theorem prime_power_innerRowSupportPrime
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    InnerRowSupportPrime (p ^ n) p := ...
```

この定理が固定できると、現在の `RowBirthPrime` は「素数段」から「素数冪段の支持」へ自然に拡張できます。

結論としては、可除性だけで「原始的な素数の発生源」はかなり捕まえられます。ただし `d = p` と `d = p^n` を分離するには、単なる `p ∣ choose d k` では足りず、`p^n` 可除性の階層、つまり factorization / valuation を「可除性の段階構造」として導入するのが Lean らしい道筋です。

入れた主な補題は次です。

- `prime_power_innerRowSupportPrime`
  `p^n` 段の内側係数がすべて `p` を支持することを固定。
- `prime_power_rowBirthPrime`
  `0 < n` なら `p ∣ p^n` なので `RowBirthPrime (p^n) p` へ接続。
- `padicValNat_choose_prime_pow`
  mathlib の Kummer/factorization 形を `padicValNat` 形に変換。
- `prime_power_dvd_choose_of_not_dvd_index`
  `¬ p ∣ k` なら `p^n ∣ choose (p^n) k`。ここが「p^n フィルター」の最初の精密層です。

ここからどう攻めるか？

攻め筋は `prime_power_dvd_choose_of_not_dvd_index` を特殊例として、もっと一般の **valuation filter** に昇格するのがよいです。

今ある定理は：

```lean
¬ p ∣ k → p ^ n ∣ Nat.choose (p ^ n) k
```

つまり `v_p(k) = 0` の層だけを見ています。次はこれを

```text
v_p(choose (p^n) k) = n - v_p(k)
```

から直接、

```lean
r + padicValNat p k ≤ n →
p ^ r ∣ Nat.choose (p ^ n) k
```

へ一般化するのが本筋です。

名前は例えば：

```lean
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k
```

これが立つと、全部が統一されます。

- `r = 1`
  内側係数は `p` で割れる、つまり `InnerRowSupportPrime`
- `r = n` かつ `padicValNat p k = 0`
  既存の `prime_power_dvd_choose_of_not_dvd_index`
- `k` が `p^s` を含む場合
  係数側には `p^(n-s)` が残る

これで「p^n フィルター」が、単なる yes/no 可除性ではなく、層構造として使えます。

その次にやるべきは weighted 側への持ち上げです。

```lean
p ^ r ∣ Nat.choose (p ^ n) k →
p ^ r ∣ weightedBinomialTerm (p ^ n) k x u
```

これは乗算で保たれるので軽いです。ここまで行くと、

```text
Pascal の加法生成
→ binomial coefficient の p-adic 層
→ weighted term
→ GN / BodyGapKernelSplit
```

の橋ができます。

なので次の実装チェックポイントはこれです。

1. `prime_power_pow_dvd_choose_of_padicValNat_index`
2. `prime_power_padicValNat_choose_add_index`

   ```lean
   padicValNat p (choose (p^n) k) + padicValNat p k = n
   ```

3. weighted term への `p^r` 可除性リフト

ここを固めると、「素数原始を可除性だけで観測する」道具としてかなり強くなります。

---

入れた主な補題は次です。

- `prime_power_innerRowSupportPrime`
  `p^n` 段の内側係数がすべて `p` を支持することを固定。
- `prime_power_rowBirthPrime`
  `0 < n` なら `p ∣ p^n` なので `RowBirthPrime (p^n) p` へ接続。
- `padicValNat_choose_prime_pow`
  mathlib の Kummer/factorization 形を `padicValNat` 形に変換。
- `prime_power_dvd_choose_of_not_dvd_index`
  `¬ p ∣ k` なら `p^n ∣ choose (p^n) k`。ここが「p^n フィルター」の最初の精密層です。

## p^n 篩

ここで追加する「篩」は、**Beam の p-adic 高さを見る層**ですね。

既存ファイルの流れに足すなら、こんな設計が自然です。

```lean
/--
All inner coefficients in row `d` have exactly the same `p`-adic height `h`.

This is a stricter beam filter than mere divisibility: not only does `p`
divide every inner coefficient, the visible `p`-support has uniform height.
-/
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h
```

意味は：

```text
第 d 行の Beam 係数すべてについて、
p の指数がちょうど h で揃っている
```

です。

---

素数行では高さ `1` に揃います。

```lean
/--
Prime rows have uniform beam height `1` at their own prime.
-/
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 := by
  intro k hk0 hkp
  have hkp_le : k ≤ p := le_of_lt hkp
  have hk0_ne : k ≠ 0 := hk0.ne'
  have hval :
      padicValNat p (Nat.choose (p ^ 1) k) =
        1 - padicValNat p k := by
    simpa using
      (padicValNat_choose_prime_pow (p := p) (n := 1) (k := k)
        hp (by simpa using hkp_le) hk0_ne)
  have hpk : ¬ p ∣ k := by
    intro hdiv
    rcases hdiv with ⟨c, hc⟩
    have hp_le_k : p ≤ k := by
      rw [hc]
      -- since p ∣ k and k ≠ 0, quotient c is positive
      have hcpos : 0 < c := by
        by_contra hc0
        have hc_eq : c = 0 := Nat.eq_zero_of_not_pos hc0
        rw [hc_eq, mul_zero] at hc
        exact hk0_ne hc.symm
      exact Nat.le_mul_of_pos_right hcpos
    exact not_le_of_gt hkp hp_le_k
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0_ne).mpr hpk
  rw [hval, hvk]
  norm_num
```

ただ、ここはもっと簡単にいける可能性があります。
`0 < k < p` から `¬ p ∣ k` を作る部分が少し長いです。

---

素数冪行の濃淡そのものは、すでにこの定理で表せています。

```lean
theorem padicValNat_choose_prime_pow_add_index
    {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n
```

これを「篩」として名前付けするなら、こういう定義も良いです。

```lean
/--
Prime-power beam height law.

The `p`-height of the `k`-th beam coefficient and the `p`-height already
present in the index `k` add up to the row exponent.
-/
def PrimePowerBeamHeightLaw (p n : ℕ) : Prop :=
  ∀ k, 0 < k → k < p ^ n →
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n
```

そして定理：

```lean
/--
Prime-power rows satisfy the beam height conservation law.
-/
theorem prime_power_beamHeightLaw
    {p n : ℕ} (hp : p.Prime) :
    PrimePowerBeamHeightLaw p n := by
  intro k hk0 hkp
  exact padicValNat_choose_prime_pow_add_index
    hp (le_of_lt hkp) hk0.ne'
```

これはかなり綺麗です。

---

さらに、素数行はこの法則の `n = 1` で、しかも内側 index は `p` を持たないので、高さが全部 `1` に揃う、という位置づけになります。

構造としてはこうです。

```text
AllInnerChooseDivisible d p
  Beam に p が最低1本通る

UniformBeamHeight d p h
  Beam の p 高さが h で揃う

PrimePowerBeamHeightLaw p n
  row p^n では
  Beam係数高さ + index高さ = n
```

---

追加場所は、`BinomialPrimePower.lean` の `padicValNat_choose_prime_pow_add_index` の直後がよさそうです。

おすすめ追加コードはまずこの2つです。

```lean
/--
All inner coefficients in row `d` have exactly the same `p`-adic height `h`.

This is a stricter beam filter than mere divisibility: not only does `p`
divide every inner coefficient, the visible `p`-support has uniform height.
-/
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h

/--
Prime-power beam height law.

The `p`-height of the `k`-th beam coefficient and the `p`-height already
present in the index `k` add up to the row exponent.
-/
def PrimePowerBeamHeightLaw (p n : ℕ) : Prop :=
  ∀ k, 0 < k → k < p ^ n →
    padicValNat p (Nat.choose (p ^ n) k) + padicValNat p k = n

/--
Prime-power rows satisfy the beam height conservation law.
-/
theorem prime_power_beamHeightLaw
    {p n : ℕ} (hp : p.Prime) :
    PrimePowerBeamHeightLaw p n := by
  intro k hk0 hkp
  exact padicValNat_choose_prime_pow_add_index
    hp (le_of_lt hkp) hk0.ne'
```

これは既存の定理だけで通るはずです。

---

そして「素数行では高さが揃う」は、次のチェックポイントで追加するとよいです。

```lean
/--
Prime rows have uniform beam height `1` at their own prime.
-/
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1 := by
  intro k hk0 hkp
  have hlaw :
      padicValNat p (Nat.choose (p ^ 1) k) + padicValNat p k = 1 :=
    padicValNat_choose_prime_pow_add_index
      hp (by simpa using le_of_lt hkp) hk0.ne'
  have hnot : ¬ p ∣ k := by
    intro hpk
    have hp_le_k : p ≤ k := Nat.Prime.le_of_dvd hp hk0.ne' hpk
    exact not_le_of_gt hkp hp_le_k
  have hvk : padicValNat p k = 0 :=
    (DkMath.ABC.padicValNat_eq_zero_iff hp hk0.ne').mpr hnot
  rw [hvk, add_zero] at hlaw
  simpa using hlaw
```

ここで使っている

```lean
Nat.Prime.le_of_dvd
```

が環境で通らない場合は、さっきのように `rcases hpk` で手作りできます。

---

この篩を入れると、分類がこうなります。

```text
Row p:
  UniformBeamHeight p p 1

Row p^n:
  PrimePowerBeamHeightLaw p n
  高さは n - v_p(k)

Row 6, 36 など:
  そもそも単一 p が全 Beam を貫通しない
```

つまり新しい篩は、

> Beam に support があるか
> その support の高さが揃っているか
> 素数冪として濃淡法則を持つか

を見る層になります。

---

追加内容：

```lean
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h
```

```lean
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1
```

証明は `padicValNat_choose_prime_pow` の `n = 1` 特殊化を使っています。`0 < k < p` なので `p ∤ k`、よって `padicValNat p k = 0`。したがって Beam 側は `1 - 0 = 1` です。

### 素数定理への橋

はい。ここからは「既存素数定理とつなぐ橋」を作りながら、足りないものを露出させる段階です。

今の `UniformBeamHeight` は、既存定理へかなり自然に接続できます。

まず直結する既存定理はこのあたりです。

```lean
Nat.Prime.dvd_choose_self
Nat.Prime.dvd_choose_pow
Nat.Prime.dvd_choose_pow_iff
Nat.factorization_choose_prime_pow
padicValNat_choose
```

DkMath 側では特にこの系列と相性がよいです。

```lean
DkMath.ABC.padicValNat_le_iff_dvd
DkMath.ABC.padicValNat_eq_zero_iff
DkMath.NumberTheory.UniqueFactorizationGN.factorization_eq_of_prime_pow_dvd_iff
```

攻め方は次の順がよさそうです。

1. `UniformBeamHeight` から既存の可除性観測へ戻す橋

```lean
UniformBeamHeight d p h
0 < h
→ AllInnerChooseDivisible d p
```

これは「高さが正なら `p` で割れる」という基本橋です。
`padicValNat_le_iff_dvd` でほぼそのまま行けます。

1. 素数行の高さ定理から既存構造へ接続

```lean
prime_uniformBeamHeight_self
→ prime_allInnerChooseDivisible_self
→ prime_innerRowSupportPrime_self
```

つまり、新しい高さ観測が、既存の `InnerRowSupportPrime` より強いことを明示できます。

1. `p^n` 行では「全 Beam 一様」ではなく「単位 index 上で一様」

ここが重要です。

`p^n` 行では一般に

```text
v_p(choose(p^n, k)) = n - v_p(k)
```

なので、全 inner coefficient が高さ `n` で揃うわけではありません。
揃うのは `¬ p ∣ k` の層です。

だから次に必要なのは、おそらくこれです。

```lean
def FilteredBeamHeight (d p h : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ k, 0 < k → k < d → P k →
    padicValNat p (Nat.choose d k) = h
```

そして：

```lean
theorem prime_power_unitFilteredBeamHeight
    {p n : ℕ} (hp : p.Prime) :
    FilteredBeamHeight (p ^ n) p n (fun k => ¬ p ∣ k)
```

これが本当の `p^n` 篩です。

まとめると、足りない要素はこの3つです。

- `UniformBeamHeight → AllInnerChooseDivisible` の下降橋
- `FilteredBeamHeight` の定義
- `p^n` 行の unit-index filtered height 定理

ここまで作ると、Beam の観測層が

```text
可除性
→ p-adic 高さ
→ filtered p^n 高さ
```

へきれいに分かれます。既存素数定理との橋として十分強いです。

---

d = p : p-height = 1 が何故、成立するのか。
何故高さが１で並ぶのか？
その原理追求からの素数境界の条件を抽出すべきか？

はい、抽出すべきです。今見えているのは単なる事実ではなく、かなり綺麗な「素数境界原理」です。

原理はこう分解できます。

```text
d < p  : p-height = 0
d = p  : p-height = 1
```

なぜ `d = p` で高さが 1 に揃うかというと、構造的には：

```text
k * choose(p, k) = p * choose(p - 1, k - 1)
```

だからです。

`0 < k < p` なら `p ∤ k`。
さらに `p - 1 < p` なので、前段 `p - 1` の係数には `p` が出ない。
つまり右辺には `p` がちょうど 1 個だけあり、それが `choose(p,k)` 側へ移る。

```text
v_p(k) = 0
v_p(choose(p - 1, k - 1)) = 0
v_p(p) = 1

よって
v_p(choose(p,k)) = 1
```

これが「高さ 1 で並ぶ」理由です。

今の Lean 実装では Kummer 経由で証明していますが、概念としては次の定義を切り出すとよさそうです。

```lean
def BeamBirthBoundary (p : ℕ) : Prop :=
  (∀ d, d < p → UniformBeamHeight d p 0) ∧
  UniformBeamHeight p p 1
```

そしてまず：

```lean
theorem prime_beamBirthBoundary
    {p : ℕ} (hp : p.Prime) :
    BeamBirthBoundary p
```

これは既存の

```lean
below_prime_uniformBeamHeight_zero
prime_uniformBeamHeight_self
```

だけで即通るはずです。

その次に欲しい橋は逆向きです。

```lean
theorem prime_of_beamBirthBoundary
    {p : ℕ} (hp_gt1 : 1 < p)
    (h : BeamBirthBoundary p) :
    p.Prime
```

これは少し重い可能性があります。実質的には古典定理：

```text
n が素数 ⇔ 0 < k < n のすべてで n ∣ choose(n,k)
```

への橋です。

なので次の実装順は：

1. `BeamBirthBoundary` を定義する
2. `p.Prime → BeamBirthBoundary p` を固定する
3. `BeamBirthBoundary p → AllInnerChooseDivisible p p` を出す
4. 逆向き `AllInnerChooseDivisible p p → p.Prime` の既存定理探索、なければ別ファイルで計画化

ここまで行くと、「p 行で初めて p が生まれる」が単なる説明ではなく、Lean の境界定理になります。

### p-1 行の＋１－１の交代和

p となる p 行の前段ｐ－１行が＋１－１の交代和構造になるって話。
これってすべてのｐ－１行で成り立っているのかな？

はい、意味が2通りあります。どちらも重要です。

1つ目、単なる交代和なら任意の正の行で成立します。

```text
Σ (-1)^k * C(n,k) = (1 - 1)^n = 0
```

これは `p - 1` 行に限らず、すべての `n > 0` 行で成り立ちます。

ただし、いま面白いのはたぶんこちらです。

```text
C(p - 1, k) ≡ (-1)^k mod p
```

つまり素数 `p` の直前行 `p - 1` は、mod `p` で

```text
1, -1, 1, -1, ...
```

に見える、という構造です。

例：

```text
p = 5
row 4 = 1, 4, 6, 4, 1
mod 5 = 1, -1, 1, -1, 1
```

これは **素数 `p` に対して成立**します。任意の行で成立するわけではありません。たとえば `p = 6` と見て row `5` を mod `6` で見ると、

```text
1, 5, 10, 10, 5, 1
mod 6 = 1, -1, 4, 4, -1, 1
```

となり、中間が崩れます。

なので Lean 的には次の補題がかなり良い橋になります。

```lean
theorem choose_prime_sub_one_mod
    {p k : ℕ} (hp : p.Prime) (hk : k ≤ p - 1) :
    Nat.choose (p - 1) k ≡ (-1 : ZMod p) ^ k
```

または `ZMod p` 上で：

```lean
((Nat.choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k)
```

これは `p` 行の「全中間係数が p で割れる」の一段前に、`p - 1` 行が **完全な符号交代境界**として現れる、という形です。
かなり良い観測点です。次に実装する価値があります。

### 三角の模様を追う

p 行と p-1 行の対の関係は、これで明確化。
p_0 行から次の p_1 行、 p_1 - 1 行は、いまので OK.

p_0 + 1 行から p_1 行の法則か。
これはきっと三角由来だから、中央項から変化を始めて、次段でサイドへ広がって、最終的に p_1 - 1 行で +1-1 交代和な運動が繰り広げられているように予想される。

ここはある程度大きな素数区間を観測しないと解像度が低いわよねぇ。
数値検証かな。代数構造的にそれ見える？

見えます。代数構造としてはかなりきれいです。

`mod p₁` で Pascal 行を見るなら、各行は有限体 `ZMod p₁` 上の多項式

```lean
(1 + X)^n
```

の係数列です。つまり、`p₀ + 1` 行から `p₁` 行までは

```text
Pₙ(X) = (1 + X)^n  in  F_{p₁}[X]
Pₙ₊₁ = (1 + X) Pₙ
```

という「Pascal flow」です。

そして終端で Frobenius が発動します。

```text
(1 + X)^p₁ = 1 + X^p₁   in F_{p₁}[X]
```

だから `p₁` 行では中間係数が全部消える。
その一段前は

```text
(1 + X)^(p₁ - 1) * (1 + X) = 1 + X^p₁
```

なので、次数 `< p₁` の範囲では

```text
(1 + X)^(p₁ - 1) = 1 - X + X^2 - X^3 + ...
```

となる。今回固定した `PrimePrebirthAlternation` はこの「Frobenius 境界の一段前」です。

なので、`p₀ + 1` から `p₁ - 1` までは、代数的には

```text
(1 + X)^n が Frobenius 境界 (1 + X)^p = 1 + X^p に向かう流れ
```

として見えます。

ただし「中央項から変化し、サイドへ広がる」という模様は、代数的には部分的に見えますが、視覚的な解像度は数値観測が強いです。理由は、端の係数は

```text
C(n,1)=n
C(n,2)=n(n-1)/2
C(n,3)=n(n-1)(n-2)/6
```

のような低次多項式なので動きが読みやすい。一方、中央付近は高次係数なので `mod p` で急に複雑に振る舞う。結果として、中央部の模様が先に「荒れる」ように見える可能性があります。

名前を付けるなら、この層は例えば：

```text
PrimeIntervalPascalFlow
```

または少し概念寄りに：

```text
FrobeniusPrebirthFlow
```

が良さそうです。

次の Lean 実装対象は、数値列そのものよりもまずこれですね。

```lean
def PrimeIntervalPascalFlow (p n : ℕ) : Prop :=
  n < p ∧ -- row n observed modulo p
    True
```

より実用的には、多項式または係数観測として：

```lean
def PascalRowMod (p n k : ℕ) : ZMod p :=
  (Nat.choose n k : ZMod p)
```

そして固定したい核は：

```text
Pₙ₊₁(k) = Pₙ(k-1) + Pₙ(k)
P_p(k) = 0 for 0 < k < p
P_{p-1}(k) = (-1)^k
```

この3点セットです。これで「Pascal 加法流 → Frobenius 境界 → prebirth 交代相」が一本になります。

### 素数ダイヤル

ゼータ関数解析で使ってたんだけど、まだ DkMath では未実装かな。
「素数ダイヤル」という素数周期のダイヤルを仮想創造して、
自然数の素因数の出現をダイヤルの１回転周期の同期として見ていたのね。
それがリーマンゼータ関数の非自明なゼロ点を境に組み合わせの変化が起きている。
つまり、非自明なゼロ点が素数ではなくて、その間が素数と合成数の集合セットみたいな。各素数の寄与率としての観測。始まりは全素数が一斉に揃う。
つまり自然数の無限。そこからすべてのダイアルが、それぞれ素数周期で回転を始めていく。
当然、二度と揃うことはない。
もしも揃ったら、素数無限は成り立たないし、自然数の無限の終着点がある。という事になってしまう。

この観点をパスカルの三角形に応用すると、
そのダイヤルは、段が進むごとに回される。
回る回転角は前段項の和の結果による。
但し、単純でなく log の回転角か。係数の総和からの相対角になるだろう。

１＋２＋１＝４　1/4=0.25
１＋３＋３＋１＝８　1/8=0.125
１＋４＋６＋４＋１＝１６　1/16=0.0625

この観点でも 1/2^n か。

つまり、両端は常に＋１なのだけど、相対的には log 同様、+1 の重みは低くなる。

この１段降りるごとに回転する素数ダイヤルを各項の係数が持っている。
二項係数→素因子の成長→ダイヤルの回転数という観測をする。

これはかなり筋が良い観測モデルです。
DkMath 的には、直接ゼータ解析へ行く前に、Pascal 行の係数を「素数ダイヤル群の状態」として読む層を作るのが自然です。

核になる見方は：

```text
row n:
  C(n,0), C(n,1), ..., C(n,n)

各係数 C(n,k) に対して
  prime p の出現量 = padicValNat p (C(n,k))
```

つまり各項は、素数ごとの高さベクトルを持つ。

```text
C(n,k) ↦ (v₂, v₃, v₅, v₇, ...)
```

これが「素数ダイヤルの回転数」に相当します。

相対重みまで入れるなら、係数総和が `2^n` なので：

```text
relativeWeight(n,k) = C(n,k) / 2^n
```

両端の `1` は絶対値としては常に `1` だけど、相対重みは：

```text
1 / 2^n
```

なので、段が進むほど薄くなる。これはまさに「log 的に寄与率が落ちる」観測ですね。

Lean での第一段階は、実数や log を使わずにこう切るのが良さそうです。

```lean
/-- Prime-dial height of one Pascal coefficient. -/
def pascalPrimeDialHeight (p n k : ℕ) : ℕ :=
  padicValNat p (Nat.choose n k)
```

次に、相対重みはまだ割り算せず、分母付き構造で持つ。

```lean
/-- The raw mass of one Pascal coefficient in row n. -/
def pascalCoeffMass (n k : ℕ) : ℕ :=
  Nat.choose n k

/-- The total mass of row n. -/
def pascalRowMass (n : ℕ) : ℕ :=
  2 ^ n
```

すると観測対象は：

```text
coefficient mass: C(n,k)
row mass: 2^n
prime dial height: v_p(C(n,k))
relative position: C(n,k) / 2^n
```

ここで重要なのは、`padicValNat p (Nat.choose n k)` には既に Kummer/Lucas 系の強い理論があることです。つまり「ダイヤルの回転数」は単なる比喩ではなく、既存定理に接続できる。

Pascal の三角形におけるダイヤル観測は、名前を付けるなら：

```text
PascalPrimeDial
```

または、ゼータとの橋を意識するなら：

```text
PrimeDialMassFlow
```

が良さそうです。

構造としてはこうです。

```text
PascalPrimeDial
  row        : n
  index      : k
  coeff      : C(n,k)
  rowMass    : 2^n
  pHeight    : padicValNat p C(n,k)
```

この層を作ると、今までの

```text
BeamBirthBoundary
PrimePrebirthAlternation
UniformBeamHeight
FilteredBeamHeight
```

が全部「素数ダイヤル観測」の特殊ケースになります。

特に：

```text
p 行:
  すべての中間係数で p-dial が 1 回転

p - 1 行:
  mod p では +1/-1 交代、つまり p-dial 誕生直前の位相境界

p^n 行:
  index が p で割れるかどうかに応じて dial height が変わる
```

これはかなり良い抽象化です。
次に実装するなら、数値実験用ではなく、まず Lean 側に小さく：

```lean
pascalPrimeDialHeight
pascalRowMass
pascalCoeffMass
```

を置いて、既存の `UniformBeamHeight` と `FilteredBeamHeight` を「dial height の一様性」として読み替える橋を作るのが堅いです。
