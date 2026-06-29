# Note: NoLift

## FLT3 仮定を外す解決を探る

調べたぞ。結論から言うと、 **ぬしの記憶は当たっておる** 。

snapshot はリポジトリ全体の `*.lean` と関連 `*.md` を含む archive なので、今回の Petal / FLT / NumberTheory 周辺を掘る対象として正しい。
そして、現行 standalone v3 の主核はまだ `hS0_not_sq` を仮定として受け取る形じゃが、この仮定を上位 API で置き換える道は snapshot 内にかなり用意されておる。Comparator に通した v3 でも、主定理は `hS0_not_sq` を仮定にして `a ^ 3 + b ^ 3 ≠ c ^ 3` を出している形じゃ。

## 1. 見つかった重要補題群

特に重要なのはこのあたりじゃ。

### `DkMath.Petal.BoundaryD3`

ここが、ぬしの言う **「3 を特殊単位・境界接触成分として扱う」** にかなり近い。

```lean
def BoundaryD3Branch (c b : ℕ) : Prop :=
  3 ∣ c - b

def BoundaryD3Reduced (c b : ℕ) : Prop :=
  ¬ 3 ∣ c - b
```

さらに、

```lean
theorem three_dvd_S0_nat_iff_three_dvd_sub
```

がある。意味はこうじゃ。

$$
3 \mid S0(c,b)\quad\Longleftrightarrow\quad 3 \mid (c-b)
$$

つまり cubic Petal 面では、`3` は `S0` 側と境界 gap `c-b` 側の **接触成分そのもの** になっておる。

### `DkMath.Petal.GcdBridge`

ここも強い。

```lean
theorem gcd_sub_S0_nat_eq_gcd_sub_three
```

意味は、

$$
\gcd(c-b,\ S0(c,b))=\gcd(c-b,\ 3)
$$

互いに素な Petal 座標では、境界 gap と `S0` が共有しうるものは **3 だけ** 。
これはまさに「3 だけは普通の素因子扱いではなく、境界単位・接触単位として別扱いできる」という構造じゃな。

さらに、

```lean
theorem coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

があるので、`¬ 3 ∣ c-b` なら

```lean
Nat.Coprime (c - b) (S0_nat c b)
```

まで行ける。

### `DkMath.FLT.PhaseLift`

ここが FLT3 の仮定除去に一番直接効く。

```lean
def S0PrimeSupportExceptThree (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ S0_nat c b → q ≠ 3 → ¬ q ∣ c - b
```

これは名前通り、 **3 を除いた S0 の素因子 support は境界 gap に乗らない** という述語。

そしてこれがある。

```lean
lemma s0PrimeSupportExceptThree_of_coprime
```

つまり、`b ≤ c` と `Nat.Coprime c b` から `S0PrimeSupportExceptThree c b` が自動生成できる。

さらに決定打はこれじゃ。

```lean
lemma three_sq_not_dvd_S0_of_coprime
```

意味は、`b ≤ c` と `Nat.Coprime c b` のもとで

$$
\neg\ 3^2 \mid S0(c,b)
$$

が出る。

これにより、「`q ≠ 3` 側は support + nonLiftable で潰し、`q = 3` 側は coprime で潰す」という分解がすでに実装されておる。

## 2. つまり、今の `hS0_not_sq` は弱められる

今 Comparator で通した主仮定はこれじゃった。

```lean
hS0_not_sq :
  ∀ {q : ℕ}, Nat.Prime q →
    q ∣ c ^ 3 - b ^ 3 →
    ¬ q ∣ c - b →
    ¬ q ^ 2 ∣ S0_nat c b
```

これは直接的すぎる。

snapshot 側の API を使うなら、次はこれへ弱められる。

```lean
hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q
```

なぜなら、`PhaseLift` に

```lean
lemma NoSqOnS0_of_support_nonLiftable_coprime
```

があるからじゃ。

構造はこう。

1. `Nat.Coprime c b` から `S0PrimeSupportExceptThree c b`
2. `¬ NoSqOnS0 c b` なら、平方因子は `3^2` か `q ≠ 3` 側に分かれる
3. `q ≠ 3` 側は `S0PrimeSupportExceptThree + hNonLiftAll` で潰れる
4. `3^2` 側は `three_sq_not_dvd_S0_of_coprime` で潰れる
5. よって `NoSqOnS0 c b`
6. よって FLT3 核へ接続

つまり、ぬしの言う「3 を単位のように除外して素性を見る」という直感は、Lean では

```lean
S0PrimeSupportExceptThree
```

と

```lean
three_sq_not_dvd_S0_of_coprime
```

の組で実装されておる。

## 3. ただし、完全な仮定除去まではまだ一段残る

ここは牙を立てずに正確に言うぞ。

`3` 例外はかなり綺麗に除ける。
しかし、まだ全体の FLT3 から仮定を完全除去するには、

```lean
∀ q : ℕ, NonLiftableS0 c b q
```

またはそれを生む

```lean
DescentClassifyImpossibleOnPrimitive c b
```

や

```lean
GEisensteinDescentCore c b
```

を無条件で構成する必要がある。

つまり現在の到達点は、

```text
hS0_not_sq
  ↓ 弱化可能
NoSqOnS0
  ↓ 回復可能
S0PrimeSupportExceptThree + hNonLiftAll + coprime
  ↓ さらに上位化可能
DescentClassify / GEisensteinCore
```

じゃ。

## 4. 次の Comparator Challenge 候補

次に試すなら、これがよい。

`hS0_not_sq` を直接仮定するのではなく、`hNonLiftAll` を仮定する版。

Candidate 末尾に追加する wrapper 案：

```lean
theorem PNat.pow3_add_pow3_ne_pow3_of_coprime_and_nonLiftable
    (x y z : ℕ+)
    (hcop : Nat.Coprime (x : ℕ) (y : ℕ))
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 (z : ℕ) (y : ℕ) q) :
    (x : ℕ) ^ 3 + (y : ℕ) ^ 3 ≠ (z : ℕ) ^ 3 := by
  intro h_eq
  have hcop_zy : Nat.Coprime (z : ℕ) (y : ℕ) :=
    coprime_cb_of_eq hcop h_eq
  have hyz : (y : ℕ) < (z : ℕ) := by
    by_contra hnot
    have hzy : (z : ℕ) ≤ (y : ℕ) := Nat.not_lt.mp hnot
    have hz3_le : (z : ℕ) ^ 3 ≤ (y : ℕ) ^ 3 :=
      Nat.pow_le_pow_left hzy 3
    have hsum_le : (x : ℕ) ^ 3 + (y : ℕ) ^ 3 ≤ (y : ℕ) ^ 3 := by
      simpa [h_eq] using hz3_le
    have hx3_pos : 0 < (x : ℕ) ^ 3 := by
      positivity
    omega
  exact
    (FLT_d3_by_padicValNat_of_nonLiftable_coprimeSupport
      x.2 y.2 z.2
      hcop
      hyz
      hcop_zy
      hNonLiftAll) h_eq
```

これが通れば、Comparator 上の主張は一段前進して、

```text
hS0_not_sq 仮定付き FLT3
```

から

```text
nonLiftable family 仮定付き FLT3
```

になる。

## 5. わっちの判定

これは **取り組む価値がかなり高い** 。

理由は単純じゃ。
今の standalone v3 は、すでに Comparator で検証済みの核を持っている。そこに snapshot の `PhaseLift` / `Petal` 層を移植すれば、仮定を

```lean
hS0_not_sq
```

から

```lean
hNonLiftAll
```

へ下げられる可能性が高い。

そして、その次の段階で `hNonLiftAll` を `classifyLift = impossible` や `GEisensteinDescentCore` から供給する。
ここまで行けば、かなり「FLT3 の証明シナリオ」として見栄えが変わる。

ぬしよ、これは忘れていた鉱脈じゃ。
今の Comparator 成功の直後に掘るには、ちょうどよい深さの金脈じゃな。
