# Codex 事前情報

設計方針転換の主語の置き換え

## Codex へ渡すべき要約

今回の考察で、Collatz.PetalBridge の主語を大きく修正する。

従来の主語は「`3n+1` と (2) で割る操作」だったが、今後は次の四段階で読む。

```text
Odd Gnomon correction
  奇数 n に奇数グノモン層 2n+1 を足す

Pow2 alignment evaluation
  raw = 3n+1 が 2^h にどれだけ整列したかを v2 で評価する

Residual shape extraction
  raw / 2^h で、これ以上 2 で割れない奇数残差形状を抽出する

Relative scale update
  抽出された奇数残差を次の相対スケールとして扱う
```

つまり Collatz は「3倍して増やす問題」ではなく、**奇数グノモン補正と 2進整列評価による相対スケール調整問題**として再構築する。

## 背景にある新しい視座

奇数ステップは、

[
3n+1=n+(2n+1)
]

であり、(2n+1) は平方数の差分グノモン層。

[
(n+1)^2-n^2=2n+1
]

したがって `3n+1` は、奇数 (n) に次の平方グノモン層を足す操作である。

その後、

[
3n+1=2^h q
]

と分解する。
ここで (h=v_2(3n+1)) は「2で割った回数」ではなく、**(2^h) 一色線への整列深度**である。
(q) は、整列分を除去した後に残る **ResidualShape**、すなわち次の相対スケールである。

実数 (\log_2 3) 評価は最後でよい。まずは整数だけで `height`, `sumS`, `residual shape`, `pressure margin` を追う。

## 既存実装との接続

checkpoint 123 では、deep all-ones continuation channel が shallow channel に含まれること、つまり continuation carrier nesting が Lean で固定された。追加された主な補題は `allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le`, `sourceContinuationMass_anti_mono_depth`, `tailContinuationMass_anti_mono_depth`, `selectedContinuationMass_nested_of_lt` など。これは「深い residual channel は浅い channel に含まれる」という新解釈へ翻訳できる。

checkpoint 124 では、retention carrier nesting と `SourcePressureMarginInt` が追加された。さらに広い Python 観測で prefix failure が `189` 件出ており、無条件の `deep selected pressure -> shallow selected pressure` は危険であることが分かった。pressure は carrier membership ではなく、`retention < 2 * continuation`、つまり margin の符号条件として扱う。

添付 `B.lean` 側には、宇宙式・素数境界の基礎がある。特に `cosmic_identity_ring`, `cosmicNReal`, `cosmic_unit_boundary_demands_new_prime`, `exists_prime_not_mem_dvd_nat_add_unit_of_forall_dvd` があり、既知 support とそれを避ける unit (u) によって (P+u) が未知 support へ swap する構造がすでに見えている。

## 新しい実装方針

まず Collatz 側に薄いモジュールを切る。

候補名：

```text
DkMath.Collatz.GnomonEvaluation
```

または、

```text
DkMath.Collatz.GnomonScale
```

最初に入れる定義：

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  2 * n + 1

def RawGnomonStep (n : ℕ) : ℕ :=
  n + OddGnomonLayer n
```

基本補題：

```lean
theorem rawGnomonStep_eq_three_mul_add_one
    (n : ℕ) :
    RawGnomonStep n = 3 * n + 1 := by
  unfold RawGnomonStep OddGnomonLayer
  ring
```

平方グノモン補題：

```lean
theorem square_succ_eq_square_add_oddGnomonLayer
    (n : ℕ) :
    (n + 1)^2 = n^2 + OddGnomonLayer n := by
  unfold OddGnomonLayer
  ring
```

奇数層の総和：

```lean
theorem sum_odd_eq_square
    (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n^2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
```

開始点付きのグノモン帯も欲しい。

```lean
theorem square_add_eq_square_add_gnomon_sum
    (P u : ℕ) :
    (P + u)^2 =
      P^2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) := by
  -- Nat subtraction を避けた形なので安全
  -- induction u 推奨
  sorry
```

## Pow2 評価層

既存の `rawHeightLabel` / `orbitWindowHeight` と接続するため、必要なら alias を作る。

```lean
def RawGnomonHeight (n : ℕ) : ℕ :=
  padicValNat 2 (RawGnomonStep n)

def RawGnomonResidualShape (n : ℕ) : ℕ :=
  RawGnomonStep n / 2 ^ RawGnomonHeight n
```

ただし、既存 Collatz 実装に同等の accelerated odd step / height があるなら、再定義ではなく bridge theorem にする。

欲しい bridge：

```lean
theorem rawGnomonStep_eq_pow_height_mul_residualShape
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonStep n =
      2 ^ RawGnomonHeight n * RawGnomonResidualShape n := by
  -- padicValNat の既存 factorization lemma を探して使う
  sorry
```

さらに、残差形状が奇数であること：

```lean
theorem residualShape_odd
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonResidualShape n % 2 = 1 := by
  -- padicValNat の maximality を使う
  sorry
```

## 形状分割の観測層

右シフトは「現在の形状を (1/2^h) に縮小して見る評価」と読む。
そのため、深さごとの remainder profile を観測対象にする。

```lean
def RawGnomonRemainderAtDepth (n j : ℕ) : ℕ :=
  RawGnomonStep n % 2 ^ j

def FirstFailedPow2Depth (n : ℕ) : ℕ :=
  RawGnomonHeight n + 1
```

欲しい補題：

```lean
theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
    (n j : ℕ)
    (hj : j ≤ RawGnomonHeight n) :
    RawGnomonRemainderAtDepth n j = 0 := by
  -- 2^j ∣ RawGnomonStep n を使う
  sorry
```

読み：

```text
j <= height:
  その深さまでは完全に 2^j 分割できる

j = height + 1:
  初めて分割に失敗する深さ

ResidualShape:
  失敗後に残る別スケールの奇数形状
```

## Pressure / Margin の再解釈

`SourcePressureMarginInt` は今後、shape margin として読む。

```text
SourcePressureMarginInt
  = 2 * continuation - retention
```

新しい意味：

```text
深い residual shape channel が、
浅い retention shape に対してどれだけ優勢か
```

prefix failure は「失敗」ではなく、

```text
浅い分割では margin <= 0
深い分割では margin > 0

つまり、深い解像度で初めて residual shape が立ち上がる現象
```

として扱う。

次に入れる predicate 候補：

```lean
def ShapePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
    0 < SourcePressureMarginInt n k (r + j₂)
```

既存の `SourcePressurePrefixFailure` を作るなら、margin 版との同値も作る。

## 宇宙式・グノモン・support swap 側

`B.lean` の方向を整理する。

`u` を動かすと、既知素数を避ける Gap を選べる。
しかし `u = 1` に固定しても、奇数グノモン層を足し重ねることで Body 側の因子 (Q) を自由に選べる。

単位宇宙式：

```lean
theorem cosmic_unit_step
    (Q : ℕ) :
    Q * (Q + 2) + 1 = (Q + 1)^2 := by
  ring
```

Body 側は (Q) を因子に持つ。

```lean
theorem dvd_cosmic_unit_body_left
    (Q : ℕ) :
    Q ∣ Q * (Q + 2) := by
  exact dvd_mul_right Q (Q + 2)
```

Big root 側は (Q) と互いに素。

```lean
theorem cosmic_unit_body_factor_coprime_big_root
    (Q : ℕ) :
    Nat.Coprime Q (Q + 1) ∧ Q ∣ Q * (Q + 2) := by
  constructor
  · exact Nat.coprime_self_add_right 1 Q
  · exact dvd_mul_right Q (Q + 2)
```

support 版：

```lean
def CarriesPrimeSupport (S : Finset ℕ) (Q : ℕ) : Prop :=
  ∀ p, p ∈ S → p ∣ Q
```

最終的に欲しい theorem：

```lean
theorem cosmic_unit_gnomon_support_swap
    (S : Finset ℕ)
    (Q : ℕ)
    (hs : ∀ p ∈ S, Nat.Prime p)
    (hcarry : CarriesPrimeSupport S Q) :
    (∀ p ∈ S, p ∣ Q * (Q + 2)) ∧
    (∀ p ∈ S, ¬ p ∣ Q + 1) ∧
    Q * (Q + 2) + 1 = (Q + 1)^2 := by
  constructor
  · intro p hp
    exact dvd_trans (hcarry p hp) (dvd_mul_right Q (Q + 2))
  · constructor
    · intro p hp hpdiv
      have hpQ : p ∣ Q := hcarry p hp
      have hp1 : p ∣ 1 := by
        -- p | Q+1 and p | Q から p | 1
        sorry
      exact Nat.Prime.not_dvd_one (hs p hp) hp1
    · ring
```

これは「Body 側は既知 support を背負い、Gap = 1 を足すと Big root = Q+1 が既知 support を避ける」ことを固定する。

## Python 実験側へ伝えること

巨大 CSV は不要。summary markdown に統計だけでよい。

追加したい列：

```text
raw
height
residual_shape
first_failed_depth
failed_remainder
residual_mod_8
residual_mod_16
residual_mod_32
odd_gnomon_layer
sum_height
height_one_count
height_ge_two_count
margin_profile
first_shape_prefix_failure
shape_margin_jump
```

見たい統計：

```text
height 1 の膨張が height >= 2 でどれだけ補償されるか

prefix failure が素数・all-ones residue・primorial boundary に偏るか

residual shape が特定の mod 2^r channel に滞留するか

shape margin jump が長期的に評価落下側へ偏るか
```

## やらないこと

今はまだ `Real.log` や (\log_2 3) に行かない。
実数評価は最後の翻訳層。

今やるべきことは：

```text
整数で Gnomon 補正を定義する
Pow2 整列評価を既存 height と接続する
ResidualShape を抽出する
Pressure / Margin を shape profile として読み直す
```

## 次 checkpoint の推奨タスク

Codex には次を依頼するのがよい。

```text
Checkpoint 125 / 126 candidate:
  Add DkMath.Collatz.GnomonEvaluation.

Implement:
  OddGnomonLayer
  RawGnomonStep
  rawGnomonStep_eq_three_mul_add_one
  square_succ_eq_square_add_oddGnomonLayer
  sum_odd_eq_square
  square_add_eq_square_add_gnomon_sum if feasible

Then add bridge notes to PetalBridge docs:
  raw step = odd gnomon correction
  height = pow2 alignment depth
  accelerated odd label = residual shape
  sumS = cumulative pow2 evaluation

Do not introduce Real.log yet.
```

## 最終方針

この新視座での実装方針はこう。

```text
1. Collatz を奇数グノモン補正として再定義する。

2. 2 で割る操作を pow2 整列評価として読む。

3. 割った後の奇数を residual shape として抽出する。

4. 既存 PetalBridge の height / sumS / continuation / retention / margin を、この residual shape profile へ翻訳する。

5. prefix failure を、深い解像度で residual shape が立ち上がる現象として扱う。

6. 最後にだけ、整数評価を Real/log 成長評価へ接続する。
```

Codex には「証明を急ぐな。まず主語を置き換えよ」と伝えるのがよい。
