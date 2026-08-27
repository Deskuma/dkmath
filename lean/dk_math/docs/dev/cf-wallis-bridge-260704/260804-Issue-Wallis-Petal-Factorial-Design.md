# 260804 Issue: Wallis–Petal 階乗経路 設計書

- Status: Proposed design / not implemented
- Date: 2026-08-04
- Target branch examined: `develop`
- Conversation CID: `6a70c207-6590-83e8-83ff-cfc11d956da4`
- Companion plan: `260804-Issue-Wallis-Petal-Factorial-Remediation-Plan.md`

## 1. 設計目的

この設計は、Wallis–Cosmic 有限積の中央比率を、Mathlib の `Nat.factorial` を
直接の正本とせず、Petal の動的成長構造から構成するためのものである。

検証したい構造は次。

```text
固定 Petal:
  等比成長

可変 Petal:
  lap ごとに基底が変わる積

階乗 Petal:
  基底列 1, 2, 3, ... を選んだ可変 Petal

Wallis:
  階乗 Petal の偶奇分離から現れる有限積
```

## 2. 現行モデルの整理

### 2.1 固定 Petal

現行 `relPetalTotal` は、

$$
R(n,k)
=
n(n+1)^k
$$

である。

```lean
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap
```

ここでは、

```text
initial core = n
lap base     = n + 1
```

が固定されている。

### 2.2 純粋な動的積

現行 `dynamicOrbitTotal` は、

$$
O_b(k)
=
\prod_{i<k}b(i)
$$

である。

```lean
def dynamicOrbitTotal (b : Nat -> Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b
```

これは階乗・冪・素数積を含む一般的な prefix product であり、Petal の動的成長核
として再利用できる。

### 2.3 現行 dynamic Petal

現行 `dynamicPetalTotal` は、

$$
D_a(k)
=
a(0)\prod_{i<k}(a(i)+1)
$$

である。

```lean
def dynamicPetalTotal (a : Nat -> Nat) (k : Nat) : Nat :=
  a 0 * dynamicOrbitTotal (fun i => a i + 1) k
```

この API は、固定列 `a i = n` によって `relPetalTotal n k` を回収するためには
自然である。

しかし、次を独立に指定できない。

```text
initial core
lap base sequence
```

階乗 Petal の設計では、この二つを分離する。

## 3. 基本意味論

### 3.1 Raw orbit product

基底列 `b` の零周積を含む純粋積。

$$
O_b(k)
=
\prod_{i<k}b(i)
$$

零周では空積になる。

$$
O_b(0)
=
1
$$

### 3.2 Petal orbit total

初期核 `c` を持つ Petal total を、

$$
T(c,b,k)
=
c\,O_b(k)
$$

とする。

```lean
def petalOrbitTotal
    (core : Nat) (base : Nat -> Nat) (lap : Nat) : Nat :=
  core * dynamicOrbitTotal base lap
```

再帰則は、

$$
T(c,b,0)
=
c
$$

$$
T(c,b,k+1)
=
T(c,b,k)b(k)
$$

となる。

これにより「零周では初期核だけが残る」が定義上明確になる。

## 4. 零核と零周

### 4.1 零核

`core = 0` は 0 角形に対応する退化状態と読む。

$$
T(0,b,k)
=
0
$$

lap-base が何であっても Petal total は伸びない。

推奨 theorem。

```lean
@[simp]
theorem petalOrbitTotal_zero_core
    (base : Nat -> Nat) (lap : Nat) :
    petalOrbitTotal 0 base lap = 0 := by
  simp [petalOrbitTotal]
```

### 4.2 零周

`lap = 0` は、増殖を一度も適用していない状態。

$$
T(c,b,0)
=
c
$$

推奨 theorem。

```lean
@[simp]
theorem petalOrbitTotal_zero
    (core : Nat) (base : Nat -> Nat) :
    petalOrbitTotal core base 0 = core := by
  simp [petalOrbitTotal, dynamicOrbitTotal_zero]
```

### 4.3 `0! = 1`

階乗 Petal は最小有効核 `1` を使う。

$$
F_P(n)
=
T(1,i\mapsto i+1,n)
$$

したがって、

$$
F_P(0)
=
T(1,i\mapsto i+1,0)
=
1
$$

これは、

```text
core = 0
```

から得られるのではない。

```text
core = 1
lap = 0
```

から得られる。

この意味分離を docstring に必ず記録する。

## 5. 有効 Petal 核

### 5.1 述語

```lean
def IsValidPetalCore (n : Nat) : Prop :=
  0 < n
```

### 5.2 型

Mathlib の現行版で `PNat` / `ℕ+` の利用可能性を調査する。
安定した API が確認できれば採用候補。

依存を最小にしたい場合は、DkMath 側で薄い subtype を置く。

```lean
abbrev PositivePetalCore :=
  {n : Nat // IsValidPetalCore n}
```

### 5.3 最小単位核

```lean
def unitPetalCore : PositivePetalCore :=
  ⟨1, by decide⟩
```

必要 theorem。

```lean
theorem one_le_of_validPetalCore
    {n : Nat} (hn : IsValidPetalCore n) :
    1 <= n := by
  omega
```

```lean
theorem unitPetalCore_is_minimum
    (c : PositivePetalCore) :
    unitPetalCore.1 <= c.1 := by
  exact one_le_of_validPetalCore c.2
```

## 6. 固定 Petal の回収

固定 Petal は、

```text
core = n
base i = n + 1
```

の特殊化である。

$$
T(n,i\mapsto n+1,k)
=
n(n+1)^k
$$

推奨 theorem。

```lean
theorem petalOrbitTotal_const
    (core base lap : Nat) :
    petalOrbitTotal core (fun _ => base) lap =
      core * base ^ lap := by
  simp [petalOrbitTotal, dynamicOrbitTotal_const]
```

```lean
theorem relPetalTotal_eq_petalOrbitTotal_const
    (n lap : Nat) :
    relPetalTotal n lap =
      petalOrbitTotal n (fun _ => lapBase n) lap := by
  simp [relPetalTotal, petalOrbitTotal,
    dynamicOrbitTotal_const, baseUnitCore]
```

これにより、

```text
等比 Petal
  ⊂
可変基底 Petal
```

が明示される。

## 7. 階乗 Petal

### 7.1 定義

```lean
def factorialPetal (n : Nat) : Nat :=
  petalOrbitTotal 1 (fun i => i + 1) n
```

添字は `Finset.range n` なので、因子は、

```text
1, 2, ..., n
```

になる。

$$
F_P(n)
=
1\prod_{i=0}^{n-1}(i+1)
$$

### 7.2 零点

```lean
@[simp]
theorem factorialPetal_zero :
    factorialPetal 0 = 1 := by
  simp [factorialPetal, petalOrbitTotal]
```

### 7.3 再帰

```lean
theorem factorialPetal_succ (n : Nat) :
    factorialPetal (n + 1) =
      factorialPetal n * (n + 1) := by
  simp [factorialPetal, petalOrbitTotal,
    dynamicOrbitTotal_succ, Nat.mul_assoc]
```

この theorem が Petal 階乗の主再帰則である。

### 7.4 Mathlib 階乗との一致

互換 theorem は最後に置く。

```lean
theorem factorialPetal_eq_factorial (n : Nat) :
    factorialPetal n = Nat.factorial n := by
  induction n with
  | zero =>
      simp [factorialPetal_zero]
  | succ n ih =>
      rw [factorialPetal_succ, ih, Nat.factorial_succ]
      ac_rfl
```

既存 theorem、

```lean
dynamicOrbitTotal_succIndex_eq_factorial
```

を利用して短く閉じる案もある。

ただし設計上は、`factorialPetal_zero` と `factorialPetal_succ` を先に独立して固定し、
Petal 自身の再帰構造を API として残す。

## 8. 正値性

有効核と正の base 列なら total は正。

```lean
theorem petalOrbitTotal_pos
    {core : Nat} (hcore : 0 < core)
    {base : Nat -> Nat}
    (hbase : forall i, 0 < base i)
    (lap : Nat) :
    0 < petalOrbitTotal core base lap := by
  ...
```

階乗 Petal では、

```lean
theorem factorialPetal_pos (n : Nat) :
    0 < factorialPetal n := by
  ...
```

が得られる。

Wallis の有理数除算へ進む際の分母非零証明に使える。

## 9. 現行 `dynamicPetalTotal` の扱い

削除しない。

次の特殊化 theorem を追加し、canonical API との位置関係を明示する。

```lean
theorem dynamicPetalTotal_eq_petalOrbitTotal
    (a : Nat -> Nat) (k : Nat) :
    dynamicPetalTotal a k =
      petalOrbitTotal (a 0) (fun i => a i + 1) k := by
  rfl
```

役割分担は次。

```text
dynamicOrbitTotal:
  純粋 prefix product

petalOrbitTotal:
  初期核と基底列を分離した canonical Petal total

dynamicPetalTotal:
  単位核列 a と inheritance slot +1 を結び付けた既存特殊形

relPetalTotal:
  固定単位核の等比特殊形

factorialPetal:
  unit core 1 と successor base の特殊形
```

## 10. Wallis 中央比率

### 10.1 Petal 正本

```lean
def petalCentralRatioQ (m : Nat) : Rat :=
  ((2 : Rat) ^ (2 * m) * (factorialPetal m : Rat) ^ 2) /
    (factorialPetal (2 * m) : Rat)
```

数学的には、

$$
R_P(m)
=
\frac{4^mF_P(m)^2}{F_P(2m)}
$$

### 10.2 主有限 theorem

```lean
theorem petalCentralRatioQ_eq_centralOddRatioPartialQ
    (m : Nat) :
    petalCentralRatioQ m = centralOddRatioPartialQ m := by
  ...
```

この証明は `factorialPetal_succ` を用いた帰納法で行う。
証明本体では `Nat.factorial_succ` に戻らない。

想定される比率は、

$$
\frac{R_P(m+1)}{R_P(m)}
=
\frac{2m+2}{2m+1}
$$

で、`centralOddRatioPartialQ` の次因子と一致する。

### 10.3 choose 版との互換

既存定義。

```lean
def centralRatioQ (m : Nat) : Rat :=
  (2 ^ (2 * m) : Rat) / (Nat.choose (2 * m) m : Rat)
```

互換 theorem。

```lean
theorem centralRatioQ_eq_petalCentralRatioQ (m : Nat) :
    centralRatioQ m = petalCentralRatioQ m := by
  ...
```

この theorem の内部では Mathlib の choose / factorial 補題を使ってよい。
ここは既存数学 API との境界であり、Petal 主経路ではない。

### 10.4 Wallis–Cosmic 主経路

新規主 theorem。

```lean
theorem petalCentralRatioQ_mul_mirror_eq_wallisPartialQ
    (m : Nat) :
    petalCentralRatioQ m * mirrorOddRatioPartialQ m =
      wallisPartialQ m := by
  rw [petalCentralRatioQ_eq_centralOddRatioPartialQ,
    centralOdd_mul_mirror_eq_wallisPartialQ]
```

```lean
theorem petalCentralRatioQ_mul_mirror_eq_cosmicPartialQ
    (m : Nat) :
    petalCentralRatioQ m * mirrorOddRatioPartialQ m =
      cosmicPartialQ m := by
  rw [petalCentralRatioQ_mul_mirror_eq_wallisPartialQ,
    wallisPartialQ_eq_cosmicPartialQ]
```

既存 choose 版 theorem は corollary にする。

```lean
theorem centralRatioQ_mul_mirror_eq_cosmicPartialQ
    (m : Nat) :
    centralRatioQ m * mirrorOddRatioPartialQ m =
      cosmicPartialQ m := by
  rw [centralRatioQ_eq_petalCentralRatioQ,
    petalCentralRatioQ_mul_mirror_eq_cosmicPartialQ]
```

## 11. 依存グラフ

改修後の意図する依存。

```text
DkMath.Petal.Counting
  dynamicOrbitTotal
  petalOrbitTotal
       |
       v
DkMath.Petal.Factorial
  PositivePetalCore
  factorialPetal
       |
       v
DkMath.Pascal.WallisCosmicPetalBridge
  petalCentralRatioQ
  finite half-product / cosmic bridge
       |
       +----------------------+
       |                      |
       v                      v
WallisLimitBridge        compatibility layer
Real.Wallis              Nat.factorial / Nat.choose
       |
       v
pi / 2
```

重要なのは、Petal finite route と compatibility layer を横に分けること。

## 12. Gamma 非依存性の定義

「Gamma を通らない」を一語で済ませず、三段階に定義する。

### Level 1 — Source-level independent

DkMath の Petal finite theorem のソース中に、次がない。

```text
Real.Gamma
Complex.Gamma
Gamma_nat_eq_factorial
```

### Level 2 — Factorial-source independent

Wallis 主有限 theorem が `Nat.factorial` の再帰を直接使わず、
`factorialPetal_zero` / `factorialPetal_succ` を使う。

### Level 3 — Transitive proof independent

`Real.Wallis.tendsto_W_nhds_pi_div_two` を含む依存閉包を監査し、Gamma 由来の証明を
使わないことを確認する。

Level 3 は Mathlib source の調査が必要。未確認のまま強い非依存主張をしない。

## 13. 小例での仕様固定

```lean
example : factorialPetal 0 = 1 := by decide
example : factorialPetal 1 = 1 := by decide
example : factorialPetal 2 = 2 := by decide
example : factorialPetal 3 = 6 := by decide
example : factorialPetal 4 = 24 := by decide
```

固定 Petal。

```lean
example : petalOrbitTotal 5 (fun _ => 6) 0 = 5 := by decide
example : petalOrbitTotal 5 (fun _ => 6) 1 = 30 := by decide
example : petalOrbitTotal 5 (fun _ => 6) 2 = 180 := by decide
```

退化核。

```lean
example (b : Nat -> Nat) (k : Nat) :
    petalOrbitTotal 0 b k = 0 := by
  simp
```

これらを theorem または test example として残し、off-by-one を防ぐ。

## 14. 移行方針

### 14.1 互換性

既存公開名は原則維持する。

```text
centralRatioQ_eq_centralOddRatioPartialQ
centralRatioQ_mul_mirror_eq_wallisPartialQ
centralRatioQ_mul_mirror_eq_cosmicPartialQ
```

内部証明だけを Petal 主経路へ切り替える。

### 14.2 private helper

次は削除候補。

```text
centralRatioFactorialQ
factorial_two_mul_succ_cast_Q
centralRatioFactorialQ_eq_centralOddRatioPartialQ
```

ただし互換 theorem の証明で一時的に必要なら、

```text
compatibility-only
```

と明記して局所化する。

### 14.3 下流

`WallisGrowthBridge` は当面既存 `centralRatioQ` theorem を利用してよい。
既存 theorem が Petal corollary になれば、下流は自動的に Petal 経路へ移る。

研究上の主張を明確にするため、後で `petalCentralRatioQ` 版の growth alias を追加してもよい。

## 15. 検証チェック

### Semantic tests

- `core = 0` は常に `0`。
- `lap = 0` は初期核。
- valid core は正。
- unit core は最小。
- fixed base は冪。
- successor base は階乗。

### Dependency tests

```sh
rg "Nat\.factorial|factorial_succ" \
  DkMath/Pascal/WallisCosmicPetalBridge.lean

rg "Gamma|Gamma_nat_eq_factorial" \
  DkMath/Petal \
  DkMath/Pascal/Wallis*.lean
```

期待結果は、`Nat.factorial` が compatibility theorem の局所部分に限られること。
Gamma は finite route から 0 件であること。

### Build tests

```sh
lake build DkMath.Petal.Counting
lake build DkMath.Petal.Factorial
lake build DkMath.Petal
lake build DkMath.Pascal.WallisCosmicPetalBridge
lake build DkMath.Pascal.WallisLimitBridge
lake build DkMath.Pascal.WallisGrowthBridge
lake build DkMath.Pascal
lake build DkMath
git diff --check
```

## 16. 設計上の最終判定

採用する中心構造は、

$$
T(c,b,k)
=
c\prod_{i<k}b(i)
$$

である。

固定 Petal は、

$$
T(n,i\mapsto n+1,k)
=
n(n+1)^k
$$

階乗 Petal は、

$$
T(1,i\mapsto i+1,n)
=
n!
$$

となる。

この設計により、`0! = 1` は「0 角形」ではなく、

> 最小有効単位核 `1` に対する零周保存

として Petal 内部で意味付けされる。

Wallis の中央比率はこの階乗 Petal の偶奇分離として構成し、`Nat.factorial` と
`Nat.choose` は既存数学との互換確認に下げる。
