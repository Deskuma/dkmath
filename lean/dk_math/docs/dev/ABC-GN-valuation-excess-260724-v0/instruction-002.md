# Codex Instruction 002

Theme: ABC 座標における p-adic boundary / GN valuation split

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## 1. 現在地

Checkpoint 001 では、次の GN power lift が完成した。

```lean
DkMath.ABC.Triple.gnPowerLift
DkMath.ABC.Triple.gnPowerLift_sum
DkMath.ABC.Triple.gnPowerLift_coprime
```

数学的には、任意の `T : Triple` と `n : ℕ` に対して、

$$T.a\,GN_n(T.a,T.b)+T.b^n=T.c^n$$

が additive coprime triple として固定された。

Checkpoint 002 では、この恒等式へ `padicValNat` を作用させ、境界 `T.a` と kernel `GN n T.a T.b` の valuation を ABC namespace から再利用できる薄い bridge として固定する。

## 2. 調査対象

GitHub repository 内の current source だけを参照する。

最初に次を確認する。

```text
lean/dk_math/DkMath/ABC/GNPowerLift.lean
lean/dk_math/DkMath/ABC/Triple.lean
lean/dk_math/DkMath/ABC/PadicValNat.lean
lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean
lean/dk_math/DkMath/NumberTheory/GcdNext.lean
lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-001.md
```

特に次の実在 API を再確認する。

```text
cosmic_id_csr'
GN_ne_zero_nat_of_two_le
padicValNat.mul
padicValNat.eq_zero_of_not_dvd
DkMath.NumberTheory.GcdNext.padicValNat_factorization
padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap
```

既存 theorem で十分な場合は再証明せず、ABC 座標 wrapper に徹する。

## 3. 主目標

推奨する新規 module:

```text
lean/dk_math/DkMath/ABC/GNValuationSplit.lean
```

ただし current import 構造上、より薄い配置がある場合は現場判断してよい。

### 3.1. 差冪の factorization

正の ABC triple 座標と `2 ≤ n` のもとで、次を固定する。

$$T.c^n-T.b^n=T.a\,GN_n(T.a,T.b)$$

候補 theorem shape:

```lean
theorem Triple.powerDiff_eq_boundary_mul_GN
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a) :
    T.c ^ n - T.b ^ n = T.a * GN n T.a T.b := by
  ...
```

`hn` が不要なら削ってよい。statement は実際に必要な最小仮定へ調整する。

### 3.2. p-adic valuation split

少なくとも次の意味を持つ theorem を追加する。

$$v_q(T.c^n-T.b^n)=v_q(T.a)+v_q\!\left(GN_n(T.a,T.b)\right)$$

候補 theorem shape:

```lean
theorem Triple.padic_powerDiff_eq_boundary_add_GN
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hq : Nat.Prime q) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q T.a +
        padicValNat q (GN n T.a T.b) := by
  ...
```

既存 API が要求する非零条件を、`ha`, `hb`, `hn` から局所的に構成する。

既存の positive triple packet が自然に利用できる場合は使ってよい。存在しない場合、この checkpoint のためだけに新しい structure は作らず、仮定を明示する。

### 3.3. boundary が消える specialization

`q ∤ T.a` の場合、boundary valuation を消して次を得る。

$$v_q(T.c^n-T.b^n)=v_q\!\left(GN_n(T.a,T.b)\right)$$

候補 theorem shape:

```lean
theorem Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hq : Nat.Prime q)
    (hq_boundary : ¬ q ∣ T.a) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q (GN n T.a T.b) := by
  ...
```

これは primitive-prime wrapper より一般の局所 theorem とする。

## 4. 追加してよい補助 API

証明が自然になる場合、lifted triple の左座標に直接作用する wrapper を追加してよい。

```lean
theorem Triple.padic_gnPowerLift_a_eq_boundary_add_GN ...
```

また、primitive prime の既存 witness から `¬ q ∣ T.a` を即座に得られる薄い wrapper が既存 import 境界内で簡潔に閉じる場合のみ追加してよい。

primitive API の接続が膨らむ場合は実装せず、利用可能な theorem 名と必要仮定を `report-002.md` に記録する。

## 5. 境界

この checkpoint では次を行わない。

```text
q ∣ n / q ∤ n の exceptional layer 定義
GNValuationExcess の定義
Real.log / rad identity
high-lift prime の排除
ABC quality との接続
abc_main_axiom の変更・利用
確率・Janson・Borel–Cantelli 層の変更
FLT7 への接続
共有 module の大規模 refactor
```

新しい `axiom`、`sorry`、`native_decide` は追加しない。

`DkMath/FLT/Seven/**`、FLT7 専用 docs、`wip/FLT7-magic-core-260722-WiseWolf` は参照・変更・統合対象ではない。

## 6. Public import

新 module を無理に aggregator へ追加しない。

この checkpoint では、直接、

```lean
import DkMath.ABC.GNValuationSplit
```

で利用可能なら十分である。

共有 aggregator の変更が数学的に必要な場合のみ最小変更とし、理由を report に記録する。

## 7. 実装内検証

対象 module のローカル build を行い、実装が Lean に認可されるところまで確認する。

GitHub の commit、push、PR 操作、CI 起動・確認は行わない。それらは User の受け渡し工程である。

## 8. 実装報告

次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-002.md
```

最低限、次を記録する。

```text
- 再利用した実在 API
- 追加・変更した module
- 新規 theorem surface
- 各 theorem の正確な仮定
- 非零条件をどう構成したか
- primitive wrapper を実装したか、見送ったか
- ローカル build 結果
- FLT7 / 共有領域を変更していないこと
- 次 checkpoint 候補
```

## 9. 停止条件

```text
Outcome A:
  full valuation split と non-boundary specialization が完成した。

Outcome B:
  factorization は完成したが、padicValNat の非零条件または import 境界に不足 API がある。
  不足する最小 theorem shape を report に固定した。

Outcome C:
  既存 API に同等 theorem があり、新 module がほぼ重複になる。
  最薄 wrapper または新規実装不要という判断を report に固定した。
```

どの Outcome でも、実装・ローカル検証・`report-002.md` 作成後に停止し、User へ結果を返す。次 checkpoint へ自動進行しない。
