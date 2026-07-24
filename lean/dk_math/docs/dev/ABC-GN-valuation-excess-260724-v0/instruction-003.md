# Codex Instruction 003

Theme: ABC 座標における exponent-exception / non-exceptional GN layer

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## 1. 現在地

Checkpoint 001 では GN power lift、Checkpoint 002 では p-adic boundary / GN split が完成した。

```lean
DkMath.ABC.Triple.gnPowerLift
DkMath.ABC.Triple.powerDiff_eq_boundary_mul_GN
DkMath.ABC.Triple.padic_powerDiff_eq_boundary_add_GN
DkMath.ABC.Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
```

数学的には、正の ABC triple と `2 ≤ n` のもとで、

$$v_q(T.c^n-T.b^n)=v_q(T.a)+v_q\!\left(GN_n(T.a,T.b)\right)$$

が固定された。

Checkpoint 003 は研究地図 `ABC-GN-004` に対応する。境界 `T.a` と kernel `GN n T.a T.b` の共通 prime は指数 `n` を割る、という gcd spine を ABC namespace へ固定し、`q ∤ n` の non-exceptional channel では valuation が GN 側へ集中することを theorem surface として得る。

## 2. 調査対象

GitHub repository 内の current source だけを参照する。

```text
lean/dk_math/DkMath/ABC/GNPowerLift.lean
lean/dk_math/DkMath/ABC/GNValuationSplit.lean
lean/dk_math/DkMath/ABC/Triple.lean
lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean
lean/dk_math/DkMath/NumberTheory/UniqueFactorizationGN.lean
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-002.md
```

特に次の実在 API を再確認する。

```text
DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
DkMath.NumberTheory.Gcd.coprime_boundary_GN_of_coprime_add_of_coprime_exp
DkMath.NumberTheory.PrimePowComparisonExceptionalLayer
DkMath.NumberTheory.PrimePowComparisonNonExceptionalLayer
Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
```

`UniqueFactorizationGN` は既存 vocabulary と theorem surface の確認対象である。依存が重い場合、この ABC module から import せず、`Gcd.GN` の最小 API だけで実装する。

## 3. 推奨 module

```text
lean/dk_math/DkMath/ABC/GNExceptionalSplit.lean
```

current import 構造上、より薄い配置・名称がある場合は現場判断してよい。

## 4. 主目標

### 4.1. ABC boundary / GN gcd は指数を割る

次の意味を持つ ABC wrapper を追加する。

$$\gcd\!\left(T.a,GN_n(T.a,T.b)\right)\mid n$$

候補 theorem shape:

```lean
theorem Triple.gcd_boundary_GN_dvd_exp
    (T : Triple) {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a) :
    Nat.gcd T.a (GN n T.a T.b) ∣ n := by
  ...
```

`T.hsum` から `T.b < T.c` を作り、`T.hcop` から `Nat.Coprime T.c T.b` を作って、既存 `gcd_gap_GN_dvd_exp` を ABC 座標へ移すことを第一候補とする。

仮定がさらに削れる場合は最小化してよい。

### 4.2. boundary / GN overlap は指数例外を強制する

prime に限定する前の一般 divisibility theorem を優先する。

```lean
theorem Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hq_boundary : q ∣ T.a)
    (hq_GN : q ∣ GN n T.a T.b) :
    q ∣ n := by
  ...
```

これは、任意の共通因子が gcd を経由して指数を割るという局所 Core である。

### 4.3. non-exceptional channel の boundary separation

`q ∤ n` かつ `q ∣ GN` なら、`q ∤ T.a` を得る。

```lean
theorem Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hq_exp : ¬ q ∣ n)
    (hq_GN : q ∣ GN n T.a T.b) :
    ¬ q ∣ T.a := by
  ...
```

定理名と引数順は existing style に合わせて調整してよい。

### 4.4. non-exceptional GN valuation concentration

Checkpoint 002 の specialization と 4.3 を接続し、prime `q` が GN に現れ、指数を割らない場合、差冪 valuation 全体が GN 側へ集中する theorem を追加する。

$$q\nmid n,\ q\mid GN_n(T.a,T.b)\Longrightarrow v_q(T.c^n-T.b^n)=v_q\!\left(GN_n(T.a,T.b)\right)$$

候補 theorem shape:

```lean
theorem Triple.padic_powerDiff_eq_GN_of_not_dvd_exp_of_dvd_GN
    (T : Triple) {n q : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hq : Nat.Prime q)
    (hq_exp : ¬ q ∣ n)
    (hq_GN : q ∣ GN n T.a T.b) :
    padicValNat q (T.c ^ n - T.b ^ n) =
      padicValNat q (GN n T.a T.b) := by
  ...
```

この theorem は primitive prime を仮定せず、non-exceptional GN support 上の一般局所 bridge とする。

### 4.5. coprime exponent wrapper

既存 theorem の薄い ABC wrapper として自然に閉じる場合、次も追加してよい。

```lean
theorem Triple.coprime_boundary_GN_of_coprime_exp
    (T : Triple) {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hcop_exp : Nat.Coprime T.a n) :
    Nat.Coprime T.a (GN n T.a T.b) := by
  ...
```

これは 4.1 の全体版であり、既存 `coprime_boundary_GN_of_coprime_add_of_coprime_exp` の ABC 座標 wrapper に徹する。

## 5. 設計判断

新しい `GNExceptionalPrime` / `GNNonExceptionalPrime` predicate は必須ではない。既存 `q ∣ n` / `¬ q ∣ n` の theorem assumptions と `UniqueFactorizationGN` の vocabulary で十分なら、重複定義を追加しない。

一般数論定理を ABC 側で再証明しない。ABC module の役割は、`T.a + T.b = T.c` と `T.hcop` を既存 GN gcd API へ接続する薄い翻訳層である。

## 6. 境界

この checkpoint では次を行わない。

```text
prime-power comparison family の新規構築
GNValuationExcess の定義
factorization support の有限和
Real.log / rad identity
primitive / Zsigmondy witness の接続
high-lift prime の排除
ABC quality との接続
abc_main_axiom の変更・利用
FLT7 への接続
共有 module の大規模 refactor
```

新しい `axiom`、`sorry`、`native_decide` は追加しない。

`DkMath/FLT/Seven/**`、FLT7 専用 docs、`wip/FLT7-magic-core-260722-WiseWolf` は参照・変更・統合対象ではない。

## 7. Public import

新 module を無理に aggregator へ追加しない。

```lean
import DkMath.ABC.GNExceptionalSplit
```

で利用可能なら十分である。共有 aggregator の変更が必要な場合のみ最小変更とし、理由を report に記録する。

## 8. 実装内検証

対象 module のローカル build を行い、実装が Lean に認可されるところまで確認する。

GitHub の commit、push、PR 操作、CI 起動・確認は行わない。それらは User の受け渡し工程である。

## 9. 実装報告

次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-003.md
```

最低限、次を記録する。

```text
- 再利用した実在 API
- 追加・変更した module
- 新規 theorem surface
- gcd spine の正確な仮定
- non-exceptional separation の証明経路
- valuation concentration theorem の正確な仮定
- `UniqueFactorizationGN` を import したか、避けたか、その理由
- ローカル build 結果
- FLT7 / 共有領域を変更していないこと
- 次 checkpoint 候補
```

## 10. 停止条件

```text
Outcome A:
  gcd boundary/GN divides exponent、overlap forces exception、
  non-exceptional boundary separation、valuation concentration が完成した。

Outcome B:
  gcd spine と separation は完成したが、valuation wrapper の import または
  仮定整合に不足 API がある。最小 blocker を report に固定した。

Outcome C:
  current source に同等 theorem が既に存在し、ABC wrapper だけで十分だった。
  最薄 theorem surface と重複回避判断を report に固定した。
```

どの Outcome でも、実装・ローカル検証・`report-003.md` 作成後に停止し、User へ結果を返す。
次 checkpoint へ自動進行しない。※ただし、ユーザーの意向を最優先とする。
