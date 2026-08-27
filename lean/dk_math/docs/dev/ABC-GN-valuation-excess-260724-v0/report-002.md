# ABC–GN Checkpoint 002 Report

作成日: 2026-07-24

Outcome: A

## 1. 再利用した実在 API

- `DkMath.ABC.Triple.gnPowerLift_sum`
  - `T.a * GN n T.a T.b + T.b ^ n = T.c ^ n`
- `DkMath.CosmicFormulaBinom.GN_ne_zero_nat_of_two_le`
  - `2 ≤ n`, `0 < a`, `0 < b` から `GN n a b ≠ 0`
- `padicValNat.mul`
  - 両因子の非零条件の下で積の valuation を加法化する。
- `padicValNat.eq_zero_of_not_dvd`
  - `¬ q ∣ a` から `padicValNat q a = 0`
- `Nat.add_sub_cancel_right`
  - GN power lift の加法式を差冪 factorization に戻す。

調査した既存の近接 API:

- `DkMath.NumberTheory.GcdNext.padicValNat_factorization`
- `DkMath.NumberTheory.Gcd.padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap`
- `DkMath.NumberTheory.PrimitiveBeam.primitive_prime_not_dvd_boundary`
- `DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_eq_GN`
- `DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_boundaryMass_eq_zero`

既存 `GcdNext.padicValNat_factorization` は一般の `a ^ d - b ^ d` 座標で
同じ積公式を提供する。今回の ABC wrapper では checkpoint 001 の
`gnPowerLift_sum` が直接 factorization を与えるため、より薄く
`padicValNat.mul` を再利用した。

## 2. 追加・変更した module

追加:

```text
DkMath/ABC/GNValuationSplit.lean
```

既存 module と共有 aggregator は変更していない。公開面は直接、

```lean
import DkMath.ABC.GNValuationSplit
```

で利用する。

## 3. 新規 theorem surface

```text
DkMath.ABC.Triple.powerDiff_eq_boundary_mul_GN
DkMath.ABC.Triple.padic_powerDiff_eq_boundary_add_GN
DkMath.ABC.Triple.padic_gnPowerLift_a_eq_boundary_add_GN
DkMath.ABC.Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
```

## 4. 各 theorem の正確な仮定

### `Triple.powerDiff_eq_boundary_mul_GN`

```lean
(T : Triple) (n : ℕ)
```

結論:

```lean
T.c ^ n - T.b ^ n = T.a * GN n T.a T.b
```

指数下界・positivity・prime 条件は不要で、`n = 0` も含む。

### `Triple.padic_powerDiff_eq_boundary_add_GN`

```lean
(T : Triple) {n q : ℕ}
(hn : 2 ≤ n)
(ha : 0 < T.a)
(hb : 0 < T.b)
(hq : Nat.Prime q)
```

結論:

```lean
padicValNat q (T.c ^ n - T.b ^ n) =
  padicValNat q T.a + padicValNat q (GN n T.a T.b)
```

### `Triple.padic_gnPowerLift_a_eq_boundary_add_GN`

仮定は full split と同じ。結論は lifted triple の左座標へ直接作用する。

```lean
padicValNat q (T.gnPowerLift n).a =
  padicValNat q T.a + padicValNat q (GN n T.a T.b)
```

### `Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary`

full split の仮定に加えて、

```lean
(hq_boundary : ¬ q ∣ T.a)
```

を要求し、結論は次となる。

```lean
padicValNat q (T.c ^ n - T.b ^ n) =
  padicValNat q (GN n T.a T.b)
```

## 5. 非零条件の構成

`padicValNat.mul` に必要な左因子の非零条件は、

```lean
Nat.ne_of_gt ha : T.a ≠ 0
```

で得た。

右因子は既存 theorem をそのまま使った。

```lean
GN_ne_zero_nat_of_two_le hn ha hb :
  GN n T.a T.b ≠ 0
```

素数条件は、

```lean
haveI : Fact q.Prime := ⟨hq⟩
```

として Mathlib の積公式へ渡した。

## 6. primitive wrapper

実装しなかった。

既存の

```lean
PrimitivePrimeFactorOfDiffPow q a b d
primitive_prime_not_dvd_boundary
primitive_prime_padic_eq_GN
```

は、`a := T.c`, `b := T.b` と置けば ABC boundary
`T.c - T.b = T.a` へ接続できる。しかし、その wrapper のためだけに
`PrimitiveBeam` と Zsigmondy research 層を ABC の最小 valuation module
へ import すると依存が大きくなる。checkpoint 002 の一般
`¬ q ∣ T.a` specialization は primitive prime より広く、必要な差し替え口を
既に提供するため、primitive 接続は後続 checkpoint 側へ残した。

## 7. 数学的に閉じたこと

ABC triple の差冪を、

```text
boundary contribution  v_q(T.a)
kernel contribution    v_q(GN n T.a T.b)
```

へ正確に分離した。さらに boundary を割らない prime では boundary
contribution が 0 となり、差冪の valuation 全体が GN kernel 上に移る。

この checkpoint は exceptional prime、valuation excess、ABC quality の
いずれも定義・主張していない。

## 8. ローカル build

実行:

```text
lake build DkMath.ABC.GNValuationSplit
```

結果:

```text
Build completed successfully (8263 jobs).
```

`git diff --check` は成功した。新 module に `axiom`, `sorry`,
`native_decide` はない。

instruction-002 に従い、commit、push、PR 操作、GitHub CI は行っていない。

## 9. FLT7 / 共有領域

`DkMath/FLT/Seven/**`、FLT7 専用 docs、FLT module、共有 aggregator は
参照・変更していない。変更は新規 ABC module と本 report のみである。

## 10. 次 checkpoint 候補

次 checkpoint へは自動で進まない。賢狼レビュー後の最小候補は、
この split を入力として `q ∣ n` / `q ∤ n` を分離し、指数由来の
exceptional layer と non-exceptional GN valuation を theorem surface 上で
区別することである。
