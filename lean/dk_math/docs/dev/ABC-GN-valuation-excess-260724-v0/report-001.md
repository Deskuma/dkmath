# ABC–GN Checkpoint 001 Report

作成日: 2026-07-24

Outcome: A

## 1. 調査で見つかった既存 API

- `DkMath.ABC.Triple`
  - `Triple` は `a`, `b`, `c`, `hsum : a + b = c`,
    `hcop : Nat.Coprime a b` を持つ。
- `DkMath.CosmicFormulaBinom`
  - `GN` は canonical `DkMath.CosmicFormula.GN` への compatibility wrapper。
  - `cosmic_id_csr'` が任意の `CommSemiring` 上で
    `(x + u) ^ d = x * GN d x u + u ^ d` を与える。
- `DkMath.NumberTheory.Gcd.GN`
  - `gcd_gap_GN_dvd_exp`
  - `coprime_boundary_GN_of_coprime_add_of_coprime_exp`
  - `coprime_gap_GN_of_not_dvd_exp_prime`
  - `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap`
- `DkMath.NumberTheory.PrimitiveBeam`
  - primitive prime から `GN` divisibility へ移す既存 bridge がある。
- `DkMath.NumberTheory.UniqueFactorizationGN`
  - boundary / kernel 分離と `padicValNat.mul` wrapper が既にある。
- `DkMath.ABC.MassBridge`
  - `supportMass = rad` と prime-channel family からの support 下界がある。
- `DkMath.ABC.ValuationFlowBridge`
  - primitive witness family から `supportMass` / `rad` 下界へ接続する。
- `DkMath.Petal.ABCBridge`
  - Petal label support から `rad (GN d x u)` 下界へ接続する。
- `padicValNat`
  - 積公式 `padicValNat.mul` は両因子の非零条件を要求する。
  - 冪公式は `DkMath.ABC.padicValNat_pow` から利用できる。

root の指示候補にあった `SUMMARY.md` は current branch に存在しなかった。
current source と上記 module を優先して調査した。

## 2. 追加した file と API

追加:

```text
DkMath/ABC/GNPowerLift.lean
```

新規 API:

```text
DkMath.ABC.Triple.gnPowerLift
DkMath.ABC.Triple.gnPowerLift_a
DkMath.ABC.Triple.gnPowerLift_b
DkMath.ABC.Triple.gnPowerLift_c
DkMath.ABC.Triple.gnPowerLift_sum
DkMath.ABC.Triple.gnPowerLift_coprime
```

`gnPowerLift` の座標は次である。

```text
a := T.a * GN n T.a T.b
b := T.b ^ n
c := T.c ^ n
```

## 3. 数学的に閉じたこと

任意の `T : Triple` と `n : ℕ` に対して、次を Lean で閉じた。

```text
T.a * GN n T.a T.b + T.b ^ n = T.c ^ n
Nat.Coprime (T.a * GN n T.a T.b) (T.b ^ n)
```

したがって、この三座標は再び `Triple` を構成する。指数 `n = 0` も
含めて仮定なしで成立する。

coprime certificate は `GN mod b` を再証明せず、次の短い経路で得た。

```text
Coprime a b
  -> Coprime (a + b) b
  -> Coprime c b
  -> Coprime (c ^ n) (b ^ n)
  -> Coprime (a * GN n a b) (b ^ n)
```

最後の段は GN 加法恒等式と gcd の加法不変性を使う。

## 4. 再利用した theorem

- `DkMath.CosmicFormulaBinom.cosmic_id_csr'`
- `Nat.coprime_add_self_left`
- `Nat.Coprime.pow`
- `Triple.hsum`
- `Triple.hcop`

一般 gcd / primitive / valuation module は API frontier の調査対象としたが、
今回の最短証明には import しなかった。

## 5. 実装しなかった候補と理由

- ABC 座標の `padicValNat` 分解:
  - 積公式には `a ≠ 0` と `GN n a b ≠ 0` が必要で、power lift 本体には
    不要な positivity / nonzero 仮定が増える。
  - instruction 001 の余力項であり、次 checkpoint で必要な statement shape
    と一緒に設計する方が薄い。
- primitive prime の境界 valuation 消滅 wrapper:
  - 既存の `Gcd.GN` と `ValuationFlowBridge` に一般形があり、今回重複する
    ABC wrapper は追加しなかった。
- aggregator import:
  - `DkMath.ABC` / `DkMath.ABC.Main` は解析・公理層まで含む重い入口である。
  - 循環と不要依存を避け、今回は
    `import DkMath.ABC.GNPowerLift` を最薄の公開面とした。
- ABC quality、valuation excess、`abc_main_axiom` 除去:
  - checkpoint 001 の禁止範囲なので扱っていない。

## 6. 検証結果

局所 build:

```text
lake build DkMath.ABC.GNPowerLift
Build completed successfully (8262 jobs).
```

差分監査:

```text
git diff --check
```

新 module に `axiom`, `sorry`, `native_decide` はない。

GitHub Lean CI:

```text
PR #67
Lean CI run #240
final conclusion: success
```

初回 attempt は Mathlib cache setup 中の `leantar` download が
`curl: (35) Recv failure: Connection reset by peer` で失敗し、Lean build
自体は skipped だった。同じ run の failed job を再実行し、full build は
成功した。

## 7. 次の最小 checkpoint 候補

次 checkpoint へは自動で進まない。賢狼レビュー後の候補は、lifted triple の
両座標が非零となる正確な条件を固定し、その条件下で

```text
padicValNat q (c ^ n - b ^ n)
  = padicValNat q a + padicValNat q (GN n a b)
```

を ABC 座標 wrapper として既存積公式へ接続することである。

## 8. Commit

実装 commit:

```text
742f2294 feat: add ABC GN power lift
```

## 9. 並行 FLT7 branch / 共有領域

`DkMath/FLT/Seven/**`、FLT7 専用 docs、FLT module、共有 aggregator は
変更していない。変更対象は新規 ABC module と本 report のみである。
