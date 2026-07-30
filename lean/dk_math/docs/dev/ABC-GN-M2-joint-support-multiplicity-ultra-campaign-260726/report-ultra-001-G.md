# Ultra-001G Report — Uniform budget obstruction

Date: 2026-07-26  
Status: **exact final obligation isolated / unconditional construction not proved**

## Kernel-fixed reduction

以下は production theorem として完成した。

```lean
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
Triple.nonExceptionalChannelMassBudget_iff_log_GN_le
abc_of_GNOddPrimeJointContract
```

prime exponent の exact radical identity により:

```text
joint pressure budget
  <->
S + E <= ρ R + C
```

である。さらに odd-prime exact accounting により:

```text
S + E <= ρ R + C
  <->
log GN <= ρ R + C + log(exceptional support product)
```

となる。exceptional support product は指数 `p` の radical に吸収される
有限項だが、`S+E` の一様係数問題は残る。

## Exact missing theorem

公開 ABC statement を閉じるため残る最小 production obligation は:

```lean
theorem construct_GNOddPrimeJointContract
    (ε : ℝ) (hε : 0 < ε) :
    ABCGNOddPrimeJointContract ε
```

に相当する無条件構成である。

この contract が得られれば:

```text
construct contract
  -> abc_of_GNOddPrimeJointContract
  -> raw-variable ABC statement
```

となり、`a=0`、`b=0`、positive case は全て閉じている。

## なぜ deterministic remainder ではないか

既存 return theorem:

```text
(p - 1) log c <= log GN
```

と margin:

```text
ρ <= (p - 1)(1 + ε)
```

を合わせると、上の uniform joint contract は正の ABC triple に対する
ABC inequality を直接含んでいる。従ってこれは会計 API の不足ではなく、
campaign の最終算術不等式そのものである。

## 攻撃 lane の監査結果

- layer-cake は multiplicity を同じ prime の高次 support として exact に
  再計上するが、新しい異なる prime を生成しない。
- weighted pincer の heavy branch は deep prime witness を返すが、それを
  排除しない。
- exact order は `p ∣ q-1` を与えるが valuation depth を制限しない。
- primitive divisor / Zsigmondy は fresh prime の存在を与えても
  valuation `= 1` を与えない。
- Hensel uniqueness は deep lift の不存在を意味しない。
- PrimitiveSet / Petal の現行 multiplicity budget endpoint は必要な budget
  または noncollision/no-lift 条件を入力として要求する。
- `ZsigmondyCyclotomicResearch` を経由する unconditional-looking endpoint は
  `sorry` 依存を含むため使用しない。

## Final flag

`abc_main_axiom` は削除していない。無条件 joint contract が証明されて
いない状態で削除または置換すれば、victory condition と trust boundary の
両方に反する。

本 report は `ULTRA_FINAL_REPORT.md` ではない。公開 `abc_main` の
project-axiom dependency は残っている。
