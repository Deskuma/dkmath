# Ultra-001H Report — raw-variable endpoint と `abc_main` 監査

Date: 2026-07-26  
Status: **raw endpoint transport complete / `abc_main` replacement blocked**

## Production endpoint

Module:

```text
DkMath.ABC.GNJointPressureOddPrime
```

Theorem:

```lean
abc_of_GNOddPrimeJointContract
```

この theorem は一様な:

```lean
ABCGNOddPrimeJointContract ε
```

から、既存 `abc_main` と同じ raw-variable statement:

```lean
∃ K : ℝ, 1 ≤ K ∧
  ∀ a b c : ℕ, a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)
```

を返す。

## Endpoint split

実装は三つの場合を全て閉じている。

```text
a = 0  -> coprime 0 b -> b = 1 -> c = 1
b = 0  -> coprime a 0 -> a = 1 -> c = 1
0 < a and 0 < b -> abc_positive_of_GNOddPrimeJointContract
```

従って、positive triple から raw-variable surface への transport は残って
いない。

## Replacement audit

`abc_main` の置換に必要な唯一の未構成入力は:

```lean
∀ ε, 0 < ε → ABCGNOddPrimeJointContract ε
```

である。Ultra-001G で確認した通り、この入力は exact accounting と return
bridge を通じて正の ABC inequality を直接含む。既存 API から機械的に生成
できる補助 contract ではない。

このため:

```text
abc_main                    unchanged
abc_main_axiom              retained
ULTRA_FINAL_REPORT.md       not emitted
```

とした。未証明 contract を隠して `abc_main` を置換することは、campaign の
victory condition と trust boundary の両方に反する。

## Axiom audit

次の production endpoints は全て:

```text
propext
Classical.choice
Quot.sound
```

のみに依存する。

```lean
Triple.rad_gnPowerLift_eq_rad_mul_nonExceptionalSupport_of_prime
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
abc_of_GNOddPrimeJointContract
GNNonExceptionalValuationExcess_eq_sum_depthMass
Triple.GNNonExceptionalValuationExcess_le_log_product_or_exists_deepPacket
Triple.mod_eq_one_of_mem_GNNonExceptionalSupport
```

対して公開 theorem の audit は:

```text
DkMath.ABC.abc_main
  -> propext
  -> Classical.choice
  -> Quot.sound
  -> DkMath.ABC.abc_main_axiom
```

となる。これは victory 未達を意図通り可視化した結果である。

## Local verification

```text
lake build DkMath.ABC.GNJointPressureOddPrime DkMath.ABC
Build completed successfully (8380 jobs).

lake build DkMath
Build completed successfully (8750 jobs).

git diff --check
clean
```

既存の推移的 dependency
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` にある `sorry` warning は
replay されるが、上記新規 endpoints の axiom audit に `sorryAx` は現れない。
