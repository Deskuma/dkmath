# FLT-Kummer-ClassGroup-Bridge Report 032: Stage 1 Coprimality 完成

※ これは作業 AI 自身によるレポートです。

**日時**: 2026/04/07 04:40 JST

## 戦況まとめ

### 今回達成したこと

1. **y ∈ P 分岐の contradiction を no-sorry で完成**
   - `coprime_span_of_nat_coprime`: Bezout → Ideal span coprimality
   - `false_of_nat_coprime_both_in_prime`: coprime naturals both in prime → False
   - `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq`: y ∈ P contradiction

2. **P | (p) 分岐の contradiction を 2 targets で完成**
   - `PrimeOverPEqualsZetaMinusOneTarget`: P | (p) ∧ P prime ⟹ P = (ζ-1)
   - `IntegerInZetaMinusOneIdealDivisibleByPTarget`: n ∈ (ζ-1) ∧ n ∈ ℤ ⟹ p | n
   - `noPrimeOverP_of_firstCase_of_chosenFactorInP`: first case + targets → False

3. **Prime (ζ-1) の Mathlib API 接続**
   - `zeta_sub_one_prime_of_p`: {p} 形式から Prime (ζ-1) を導出
   - `zeta_sub_one_ideal_isPrime`: (ζ-1) が prime ideal を生成

4. **Stage 1 coprimality theorem を完成**
   - `noPrimeOrY_of_firstCase_of_coprime`: P|(p)∨y∈P → False combiner
   - `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`: ★完成★

### 残る Open Targets (2本)

```lean
-- Target 1: 素イデアル因子分解 (p) = (ζ-1)^(p-1)
abbrev PrimeOverPEqualsZetaMinusOneTarget (K : Type*) ... : Prop :=
  ∀ {P : Ideal (𝓞 K)}, P.IsPrime → P ≠ ⊥ →
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) →
    P = Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))

-- Target 2: ノルム N(ζ-1) = p
abbrev IntegerInZetaMinusOneIdealDivisibleByPTarget (K : Type*) ... : Prop :=
  ∀ {n : ℕ}, (n : 𝓞 K) ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) → p ∣ n
```

### Mathlib API の見込み

- **Target 2**: `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` で N(ζ-1) = p が得られる
  - Chain: (ζ-1)|n ⟹ N(ζ-1)|N(n) ⟹ p|n^(p-1) ⟹ p|n

- **Target 1**: Prime ideal factorization API が必要
  - (p) = (ζ-1)^(p-1) (totally ramified) から P = (ζ-1)
  - Mathlib に直接 API があるか要確認

## Stage 1 → Stage 2 の接続

現在の flow:

```
chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack
  ↓ (coprimality)
cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime
  ↓ (span equality)
linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
  ↓ (existence boundary)
cyclotomicUnitNormalization_of_...
  ↓ (Stage 2: unit normalization)
Stage 3
```

## 次の一手

**判断分岐**: 2 targets を Mathlib で埋めるか、targets を仮定した形で進むか

- **Option A**: 2 targets を Mathlib API で埋める (deep cyclotomic theory)
  - 利点: Stage 1 が完全 no-sorry になる
  - リスク: Mathlib API の接続に時間がかかる可能性

- **Option B**: targets を仮定した形で Stage 2 → Stage 3 へ進む
  - 利点: 全体構造が先に見える
  - リスク: targets が埋まらないと最終的に閉じない

**推奨**: Option A を短時間試み、詰まったら Option B へ切り替え

## 結論

Stage 1 coprimality の **構造は完全に完成**。
残りは 2 つの deep cyclotomic targets の埋め立てのみ。

これらは Mathlib の cyclotomic number theory API で埋められる見込みが高い。
特に `norm_sub_one_of_prime_ne_two` が Target 2 の key API。
