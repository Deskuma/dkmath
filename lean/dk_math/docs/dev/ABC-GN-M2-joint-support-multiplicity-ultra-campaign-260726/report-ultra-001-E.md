# Ultra-001E Report — Support/depth pincer

Date: 2026-07-26  
Status: **finite dichotomy and witness packet complete**

## 実装

```lean
GNNonExceptionalValuationExcess_le_pred_mul_supportLogMass_of_cap
GNNonExceptionalValuationExcess_le_or_exists_deep
GNNonExceptionalValuationExcess_le_log_product_or_exists_deep
GNNonExceptionalDeepPrimePacket
Triple.GNNonExceptionalDeepPrimePacket_of_mem
GNNonExceptionalDeepPrimePacket.highLift
Triple.GNNonExceptionalValuationExcess_le_log_product_or_exists_deepPacket
```

任意の threshold `K` について:

```text
E <= (K - 1) * S
or
exists q in non-exceptional support,
  K + 1 <= factorization q
```

を `K=0` と空 support を含めて証明した。

## Heavy witness

後半の witness は:

```text
q prime
q ∤ p
q^(K+1) ∣ GN
q^(K+1) ∣ c^p - b^p
q^(K+1) ∣ lifted a-coordinate
q ∤ a*b*c
K+1 <= padicValNat q GN
padicValNat q (c^p-b^p) = padicValNat q GN
```

を一つの packet として返す。

## Boundary

pincer は完全な有限場合分けであり、heavy branch の rarity や contradiction
を主張しない。`K >= 1` なら high-lift packet になるが、その high lift を
排除する別 theorem は含まれない。
