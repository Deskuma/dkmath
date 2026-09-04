# FLT3U-004 実装報告: Signed Three-Adic Routing and Exact Power Split

## 1. mod 9 classification

`SignedThreeAdic.lean` に `Fin 9` 上の kernel-checked finite classification を追加した。
`a^3+b^3=c^3` の mod 9 形式から `3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c` を得て、
`Nat.Coprime a b` と三つの pairwise exclusion を合わせ、3 の所在を一意に
`a`, `b`, `c` のいずれかへ分類する。

## 2. 三つの orientation

`SignedThreeAdicOrientation` として `.a`, `.b`, `.c` を導入した。

- `.a`: carrier `c-b`, residual `S0_nat c b`, distinguished `a`,
  `alpha = eisensteinCoord (-c) (-b)`
- `.b`: carrier `c-a`, residual `S0_nat c a`, distinguished `b`,
  `alpha = eisensteinCoord (-c) (-a)`
- `.c`: carrier `a+b`, residual `a^2+b^2-a*b`, distinguished `c`,
  `alpha = eisensteinCoord (-a) b`

いずれも `alpha.snd - alpha.fst = carrier` の同じ符号規約である。

## 3. common packet

`SignedThreeAdicPacket a b c` を追加した。packet は正の carrier/residual/
distinguished、因数分解、Eisenstein norm、signed gap、`3` の carrier と
distinguished への divisibility、residual の mod 9 値を保持する。
さらに正規化に必要な `Nat.gcd carrier residual = 3` を kernel-checked field
として保持する。

## 4. residual mod 9

非 3-divisible な二変数について、差 orientation では cubic residues の一致、
sum orientation では cubic sum の消滅を `Fin 9` の有限計算で検証し、各 residual が
正確に `residual % 9 = 3` となることを実装した。

## 5. `padicValNat` の追加有無

`padicValNat 3 residual = 1` は追加していない。今回の exact split に必要な
`3 ∣ residual` と `¬ 9 ∣ residual` は `residual % 9 = 3` から直接導出でき、
新たな public field としては冗長だからである。

## 6. exact gcd

差 orientation は既存の
`DkMath.Petal.gcd_sub_S0_nat_eq_gcd_sub_three` に接続し、carrier の 3-divisibility
から gcd を 3 に固定した。sum orientation は
`(a+b)^2 = residual + 3*a*b` と `Coprime (a+b) (a*b)` を用いて共通因子が
3 を割ることを示し、residual と carrier の双方の 3-divisibilityと合わせて
`gcd carrier residual = 3` を得た。

## 7. power split surface

`SignedThreeAdicPowerSplit.lean` に次を追加した。

```text
structure SignedThreeAdicPowerSplit (a b c : ℕ) : Type where
  packet : SignedThreeAdicPacket a b c
  A B : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  coprime_A_B : Nat.Coprime A B
  carrier_eq : packet.carrier = 3^2 * A^3
  residual_eq : packet.residual = 3 * B^3
  distinguished_eq : packet.distinguished = 3 * A * B
  three_not_dvd_B : ¬ 3 ∣ B
```

## 8. A/B equations

既存の Nat/GCDMonoid の generic theorem
`exists_eq_pow_of_mul_eq_pow` を用い、gcd 3 を除いた coprime product を
cube ごとに分離した。結果は
`carrier = 9*A^3`, `residual = 3*B^3`, `distinguished = 3*A*B` である。

## 9. `3 ∤ B`

`residual % 9 = 3` と `residual = 3*B^3` を比較し、`3 ∣ B` なら
`9 ∣ residual` となる矛盾から `three_not_dvd_B` を得た。

## 10. signed alpha convention

全 orientation で packet の alpha は上記の負符号を含む固定 convention を使用し、
norm は residual、signed coordinate gap は carrier に一致する。

## 11. future beta sign

`future_signed_beta_snd_pos` を追加し、004B で将来 `alpha = lambda * beta` を
構成できた場合に対応する beta の第二座標候補 `3*A^3` が正であることを記録した。
この checkpoint では lambda quotient 自体は構成していない。

## 12. imports

新規 module の直接 import は次の通りである。

```text
SignedThreeAdic.lean:
  DkMath.FLT.Three.EisensteinSubstrate
  DkMath.Petal.GcdBridge

SignedThreeAdicPowerSplit.lean:
  DkMath.FLT.Three.SignedThreeAdic
  Mathlib.Algebra.GCDMonoid.Basic
```

FLT5 の production module、`DkMath.FLT.Main`、`DkMath.FLT.Basic`、
`DkMath.FLT.Core`、provisional な GEisenstein bridge は import していない。

## 13. focused build

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.SignedThreeAdic
lake build DkMath.FLT.Three.SignedThreeAdicPowerSplit
```

両方とも `Build completed successfully (8713 jobs).` で終了した。新規2 module
自身には warning はなく、依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning
は残っている。

## 14. axiom / forbidden-construct audit

新規2 source に `sorry`、`axiom`、FLT3 完結 theorem、FLT5 production import はない。
主要 theorem の `#print axioms` は packet/power-split constructor で
`[propext, Classical.choice, Quot.sound]`、future sign theorem で `[propext]`
のみであり、`sorryAx` は含まれない。

## 15. outcome

`exists_signedThreeAdicPacket_of_primitive_solution` と
`signedThreeAdicPowerSplit_of_primitive_solution` により、正の primitive
solution から packet と exact power split を得る surface を実装した。
004A の終端条件

```text
carrier = 9*A^3
residual = 3*B^3
distinguished = 3*A*B
Nat.Coprime A B
¬ 3 ∣ B
```

および alpha の norm/gap 条件を満たす。lambda quotient、共役 coprimality、
UFD/PID、sector、strict descent、最終 FLT3 theorem は次 checkpoint 以降の
non-goal として残した。
