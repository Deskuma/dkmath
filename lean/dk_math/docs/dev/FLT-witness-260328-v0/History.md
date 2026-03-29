# History

## History Log

Archive

- None

### 日時: 2026/03/28 22:23 JST

1. 目的:
   - `review-001`
     に従い、
     current same-`q` existential route
     `PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget`
     が本当に残るかを、
     まず反例で即検査する。
2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `counterexample_not_dvd_bodyCore_two`
     - `counterexample_not_dvd_bodyCore_three`
     - `counterexample_no_same_q_bodyCoreWitness`
     - `not_primeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget`
     を追加した。
   - 反例は
     `(d, x, u) = (5, 5, 7)`
     であり、
     `x + 1 = 6`
     の prime divisors が
     `2, 3`
     に限られることを
     `Nat.prime_dvd_prime_iff_eq`
     と `hqprime.dvd_mul.mp`
     で処理した。
3. 結論:
   - same-`q` existential route
     `PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget`
     も universal theorem としては偽だと Lean 上で確定した。
   - したがって以後の本線は、
     arithmetic datum と body/core datum を
     同じ witness `q` に乗せる route ではなく、
     witness を分離した route
     へ切り替えるべき段である。
4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   を完了まで待って実行し、成功を確認した。
5. 失敗事例:
   - `PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget`
     に続き、
     `PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget`
     も反例で偽となった。
6. 次の課題:
   - arithmetic witness と body/core witness を分離した
     two-witness existential route を theorem 名として切り出す。
   - その body/core witness を primitive packet descent へ渡す
     clean interface を置く。

### 日時: 2026/03/30 02:24 JST

1. 目的:
   - `review-002`
     に従い、
     same-`q` route を正式に捨てた後の本線を
     theorem 名の上でも
     two-witness existential route
     へ切り替える。
   - あわせて、
     body/core witness を
     primitive packet descent / existence mainline
     へ渡す clean interface を
     missing bridge として切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceTarget`
     - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
     - `PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget`
     - `PrimeGe5BranchAExceptionalBodyCoreWitnessToPrimitivePacketDescentTarget`
     - `PrimeGe5BranchAExceptionalBodyCoreWitnessToExistenceMainlineTarget`
     を追加した。
   - あわせて
     - `primeGe5BranchAExceptionalBodyCoreWitnessExistence_of_selectedCoreWitness`
     - `primeGe5BranchAExceptionalPracticalTwoWitnessConcrete_of_witnessSupply_and_bodyCoreWitness`
     - `primeGe5BranchAExceptionalPracticalTwoWitnessConcrete_of_selectedCoreWitness`
     - `primeGe5BranchAExceptionalExistenceMainline_of_bodyCoreWitnessExistenceBridge`
     - `primeGe5BranchAExceptionalExistenceMainline_of_twoWitness_and_bodyCoreBridge`
     - `primeGe5BranchAPrimitivePacketDescent_of_bodyCoreWitnessExistenceBridge`
     - `primeGe5BranchAPrimitivePacketDescent_of_twoWitness_and_bodyCoreBridge`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     two-witness / body-core bridge 用 alias と adapter を追加した。

3. 結論:
   - current canonical route は、
     もはや
     same-`q` witness ではなく、
     `arithmetic witness`
     と
     `body/core witness existence`
     を分離した two-witness route として読める。
   - さらに、
     packet descent / mainline 側の次の missing math は、
     `bodyCore witness existence`
     から downstream へ渡す clean bridge
     1 本だと整理できた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - same-`q` route に戻る新しい定理は追加していない。
   - 以後、
     `PrimeGe5BranchAExceptionalPracticalSelectedCoreOnDatumConcreteTarget`
     と
     `PrimeGe5BranchAExceptionalPracticalBodyCoreWitnessConcreteTarget`
     は false route として保持する。

6. 次の課題:
   - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
     の concrete 本体を切る。
   - 併せて、
     body/core witness から
     primitive packet descent / existence mainline
     へ渡す clean bridge の statement を
     より薄い数論形へ正規化する。

### 日時: 2026/03/30 02:42 JST

1. 目的:
   - `dev-report.md`
     の指摘どおり、
     current body-only witness route 自体が false かを
     先に Lean 上で確定する。
   - false なら two-witness canonical target も同時に閉じる。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `counterexample_u_one_bodyCore_eq_one`
     - `not_primeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
     - `not_primeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget`
     を追加した。
   - 反例は
     `(d, x, u) = (5, 5, 1)`
     である。
     このとき
     `cyclotomicPrimeCore 5 1 (1 - 1) = 1`
     なので、
     それを割る prime witness は存在しない。

3. 結論:
   - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
     は false。
   - したがって
     `PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget`
     も false。
   - same-`q` route に続き、
     body-only witness / two-witness route も
     current statement のままでは本線にならないと Lean 上で確定した。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - `u = 1`
     では
     `cyclotomicPrimeCore d 1 (u - 1) = 1`
     となり、
     body/core witness existence は構造的に壊れる。

6. 次の課題:
   - `cyclotomicPrimeCore d 1 (u - 1)` ではなく、
     `cyclotomicPrimeCore d x u`
     あるいは
     `boundaryCyclotomicPrimeCore .right d x u`
     を first target に据えた route へ切り替える。
   - arithmetic core / boundary core 側の存在 theorem を
     Mathlib.FLT 非依存で直接立てる。

### 日時: 2026/03/30 03:03 JST

1. 目的:
   - `proof-004`
     の提案どおり、
     false と確定した body-only / two-witness route を離れ、
     current canonical route を
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     へ戻す。
   - その sanity check として、
     `(d, x, u) = (5, 5, 1)`
     で boundary route が実際に生きていることを Lean で確認する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `PrimeGe5BranchAExceptionalBoundaryCoreWitnessConcreteTarget`
     を追加し、
     current canonical route を
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     と同一視した。
   - あわせて
     `primeGe5BranchAExceptionalBoundaryCoreWitness_sanity_u_one`
     を追加し、
     `boundaryCyclotomicPrimeCore .right 5 5 1`
     に対して
     `q = 311`
     が concrete witness になることを示した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     `BranchAExceptionalBoundaryCoreWitnessConcreteAdapterTarget`
     を追加した。

3. 結論:
   - `cyclotomicPrimeCore d 1 (u - 1)` route は false だが、
     `boundaryCyclotomicPrimeCore .right d x u`
     route は
     `(5,5,1)`
     で既に concrete witness を持つ。
   - したがって、
     current proof exploration の本線は
     arithmetic-core / boundary-core route
     だと見てよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
     と
     `PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget`
     は false のまま保持する。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     の concrete 本体を直接攻める。
   - 具体的には
     `cyclotomicPrimeCore d x u ≡ d * u^(d-1) [MOD p]`
     と
     `cyclotomicPrimeCore d x u ≡ d [MOD d^2]`
     系の補題へ落とす。

### 日時: 2026/03/30 03:26 JST

1. 目的:
   - `proof-004`
     の step 1 をそのまま Lean 化し、
     boundary-core route の最初の arithmetic kernel を実装する。
   - 具体的には、
     `q ∣ x`
     のもとで
     `boundaryCyclotomicPrimeCore .right d x u`
     が
     `d * u^(d-1)`
     に合同であること、
     および
     `q ∣ core ∧ q ∣ x`
     なら
     `q = d`
     であることを切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_boundary_core_modEq_mul_u_pow_pred_of_dvd`
     を追加した。
     これは
     `x + u ≡ u [MOD q]`
     を各項へ入れて
     `boundary core ≡ d * u^(d-1) [MOD q]`
     を返す補題である。
   - 同ファイルに
     `exceptional_boundary_prime_dvd_x_and_core_imp_eq_d`
     を追加した。
     これは
     `q` prime,
     `q ∣ x`,
     `q ∣ boundary core`
     のとき
     `q = d`
     を返す。
   - さらに
     `exceptional_boundary_prime_not_dvd_core_of_dvd_x_ne_d`
     を追加し、
     `q ≠ d`
     な prime は
     `x`
     を割るなら
     boundary core を割れない、
     という proof-004 step 1 の否定形も API 化した。

3. 結論:
   - boundary route の arithmetic 側は、
     少なくとも
     「`x` の素因子が boundary core に残るのは distinguished prime `d` だけ」
     までは Lean 上で確定した。
   - したがって、
     残る本丸は
     `d`
     自身の寄与を 1 回だけ剥がす
     `mod d^2`
     / valuation 側である。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 備考:
   - 今回の実装は
     `Mathlib.FLT`
     を参照していない。
   - warning は既存の `sorry` 群に加え、
     `primeGe5BranchAExceptionalBoundaryCoreWitness_sanity_u_one`
     内の
     `native_decide`
     由来の linter warning が残っている。

6. 次の課題:
   - `core ≡ d [MOD d^2]`
     あるいは同等の
     `d ∣ core` と `¬ d ∣ core / d`
     を返す補題を置く。
   - その上で
     `core / d`
     の prime divisor を取り、
     今回の step 1 補題と組み合わせて
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     を直接閉じる。
