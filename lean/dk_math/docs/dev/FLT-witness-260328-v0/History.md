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
