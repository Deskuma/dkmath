# source-constraint-frontier-019 — actual core への制約の不足

2026-10-14。Outcome B。same packet p の actual norm packet を K、m=K.innerSndRoot、M=|m|、A=innerRoot.fst、B=innerRoot.snd とする。signed B=7^4*m^7 であり、M を用いると |B|=7^4*M^7。Q=p.signedDepth.quotientRoot は M とは別である。

| 条件 / 実 source provenance | 仮定の種類 | ledger 単独より追加されるもの | actual M への評価 |
|---|---|---|---|
| M*N=V*C、Coprime M N、正値、7-unit、Coprime V C; AllocationThreshold / SourcePrimeValuationLedger | bare p | scalar ledger の内容 | 841モデルは全て満たす |
| IsCoprime A B; QuadraticInnerRoot.innerRoot_coordinates_isCoprime | bare K.quadratic | actual integral coordinates の primitive 性 | A の存在を model は供給しない。M の prime/cofactor 分類は得ない |
| signed B=7^4*m^7; K.innerSnd_eq | bare K | actual coordinate と actual core の等式 | 深さ4と7∤Mが既存。m の他素因子を制限しない readout |
| norm(innerRoot)=residualNormRoot; innerRoot_norm_eq / TraceOneQuadratic.norm | bare K.quadratic | A²+A*B+2B² という positive-definite norm、normの7-unit | scalar model は normroot や A を与えない。別 root の値を M と同定しない |
| leftCubic(A,B)=leftRoot^7、rightCubic(A,B)=rightRoot^7; K fields / norm_leftSource_eq / norm_rightSource_eq | bare K | 同じ A,B 上の2つの signed seventh-power norm 条件 | 連立条件から A,leftRoot,rightRoot を消去して M-only restriction を得る証明が未供給 |
| rightRoot^7−leftRoot^7=7*A*B*(A+B); signedRootGap_seventhPower_eq | bare K | 実際の signed additive integer identity | 右辺が natural seventh power とは証明されていない。Fermat chart と同じ式ではない |
| |sndCore(A,B)|=N^7; exists_inner_complementary_seventh_root | bare K、実際の witness N | complementary N を polynomial 座標へ接続 | 新しい test-only N>1。N=1 model は source tuple として不成立。M=841 自体は未排除 |
| sourceDifference=axis^6*normalizedWitness(m)^7; sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven | bare K | actual cubic ring equation、units/axis を保持 | natural complement の literal sixth power や small cofactor bound ではない |
| rhs theta depth13、coprime gap/quotient cores、cores_product_associated_pow_seven; RealCubicAxisDrop | actual depthLedger within p | ramified axis 除去と associated seventh powers | この axis 深さは7-unitから既存。arbitrary non7 prime を usable prime へ強制する条件ではない |
| d*Q=A*(A+B)*m^7; signedDepth.normalizedEquation | bare p | actual signed gap root d、Q と m の連結 | Q は m と関連するが等しくはない。Q supportをM supportと同定しない |
| oriented carrier exact valuation / real-pair gcd load splitting | actual p；関係する family/prime support を保持 | Q に属する norms、ideals、loadsの分配 | targeted inspectionでは M-only restriction の追加を確認できず |
| full-core loaded absorption | p + h21:∃a,c21=a^7 と h22:∃b,c22=b^7 | full cores の associated seventh powers | cell hypotheses は bare p の無条件結論でない |
| 343<M; internalDepthFourReconstruction_core_gt_343 | p + hrec | exact receiver の coarse size | bare source restriction と数えない |
| finite chart at carrier | reconstruction/pack/certificate が必要 | natural primitive additive endpoints | gate017の未供給存在。今回再探索していない |

`RamifiedSecondCoordinateCanonicalSplit.vertical_coprime_compensation_residual` と actual quadratic `compensationCore_eq` は Coprime V C の既存根拠であり、source-only である。しかし gate018 の exclusivity を再掲するだけでは今回の独立制約に数えない。

## 指定モデルをどこまで分離したか

M=841,N=1,V=M,C=1 は scalar ledger を満たす。ℓ∣M の prime は29だけで、Nat.Coprime 7 28 は偽。従って ledger は gate016 の usable prime を強制しない。

今回の `sourceComplement_ne_one` は、同一 source 座標の cubic factorization と非零性を使い N=1 を否定する。指定された四つ組の source realization は阻まれるが、M=841 を別 N と共に realization できるかは未検証・未証明。この違いを保つ。

## 最初の missing sharpening

本来 source が満たす連立式は存在している。欠けているのはそこから A、signed roots、他のsource factors を消去し、Mだけに適用できる independent condition を証明する段階である。例えば gate016を使う経路なら、actual p のみから

```text
M=c*ℓ^n,
c≤343, n>0, ℓ prime, ℓ≠2,7, Nat.Coprime 7 (ℓ−1)
```

を得る sharpening が必要だが、今回その命題の成立自体を保証する証拠はない。これを新仮定・axiom・予定済み theorem として追加していない。

別の descent 経路を選ぶなら、既存の signed norm gap を positive natural Fermat chart に結ぶ追加の exact-power/orientation 証明と、その route に適用できる well-founded measure の減少が必要となる。既存 inner depth5→4 は代数座標の減少であって、counterexample endpoint の構成ではない。

戦略的一時停止と設計の再検討を提案する。次を始める前に「どの独立した source 条件を使って、どの変数を消去し、どの M-only contradiction または measure を得るのか」を具体化する必要がある。追加 modulus や同値な ledger wrapper の生成を、その代用にしない。
