# NOTE-032: 一般 `hno` の証明経路監査

更新日: 2026-11-01。`__REVIEW.md` を参考に実ソースを照合し、局所入力を形式化した。

## 現在の証明境界

**位数 `p` の Galois 固定幾何点と、同じ点についての2進・3進の全延長付値環での
零成分外性は実装済み。一般 `hno` は未完成である。**

```text
Cofixed line, p ≥ 5, Even S.b
  → integer quotient W, W.Δ ≠ 0
  → rational Q with addOrderOf Q = 2*p
  → P = baseChangePoint (2 • Q), addOrderOf P = p, Galois fixed
  → 2 ∣ W.Δ, 2 ∤ W.c₄; 3 ∣ W.Δ, 3 ∤ W.c₄
  → for every A above 2 or 3, P is outside the smooth zero component
                                                               [今回までで実装済み]
  → Mazur Step Three: other bad primes ℓ ≠ p                  [大域本体が未移植]
  → later cofixed torsion-tower/global argument                [未接続]
  → general hno                                              [未完成]
```

## 外部公開定理の正確な入力と出力

ローカルの `fermats-last-theorem` ソースを確認した。参照コミットとファイルの
SHA-256 は `evidence/note032-mazur-global-dependencies.json` に保存した。

`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt` は以下を受け取る。

- 素数 `p`、`p ∉ {2, 3, 5, 7, 13}`。
- 整数モデル `W` と `W.Δ ≠ 0`。
- 幾何点 `P`、Galois 固定性、`addOrderOf P = p`。
- `2 ∣ Δ`, `2 ∤ c₄`、2上の任意の `LiesOverPrime` 付値環での零成分外性。
- `3 ∣ Δ`, `3 ∤ c₄`、3上の任意の `LiesOverPrime` 付値環での零成分外性。
- 対象の素数 `ℓ` ごとの `ℓ ≠ p`, `ℓ ∣ Δ`, `ℓ ∤ c₄` と付値環 `A`。

その結論が **対象の `A` における零成分外性** である。全 bad prime の零成分外性を
事前入力にしてはいけない。`Definitions/Def_ModularCurve_MazurStepThree.lean` の
命題仕様は全素数での半安定性を要求するが、上記の公開定理は対象 `ℓ` の局所条件を
個別に要求する。今回の局所終点は `p ≥ 5` で成立し、外部定理の例外素数条件を
消去したことにはならない。

## 実装済みの接続

| モジュール / 定理 | 内容 |
| --- | --- |
| `FiniteAdditiveTorsionQuotient.addOrderOf_two_nsmul_eq_prime_of_addOrder_eq_two_mul_prime'` | `ord Q = 2*p` だけから `ord (2 • Q) = p`。倍の非零性を内部供給 |
| `FreyRationalTwoPTorsion.residual_cofixed_implies_geometric_rational_prime_torsion` | 同じ有理 `Q` の倍を base-change し、厳密位数と固定性を公開 |
| `WeierstrassNodalCenterCharThree.candidate_defect_identity` | 任意の標数3の体で `b₂³ * equationDefect = Δ` |
| `WeierstrassNodalCenterCharThree.singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero` | `Δ = 0`, `c₄ ≠ 0` から有理特異中心を構成 |
| `EllipticLocalComponentObstruction.localValuationSubring_double_not_mem_zeroComponent_of_singularCentre` | 実際の有理局所住所で `#E_sm ≤ q+1 < p` を使い倍の零成分所属を排除 |
| `FreyTriadicComponentObstruction` | Cofixed → `3 ∣ abc` → 3進剰余不変量 → 倍の零成分外性 |
| `EllipticRationalLocalTransport.hasSmoothReduction_integer_baseChange_iff` | 同じ素数上の任意の延長付値環へ滑らかな還元を保存・反映 |
| `EllipticRationalLocalTransport.hasSmoothReduction_iff_zero_or_exists` | 外部 `InZeroComponentAt` の零点または有限座標という仕様との同値 |
| `FreyMazurLocalInputs.residual_cofixed_mazur_integer_invariants` | `Δ ≠ 0` と2・3での整数不変量の可除性 |
| `FreyMazurLocalInputs.residual_cofixed_implies_geometric_prime_torsion_local_inputs` | **同じ一つの位数 `p` 固定幾何点**に2・3上の全局所条件を合成 |

固定性は既存 `pointAction_baseChange` を再利用した。新たな Galois 固定性理論は不要。
輸送では有理数とその逆数の付値環所属、および偏微分の非単元性を比較する。
代数閉包上の剰余体を有限体と同一視せず、有限濃度を輸送の仮定にもしていない。

## 残る大域本体の依存

外部 `P2M/Sol/S_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean` の
`solution` は次を具体的に消費する。

1. `ModularCurve.heckeOperatorsCommuteBar` と実際の `heckeModuleBar`。
2. `eisensteinQuotientInvariantsFiniteAt_heckeModuleBar`。
3. `cuspidalClassSurvives_heckeModuleBar`。
4. `mazurQuotientSpecialization_heckeModuleBar`。
5. `moduliPointExists_jQuotVelu_of_mult_two`。
6. `tateCuspCriterion_jQuotVelu`。
7. cusp の次数と Galois 作用、Jacobian の divisor-class 計算。

特に、局所入力を受け取るだけでは 1–7 の数学は供給されない。現在の DkMath には
これらのモジュラー曲線用終点がない。Eisenstein 整数のノルム API はこの Hecke 商と
別の対象であり、代用できない。

外部 `Definitions.*`, `Theorems.*`, `P2M.*` を構文的に辿った輸入閉包は 11,111
モジュールだった。これは wrapper と utility を含み、最小移植量の主張ではない。
必要な接続の入口は上記 1–7 である。

さらに `S_FreyPackage_frey_no_cofixed_large` は、Step Three 後にも、慣性での局所
filtration、torsion tower、連続 extension 消滅、Frobenius の Cayley–Hamilton と
有限還元点群の計数を使う。この後半も `hno` 閉包から省略できない。

## 検証

実行した検証と結果は `evidence/validation-note032-mazur-local-inputs.txt` に記録する。
新しい定理の `#print axioms` と禁止構文走査は、今回の局所結果の検証であり、
未移植の大域定理や一般 `hno` の検証を意味しない。
