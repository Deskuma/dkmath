# NOTE-032: 一般 `hno` の証明経路監査

## 目的

局所成分群の拡張を先に進めるのではなく、完成済みの模範解答における
`frey_no_cofixed_large` と、DkMath の Cofixed 直線から得られる有理捩れ点を
比較する。未形式化の数学を完成済みと扱わず、一般 `hno` に必要な最短の接続を
固定する。

## 1. 模範解答の実際の終点

`fermats-last-theorem/PROOF-PATH.md` と
`P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean` を確認した。

大指数 `p ≥ 17` の Cofixed 排除は、単なる有理 torsion 分類ではない。構造は

```text
Galois-stable cofixed line
  → rational p-torsion point on the Frey quotient
  → MazurStepThree
  → nonzero point is outside every relevant zero component
  → Eisenstein quotient / component-group counting contradiction.
```

`MazurStepThree` は次を要求する仕様である。

- `p` は `2, 3, 5, 7, 13` 以外の素数。
- 整数 Weierstrass モデルの `Δ ≠ 0`。
- `Δ` を割る各素数で `c₄` は割れない。
- 代数閉包上の点 `Q` が Galois 固定。
- `addOrderOf Q = p`。
- `2`, `3`, および `p` 以外の判別式支持素数の各 valuation で `Q` が零成分外。

従って、外部証明は「一般楕円曲線に位数 `2p` の点がない」という Mazur の
rational-torsion 分類を直接呼び出していない。モジュラー曲線、Jacobian、
Eisenstein 商、Néron 成分群を含む専用の `MazurStepThree` 実装に依存している。

## 2. DkMath の既存入力

ワークスペースの定理検索とソースを確認した結果、次が既に利用できる。

| DkMath 定理 | 供給するもの |
| --- | --- |
| `residual_cofixed_implies_rational_two_p_torsion` | 商整数モデル上の有理点 `Q`、`addOrderOf Q = 2*p` |
| `residual_integer_target_multiplicative_at_two` | 2進での乗法的還元 |
| `residual_integer_target_multiplicative_at_bad_prime` | 条件付き bad-prime 乗法的還元 |
| `residual_integer_target_multiplicative_at_bad_place` | `q = 2` または `q ∣ abc` の局所還元 |
| `residual_cofixed_forces_small_prime_support` | `q < p` の bad-prime 支持 `q ∣ abc` |
| `residual_stable_line_eq_zeroComponent_at_two` | 2進の安定直線と零成分の一致 |
| `residual_cofixed_forces_dyadic_component_prime_order` | 2進抽象商に厳密位数 `p` の元 |
| `prime_dvd_finite_component_of_ker_le` | 有限標的写像の核包含から `p ∣ Nat.card F` |

現在の DkMath の局所成分補題は、Néron 成分群そのものではなく、
`zeroComponentSubgroup` による抽象商を対象にしている。

## 3. 証明ギャップ

### A. `2p` 有理点から `MazurStepThree` へ

`residual_cofixed_implies_rational_two_p_torsion` の点は強い入力だが、
`MazurStepThree` が受け取るのは代数閉包上の位数 `p` の Galois 固定点である。

必要な接続は少なくとも次の三つに分かれる。

1. 位数 `2p` の点から非零位数 `p` の点 `2Q` を取り出す。
2. 整数モデル上の点を代数閉包上の点へ正しく輸送する。
3. `2Q` が Galois 固定であることを示す。

1 と 2 の群論・モデル同一性 API は DkMath に存在する。3 は、有理点からの
base-change と `Affine.Point.map` の接続を個別に証明する必要がある。

### B. 零成分外性の全素数化

DkMath には 2進の零成分外性と、`q < p` の bad-prime 支持がある。しかし
`MazurStepThree` は判別式を割る全ての `q ≠ 2,3,p` に対して、代数閉包上の
任意の valuation subring で零成分外性を要求する。

これは単なる `localValuationSubring 2` の有限剰余体計算ではなく、
`InZeroComponentAt` と `CriticalCentre` を代数閉包側へ輸送する問題である。
有限体上の点群と代数閉包剰余体上の点群を同一視してはならない。

### C. `MazurStepThree` 本体

外部証明の `Theorems/Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean`
は、モジュラー曲線の Eisenstein 商、局所 Tate 展開、Néron 成分群の計数を消費する。
DkMath の既存 `DkMath.Lib` には、この一般 `WeierstrassCurve` 用の同一定理はない。

したがって、`MazurStepThree` を無条件に DkMath の補題として宣言することはできない。
それは未証明の大域数学を仮定する独自 `axiom` と同値になり、今回の品質条件に反する。

## 4. 経路比較

### 経路 A: 一般 Néron 成分群を先に構築

- 必要物: Néron モデル、特殊ファイバー成分群、Tamagawa 数、零成分写像。
- 現状: DkMath には局所 valuation と抽象 `zeroComponentSubgroup` まで。
- 評価: 数学的には正しいが、`hno` の短期経路では過大。分裂乗法的還元枝を
  単独では排除できない。

### 経路 B: `MazurStepThree` の DkMath 接続

- 必要物: 模範解答の大域定理をそのまま仮定せず、DkMath の Frey モデル、
  Galois 固定点、局所零成分条件を同じ仕様へ合わせる。
- 評価: 一般 `hno` に最も近いが、モジュラー曲線・Eisenstein 商の大規模移植が
  必要になる可能性が高い。
- 現実的な最小単位: まず `MazurStepThree` の入力を DkMath 型で表現した
  条件付きインターフェースを作り、各入力を既存定理から供給できるか監査する。
  条件付きインターフェース自体を `hno` 完成とは扱わない。

### 経路 C: `2p` 有理捩れから直接排除

- 必要物: `p ≥ 17` の一般楕円曲線に対する有理 torsion 分類、または Frey 曲線に
  特化した位数制約。
- 現状: DkMath に一般 Mazur torsion 分類はない。
- 評価: 外部証明の実際の経路ではない。新しい大域定理を別途必要とするため、
  `MazurStepThree` より短いとは判断できない。

## 5. 推奨する次の実装単位

まず、未証明の大域定理を仮定しない教材インターフェースを追加する。

```text
MazurStepThreeInput (W, Q, p)
  := prime/order/Galois-fixed/local-zero-component obligations
```

次に、DkMath 側で以下を実装可能な順に閉じる。

1. `Q` の base-change と `Affine.Point.map` の Galois 固定性。
2. `addOrderOf Q = 2*p` から `addOrderOf (2 • Q) = p` を得る群論補題。
3. 2進および `q < p` bad-prime の局所入力を、`MazurStepThreeInput` の形へ整理。
4. `MazurStepThree` の大域本体は、実装済み定理が存在するまで未解決として残す。

この順序なら、DkMath の既存成果を再利用しながら、外部証明の巨大な依存を
誤って「完了」と扱わずに済む。

## 6. 現時点の結論

現在の証明グラフは、次の位置にある。

```text
Cofixed stable line
  → rational point of exact order 2*p                         [DkMath 完了]
  → exact order p class in abstract dyadic quotient            [DkMath 完了]
  → finite component cardinality divisibility                   [abstract lemma 完了]
  → MazurStepThree local/global zero-component exclusion        [未接続]
  → irreducibility and general hno                               [未完成]
```

従って、次に実装すべき最小の新数学は `2*p` 点から `p` 点を作る群論・
base-change 教材補題であり、一般 Néron 理論の拡張ではない。

このうち群論部分は `DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient` の
`addOrderOf_two_nsmul_eq_prime_of_addOrder_eq_two_mul_prime` として先に固定した。
残る base-change の Galois 固定性と、各局所条件の `MazurStepThreeInput` への
輸送は未実装である。

base-change の初歩的な境界も
`DkMath/Lib/NumberTheory/EllipticBaseChangeTorsion.lean` に固定した。

- `baseChangePoint_nsmul` は係数体拡大後の点が自然数倍を保存する。
- `addOrderOf_baseChangePoint_eq` は係数埋め込みの単射性から加法位数を保存する。

これらは Galois 固定性から有理点を降下させる理論ではない。固定点からの降下は
既存の `exists_baseChangePoint_of_fixed`／`exists_rational_torsion_of_fixed` が供給し、
今回の二補題はその逆向き、すなわち有理点を幾何学的点へ持ち上げる側の型境界である。

