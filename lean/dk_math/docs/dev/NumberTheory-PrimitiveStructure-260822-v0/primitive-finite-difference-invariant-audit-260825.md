# Primitive finite-difference invariant audit

日付: 2026-08-25
対象: `instruction-035.md`
対象範囲: `DkMath.CosmicFormula`、`DkMath.Analysis.TaylorBridge`、
`DkMath.NumberTheory.Legendre`、`DkMath.Primitive.SquareBody`

## 0. 結論

本 checkpoint では、ルジャンドル予想の形式化に有限差分・導関数極限を導入する
実装上の必要性と、既存 API から得られる数論的帰結を調査した。

結論は **Outcome B — ALGEBRAIC / GEOMETRIC REFINEMENT** とする。

有限差分には、二次式について次の明快な有限パラメータ表示がある。

```text
Δᵤ(x²) = u (2x + u),
(x+u)² - x(x+2u) = u²,
Δₕ²(x²) = 2h².
```

特に `Big - Body = Gap` は固定した `u` に関して `x` に依存しない保存座標であり、
二階差分は二次式の幾何的特徴を正確に表す。しかし、これらは既存の二項展開・
平方差分の言い換えであり、素数被覆、波の carry、support escape、small cofactor
に対する新しい制約を与えない。したがって、有限差分は現在のルジャンドル予想の
証明ルートを前進させる独立な数論的不変量ではない。

`u → 0` の導関数 API は線形係数 `2x` だけを取り出し、有限 `u` にある余り `u`
および `u²` を消去する。この極限から有限剰余・素数被覆の情報を逆算することも
できない。

## 1. 調査した既存 API

### 1.1 有限差分と差分商

`DkMath.CosmicFormula.CosmicDifferenceKernel` には、実数値関数について

```lean
delta f x u := f (x + u) - f x
cosmicKernel f x u := delta f x u / u
```

が定義され、`delta_add`、`delta_sub`、`delta_smul`、`delta_mul`、
`delta_finset_sum` および対応する kernel の加法・乗法・有限和 API がある。

`DkMath.CosmicFormula.CosmicDerivativePower` には、一般の自然数次数 `d` について

```lean
sub_pow_eq_u_mul_powerKernel
cosmicKernel_pow_eq_powerKernel_of_ne_zero
```

があり、

```text
(x+u)^d - x^d = u * powerKernel d x u
cosmicKernel (fun y => y^d) x u = powerKernel d x u  (u ≠ 0)
```

を与える。`DkMath.CosmicFormula.CosmicFormulaDerivativeBridge` には、二次の場合の
`delta_pow_two_eq_u_mul_powerKernel_two` と、`cosmic_formula_unit` の `u` 倍・
`u²` 表示がある。

従って、Q1 の抽象的な有限差分分解は既存 API で完全に供給されている。
`powerKernel 2 x u` を展開して `2*x+u` と書く専用の公開定理は見当たらないが、
これは `powerKernel` の定義展開と環の計算だけで得られる薄い specialization であり、
今回新規に追加すべき数論 API ではない。

### 1.2 Big / Body / Gap

`DkMath.CosmicFormula.CosmicFormulaBasic` の実数版には

```text
cosmic_formula_unit x u = (x+u)² - x(x+2u) = u²
```

および `cosmic_formula_unit_theorem` がある。一般の可換環版は
`DkMath.CosmicFormula.CosmicFormulaBinom` の
`Big`、`Body`、`Gap`、`big_is_body_and_gap`、`cosmic_id`、`cosmic_formula_binom`
で供給される。自然数を含む半環版にも `BigN`、`BodyN`、`GapN` と対応する恒等式・
大小関係がある。

次数二では

```text
Big  2 x u = (x+u)²
Body 2 x u = x(x+2u)
Gap  2 u   = u²
Big - Body = Gap.
```

よって `Big - Body` は固定 `u` で `x` に依存しない。ただしこれは新しい
保存則というより `Gap` の定義を含む既存の完全な代数恒等式である。

## 2. Q1: `delta` / `cosmicKernel` と二次式

### 既存定理の対応

| 求める内容 | 既存 API | 判定 |
|---|---|---|
| `Δᵤ(x²) = u * powerKernel 2 x u` | `delta_pow_two_eq_u_mul_powerKernel_two` | 直接利用可 |
| `(x+u)^d - x^d = u * powerKernel d x u` | `sub_pow_eq_u_mul_powerKernel` | 直接利用可 |
| `Δᵤ(x²) / u = powerKernel 2 x u` (`u ≠ 0`) | `cosmicKernel_pow_eq_powerKernel_of_ne_zero` | 直接利用可 |
| `Δᵤ(x²) = u(2x+u)` | 上記と `powerKernel` の展開 | 薄い specialization のみ |
| `cosmicKernel (square) x u = 2x+u` (`u ≠ 0`) | 上記と `powerKernel` の展開 | 薄い specialization のみ |

有限 `u` では `2x+u` の `+u` が消えない。これは導関数の `2x` と異なる重要な
形式上の差であるが、素数や剰余を含まない実数の多項式恒等式に留まる。

### Q1 の判定

有限差分 chain は **既存 API で閉じている**。専用の `squareDelta` や
`squareCosmicKernel` の抽象を増設しても、現在の Legendre 層に新しい入力を与えない。
従って実装は行わず、上記の API 対応を資料として残す。

## 3. Q2: Big / Body / Gap の有限差分

固定 `u` で `x` を差分化すると、二次の場合は形式的に

```text
Δₕ Big(x,u)  = 2h(x+u) + h²
Δₕ Body(x,u) = 2h(x+u) + h²
Δₕ Gap(u)    = 0.
```

従って `Big - Body = Gap` の差分は常に 0 であり、`Big` と `Body` の x 方向の
有限差分は一致する。二階差分は

```text
Δₕ² Big  = 2h²,
Δₕ² Body = 2h²,
Δₕ² Gap  = 0,
Δₕ²(Big - Body) = 0.
```

特に単位刻み `h=1` なら二階差分は 2 になる。

一方、固定 `x` で `u` を差分化すると

```text
Δₕ Big  = 2h(x+u) + h²,
Δₕ Body = 2xh,
Δₕ Gap  = 2uh + h²,
```

であり、`Δₕ(Big-Body) = Δₕ Gap` に過ぎない。したがって `u` 方向に新しい
u-independent conservation law は発生しない。

### Q2 の判定

`Big - Body = Gap`、x 方向の差分一致、二階差分一定性は、明快な幾何的再表現である。
しかし、`Gap = u²` は素数被覆や波の占有数に接続されていない。よってこれは
Outcome B の「代数的・幾何的 refinement」として記録するが、Legendre の証明に
使える新しい不変量とは判定しない。

## 4. Q3: 導関数極限との関係

`DkMath.CosmicFormula.CosmicDerivativeBasic` の
`hasDerivAt_iff_tendsto_cosmicKernel` は、

```text
HasDerivAt f L x
  ↔ Tendsto (fun u => cosmicKernel f x u)
      (nhdsWithin 0 ({0})ᶜ) (nhds L).
```

という punctured limit の同値を与える。`CosmicDerivativePower` の
`powerKernel_zero`、`tendsto_powerKernel_zero`、`hasDerivAt_pow_cosmic` により、
二次式については

```text
powerKernel 2 x u = 2x + u,
lim[u→0] powerKernel 2 x u = 2x.
```

となる。有限 `u` の `+u` および `Big-Body` に現れる `u²` は、この極限で消える。

`DkMath.Analysis.TaylorBridge` の `powerDifferenceQuotient`、
`real_gapGN_eq_powerKernel`、`tendsto_powerDifferenceQuotient_zero` も同じ構造を
一般次数で確認している。すなわち、有限差分商と導関数は同じ polynomial kernel を
共有するが、導関数はその `u=0` の値だけを読む。

### Q3 の判定

導関数 API は有限差分 identity の極限として整合的だが、有限 `u` の情報を強化しない。
特に、極限値 `2x` から `+u`、`u²`、または有限剰余情報を復元することはできない。

## 5. Q4: `u=1` と既存の unit-one / square-offset 層

`DkMath.CosmicFormula.CosmicFormulaBasic` の
`cosmic_formula_one_theorem` および `cosmic_formula_unit_theorem x 1` は

```text
(x+1)² - x(x+2) = 1
```

を既に与える。自然数側では

```text
(n+1)² - n² = 2n+1,
```

が `DkMath.NumberTheory.Legendre.Basic` の `SquareOffset`、
`squareOffsets`、`squareCell_iff_exists_squareOffset` と対応する。
`SquareOffset n r` は

```text
1 ≤ r ∧ r ≤ 2*n
```

であり、これは隣接平方の shell に現れる全有限 offset をすでに正確に表現している。

さらに `Legendre.Wave` は `squareWaveOffsets`、波の占有数、`squareWaveCarry`、
carry の 0/1 判定、anchor が modulus で割り切れる場合の count formula を提供する。
従って、`u=1` の有限差分を Legendre の既存データへ落とす場合、得られる内容は
既存の `2n+1` と `1 ≤ r ≤ 2n` の再記述である。

### Q4 の判定

unit-one の有限算術は既存の square-offset / wave API に取り込まれている。
有限差分層から新たな自然数・剰余・被覆条件は得られない。

## 6. Finite-u / derivative-limit / unit-one の情報分離

| 観点 | 保持する情報 | 失う情報 | Legendre 層への既存接続 |
|---|---|---|---|
| 有限 `u` | `Δᵤ(x²)=u(2x+u)`、`Big-Body=u²`、`Δₕ²(x²)=2h²` | 素数・剰余はそもそも含まない | 直接の bridge なし |
| `u→0` | 線形係数 `2x`、`HasDerivAt` | `+u`、`u²`、有限 shell の幅 | 導関数 API のみ。離散波への bridge なし |
| `u=1` | `2n+1`、`1≤r≤2n`、隣接平方 shell | 一般 `u` の連続パラメータ | `SquareOffset`、`squareWaveOffsets`、carry に既存接続 |

この三つを同一視すると、有限 shell の情報と極限の接線情報を混同する。現在の
Legendre 形式化で使われているのは最後の unit-one / Nat-divisibility 側であり、
最初の二つからそれを強化する定理は確認できなかった。

## 7. Q5: prime-wave / support / coverage への接続

### 7.1 既存の数論 API

`DkMath.NumberTheory.Legendre.Basic` には、平方 shell の offset と prime support に
ついて次の API がある。

- `SquareOffset n r` と `squareOffsets n`
- `SquareOffsetForbiddenBy n q r`
- `squareOffsetCovered_iff_exists_prime_dvd`
- `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue`
- `squareOffsetPrimeSupport` および support membership
- `SquareOffsetOverlap`、square cell、pair support/product phase

`DkMath.NumberTheory.Legendre.Wave` には、modulus ごとの wave occupancy と carry があり、

```text
card (squareWaveOffsets n m)
  = (2*n)/m + squareWaveCarry n m
```

を `squareWaveCarry_eq_div_add_carry` が与える。carry は 0/1 であり、anchor の
divisibility による carry zero と count formula も既に形式化されている。

`Frontier` には、

```text
legendreConjecture_iff_squareAnchoredSupportEscape
legendreConjecture_iff_squareOffsets_not_fully_covered
```

という、support escape・全被覆否定・ルジャンドル予想の正確な同値がある。

### 7.2 有限差分から得られる bridge の有無

有限差分側の主役は `ℝ` 上の多項式と `CommRing` 上の `Big/Body/Gap` である。
一方、prime-wave / support / coverage 側の主役は `ℕ` の divisibility、素数、有限集合、
剰余である。現在の公開 API には、次のいずれかを結ぶ定理はない。

```text
delta / cosmicKernel
  → squareWaveOffsets / squareWaveCarry
  → prime support / forbidden residue
  → coverage escape.
```

また、`Big-Body=Gap` や `Δₕ²(x²)=2h²` を wave count、support imbalance、coverage
ledger に変換する定理もない。有限 `u` を自然数に制限しても、これは単なる整数多項式
恒等式であり、素数除法の存在や非存在を導かない。

### Q5 の判定

**新しい prime-wave / support / coverage constraint は発見されなかった。**
既存の wave と coverage は unit-one の square-offset データを直接扱っており、有限差分
層を経由する利点は現時点で確認できない。

## 8. Q6: 二階差分と packet / determinant / small-cofactor

二階差分の定数性は、平方列の曲率が一定であるという幾何的事実である。一般刻みでは
`Δₕ²(x²)=2h²`、単位刻みでは 2 となる。しかし、現在の packet / determinant / small-
cofactor API にこの値を入力する consumer は確認できない。

`DkMath.NumberTheory.Legendre` の packet 関係、たとえば左右 endpoint の差が `n` になる
関係は、square-offset の配置と有限 packet の定義から得られる別個の恒等式である。
二階差分 2 を packet determinant、wave carry、または prime support の imbalance と
結ぶ定理はない。

`SmallCofactor` および `Primitive/SquareBody` の C001/C002/L022 系 API は、平方点の
上界、fresh/old split、selected support、small cofactor の素数性・非自明性を扱う。
これらの仮定に二階差分の定数性を加えても、既存の small-cofactor 結論を強化する
形式的な入力は得られない。

### Q6 の判定

二階差分は clean な幾何的 refinement だが、packet、determinant、small-cofactor への
新しい接続はない。代数的な説明を超えて route を延長する根拠はない。

## 9. Q7: shell 間 transport と descent

`SmallCofactor` の C001/C002 は、固定 anchor に対する square point の upper bound と
fresh/old split を使う。異なる shell parameter `P` に対して同じ point を表示できる場合
でも、現在の API には次の transport がない。

```text
P での fresh / selected-support / cofactor 情報
  → P' での同じ情報
  → cofactor の厳密な減少
  → descent termination.
```

特に `k ≤ P` のような単なる大小関係は、small cofactor の値が次の段階で厳密に小さく
なることを意味しない。`squareBody_large_prime_small_cofactor_split` も固定した平方
body の normal form を分解する API であり、shell を跨ぐ再帰的 provider ではない。

有限差分の `x` 方向不変性は `Big-Body=u²` の再確認に留まり、freshness、support quotient、
selected prime の transport を供給しない。

### Q7 の判定

有限差分から shell 間の descent は得られない。小因子が形式的に減少するという推論は
未証明であり、現行の C001/C002/L022 の境界を越えてはならない。

## 10. Q8: 全被覆仮定からの新制約

現在の Legendre frontier で利用できる全被覆仮定は、既に

```text
SquareOffsetsFullyCovered n
  ↔ coveredSquareOffsets n = squareOffsets n
```

および support escape・ルジャンドル予想との同値に整理されている。
調査した有限差分 API からは、

```text
SquareOffsetsFullyCovered n → NEW_CONSTRAINT n
```

の形の新しい constraint は得られなかった。特に次は未成立である。

- 全被覆から一定二階差分の矛盾を導くこと。
- carry の総和または wave occupancy の不足を導くこと。
- `Big-Body=u²` から prime support の escape を導くこと。
- small cofactor の非自明性から shell 全被覆の否定を導くこと。

### Q8 の判定

Outcome B の範囲で、有限差分は「保存座標と二階差分を明示する代数・幾何的 refinement」
として閉じている。一方、全被覆に対する新しい数論的制約はなく、Legendre の frontier
を縮めない。

## 11. 証明に使えない推論の明示

次の推論は、今回の既存 API からは導けない。

1. 有限 `u > 0` の差分表示から prime escape が出る。
2. 二階差分が一定であることから、各 shell に素数が存在する。
3. 導関数の保存的表示から residue conservation が得られる。
4. `u → 0` の極限が有限 shell の離散情報を強化する。
5. 実数の連続不変量が finite prime-wave imbalance を意味する。
6. 有限差分恒等式が `SquareOffsetsFullyCovered` の矛盾を直接与える。
7. small-cofactor の return を、shell 間の recursive descent とみなす。
8. `ℝ` の導関数等式を、明示的な bridge なしに `ℕ` の divisibility 等式へ移す。

これらのいずれにも、現在の source には必要な independent bridge、positivity、
modular counting、または descent measure がない。

## 12. 推奨と停止境界

今回の checkpoint で実装を追加する必要性は認められない。特に次の変更は見送る。

- `CosmicDifference` や square-specific kernel の新しい抽象の増設。
- 導関数用 namespace を Legendre namespace に混在させること。
- Legendre の自然数・剰余層に実数または複素数の依存を追加すること。
- `ZMod`、解析的極限、素数評価、RH 相当の provider を仮定すること。
- 既存の `SquareOffset`、wave、support、coverage、small-cofactor API の重複定義。

したがって本成果物は **report-only** とし、Lean source、import、依存関係、toolchain、
既存の CosmicFormula frontier、Lean docstring は変更しない。将来、有限差分を再開する
場合は、まず `delta` または `powerKernel` の出力を prime-wave / support API に接続する
独立した定理文を先に提示し、その定理に具体的な数論的 conclusion があることを確認すべき
である。その bridge がない限り、この route は本レポートで停止する。

## 13. 確認した主な宣言

```text
DkMath.CosmicFormula.delta
DkMath.CosmicFormula.cosmicKernel
DkMath.CosmicFormula.delta_pow_two_eq_u_mul_powerKernel_two
DkMath.CosmicFormula.sub_pow_eq_u_mul_powerKernel
DkMath.CosmicFormula.cosmicKernel_pow_eq_powerKernel_of_ne_zero
DkMath.CosmicFormula.cosmic_formula_unit_theorem
DkMath.CosmicFormulaBinom.big_is_body_and_gap
DkMath.CosmicFormulaBinom.cosmic_id
DkMath.CosmicFormulaBinom.cosmic_formula_binom
DkMath.CosmicFormula.hasDerivAt_iff_tendsto_cosmicKernel
DkMath.CosmicFormula.powerKernel_zero
DkMath.Analysis.TaylorBridge.real_gapGN_eq_powerKernel
DkMath.NumberTheory.Legendre.squareOffsetCovered_iff_exists_prime_dvd
DkMath.NumberTheory.Legendre.squareWaveCarry_eq_div_add_carry
DkMath.NumberTheory.Legendre.legendreConjecture_iff_squareOffsets_not_fully_covered
```

この一覧は実装要求ではなく、checkpoint の再現性のための参照一覧である。
