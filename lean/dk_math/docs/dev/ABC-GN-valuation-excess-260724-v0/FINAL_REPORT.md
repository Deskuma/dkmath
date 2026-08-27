# ABC–GN Valuation Excess Route — Final Report

作成日: 2026-07-24  
Repository: `Deskuma/dkmath`  
Workbench PR: `#67 WIP: ABC–GN valuation excess route`  
Implementation checkpoint commit: `5f0b9f80cd6afc20692eb6f4670ea65c8872d5a2`

## 1. 最終結論

本 workbench では、DkMath に既存の一般 `GN`、`padicValNat`、factorization、`rad`、primitive-prime bridge を ABC triple 上で再接続し、次の決定論的 spine を Lean theorem として完成させた。

```text
ABC triple
  -> GN power lift
  -> boundary / GN p-adic split
  -> exponent-exceptional / non-exceptional split
  -> exact radical-support / valuation-multiplicity identity
  -> unconditional GN return
  -> exceptional support absorption
  -> fresh non-exceptional support return
  -> support budget + valuation budget
  -> explicit K_epsilon ABC bound
```

最終的に、正の ABC triple 全体について、三つの一様 budget を与えれば、一つの明示定数 `K >= 1` による ABC 不等式が従うことを Lean が認可した。

ただし、本 workbench は ABC 予想そのものを証明していない。未解決部分は、曖昧な一個の仮定ではなく、次の三予算へ正確に分離された。

```text
1. uniform lifted-radical support growth
2. uniform exceptional valuation excess
3. uniform non-exceptional valuation excess
```

この三予算、または三者を同時に制御するより強い balance theorem が、今後の本丸である。

## 2. 信頼境界と検証状態

最終 implementation checkpoint について、次を確認済みである。

```text
lake build DkMath.ABC.GNFinalBudgetBridge
Build completed successfully (8343 jobs)
```

GitHub Lean CI:

```text
Lean CI run 271
status: completed
conclusion: success
```

追加された主要 theorem の axiom audit は、次の標準依存のみを報告した。

```text
propext
Classical.choice
Quot.sound
```

本 workbench では次を追加していない。

```text
new axiom
sorry
native_decide proof
abc_main_axiom dependency
```

また、共有 aggregator、`DkMath/FLT/Seven/**`、FLT7 専用 documentation は変更していない。

## 3. 実装 module

### 3.1. `DkMath.ABC.GNPowerLift`

ABC triple `T` と指数 `n` から、概念的に次の lifted triple を構成する。

```text
lift.a = T.a * GN n T.a T.b
lift.b = T.b ^ n
lift.c = T.c ^ n
```

中心恒等式は、`T.a + T.b = T.c` から得られる。

$$T.a\,GN_n(T.a,T.b)+T.b^n=T.c^n$$

この lifted object が、その後の coprime、support、valuation、radical の共通 carrier となる。

### 3.2. `DkMath.ABC.GNValuationSplit`

素数 `q` ごとに、power difference の valuation を boundary と GN に分解する。

$$v_q(T.c^n-T.b^n)=v_q(T.a)+v_q(GN_n(T.a,T.b))$$

primitive / clean channel では boundary valuation が消え、power difference の valuation が GN valuation へ一致する。

### 3.3. `DkMath.ABC.GNExceptionalSplit`

GN と boundary の共通 divisor は指数 `n` に閉じ込められる。

```text
q | boundary
q | GN
  -> q | n
```

したがって `q ∤ n` の non-exceptional channel では、GN support prime は boundary `T.a` を割らない。

### 3.4. `DkMath.ABC.GNValuationExcess`

自然数 `m` に対し、valuation multiplicity の squarefree support 超過量を定義した。

$$\operatorname{valuationExcess}(m)=\sum_{q\mid m}(v_q(m)-1)\log q$$

exact identity:

$$\log m=\log\operatorname{rad}(m)+\operatorname{valuationExcess}(m)$$

GN specialization:

$$\log GN=\log\operatorname{rad}(GN)+GNValuationExcess$$

さらに指数による exceptional / non-exceptional partition も exact に証明した。

$$GNValuationExcess=GNExceptionalValuationExcess+GNNonExceptionalValuationExcess$$

### 3.5. `DkMath.ABC.GNHighLift`

high-lift prime を、概念的に次で固定した。

```text
q prime
q^2 | GN n a b
```

valuation excess の carrier は valuation が 2 以上の prime だけであり、exact finite sum として high-lift support へ制限された。

```text
no high-lift prime
  -> GNValuationExcess = 0
```

この module は high-lift の不存在や希少性を主張しない。carrier の所在を有限 API として固定する層である。

### 3.6. `DkMath.ABC.GNQualityExcessBridge`

GN return の自然数下界を無条件に証明した。

```lean
Triple.pow_pred_c_le_GN
```

$$T.c^{n-1}\le GN_n(T.a,T.b)$$

対数化:

```lean
Triple.log_c_mul_pred_le_log_GN
```

$$(n-1)\log T.c\le\log GN_n(T.a,T.b)$$

この return bound と exact log identity により、高い ABC quality と GN support budget から valuation excess の下界を得る。

Affine 版の概念形:

$$\left((n-1)(1+\varepsilon)-\sigma\right)\log\operatorname{rad}(abc)-C<GNValuationExcess$$

### 3.7. `DkMath.ABC.GNSupportReturn`

GN prime support を指数で exact に分割した。

```lean
GN_support_eq_exceptional_union_nonExceptional
GNExceptionalSupport_disjoint_nonExceptional
rad_GN_eq_exceptional_mul_nonExceptional
```

$$\operatorname{rad}(GN)=E_nN_n$$

ここで、`E_n` は `q | n` の exceptional support product、`N_n` は `q ∤ n` の non-exceptional support product である。

Exceptional support は指数 radical へ有限吸収される。

```lean
GNExceptionalSupportProduct_dvd_rad
```

$$E_n\mid\operatorname{rad}(n)$$

Non-exceptional support は元の ABC coordinates 全てから fresh である。

```lean
Triple.nonExceptionalSupport_fresh
```

$$q\mid N_n\Longrightarrow q\nmid T.aT.bT.c$$

元 radical と fresh support の積は lifted triple radical を割る。

```lean
Triple.rad_mul_nonExceptionalProduct_dvd_lift_rad
```

$$\operatorname{rad}(T.aT.bT.c)\,N_n\mid\operatorname{rad}(\operatorname{lift}.a\operatorname{lift}.b\operatorname{lift}.c)$$

その結果、lifted-radical growth budget から full GN support budget への deterministic transport を得た。

```lean
Triple.GNSupportBudgetAffine_of_liftGrowth
```

Exceptional support の有限費用は、結論上に明示的な `log(rad n)` として残る。

### 3.8. `DkMath.ABC.GNFinalBudgetBridge`

Prime-support budget と valuation-multiplicity budget を最終的に合成した。

追加 predicate:

```lean
GNValuationExcessBudgetAffine
GNExceptionalExcessBudgetAffine
GNNonExceptionalExcessBudgetAffine
```

Exceptional / non-exceptional excess budget の合成:

```lean
GNValuationExcessBudgetAffine.of_split
```

Support と multiplicity の直接合成:

```lean
Triple.log_c_mul_pred_le_of_support_and_excessBudget
```

$$ (n-1)\log c\le(\sigma+\tau)\log R+(C_s+C_e) $$

ここで、`R = rad(a*b*c)` である。

Lifted-radical specialization:

```lean
Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
```

$$ (n-1)\log c\le(\sigma+\tau)\log R+C_s+C_e+\log\operatorname{rad}(n) $$

実装された明示定数:

```lean
GNABCConstant n Cs Ce =
  max 1 (Real.exp |Cs + Ce + Real.log (rad n : ℝ)|)
```

Pointwise ABC theorem:

```lean
Triple.abc_bound_of_liftGrowth_and_excessBudget
```

Margin 条件

$$\sigma+\tau\le(n-1)(1+\varepsilon)$$

の下で、

$$c\le GNABCConstant(n,C_s,C_e)\,\operatorname{rad}(abc)^{1+\varepsilon}$$

を証明した。

最後に、一様 budget を structure として束ねた。

```lean
ABCGNFinalBudgetContract
abc_positive_of_GNFinalBudgetContract
```

この contract から、正の ABC triple 全体に共通する一つの `K >= 1` を得る。

## 4. 完成した checkpoint

```text
ABC-GN-001  GN power lift                                      完了
ABC-GN-002  coprime / support separation                       完了
ABC-GN-003  p-adic boundary–GN split                           完了
ABC-GN-004  q | n / q ∤ n exceptional split                    完了
ABC-GN-005  exact log(rad) + valuation-excess identity         完了
ABC-GN-006  unconditional GN return and quality bridge         完了
ABC-GN-007  finite high-lift carrier API                       完了
ABC-GN-008  exceptional support absorption / fresh return      完了
ABC-GN-009  two-budget composition / explicit K_epsilon        完了
ABC-GN-010  uniform budget proofs / axiom replacement          未着手・研究停止
```

## 5. Lean-confirmed final chain

`T : Triple`、`n >= 2`、`T.a > 0`、`T.b > 0` とする。

### 5.1. Return

$$ (n-1)\log T.c\le\log GN_n(T.a,T.b) $$

### 5.2. Exact support / multiplicity identity

$$ \log GN_n=\log\operatorname{rad}(GN_n)+GNValuationExcess_n $$

### 5.3. Support partition

$$ \operatorname{rad}(GN_n)=E_nN_n $$

$$ E_n\mid\operatorname{rad}(n) $$

### 5.4. Fresh support return

$$ \operatorname{rad}(abc)N_n\mid\operatorname{rad}(\text{lifted }abc) $$

### 5.5. Two-budget height bound

Lifted-radical growth budget:

$$\log\operatorname{rad}(\text{lifted }abc)\le(1+\sigma)\log R+C_s$$

Valuation-excess budget:

$$GNValuationExcess\le\tau\log R+C_e$$

ならば、

$$ (n-1)\log c\le(\sigma+\tau)\log R+C_s+C_e+\log\operatorname{rad}(n) $$

となる。

さらに、

$$\sigma+\tau\le(n-1)(1+\varepsilon)$$

ならば、明示的な `K` により、

$$c\le K R^{1+\varepsilon}$$

を得る。

## 6. 残る三つの魔核

### 6.1. Uniform lifted-radical support growth

必要な型は概ね次である。

$$\log\operatorname{rad}(\text{lifted }abc)\le(1+\sigma)\log\operatorname{rad}(abc)+C_s$$

これは GN の値そのものではなく、power lift によって発生する相異なる fresh prime support の総対数質量を抑える問題である。

既存の primitive-prime / Zsigmondy 理論は、新しい prime の存在を示す方向に強い。一方、この budget は新しい prime support の総量の上界を要求するため、同じ theorem をそのまま適用するだけでは閉じない。

### 6.2. Uniform exceptional valuation excess

Exceptional prime は `q | n` に限定されるため support は有限である。しかし有限 support から valuation depth の一様上界は自動では従わない。

必要なのは、概ね次である。

$$GNExceptionalValuationExcess\le\tau_e\log R+D_e$$

固定指数では、LTE、`padicValNat`、二項係数 valuation、boundary coprimality により、`tau_e = 0` と指数依存定数だけへ落とせる可能性がある。

三魔核の中では最初に攻める価値が高い。

### 6.3. Uniform non-exceptional valuation excess

Non-exceptional high-lift は、

$$q\nmid n,\qquad q^2\mid GN_n(a,b)$$

という深い局所一致である。

適切な単元比で見れば、これは `X^n = 1 mod q^2` 型の Hensel lift、p-adic logarithm、Wieferich 型現象へ接続する。

必要なのは個々の high-lift の説明だけではなく、

$$\sum_{q\nmid n}(v_q(GN)-1)\log q$$

全体の一様上界である。

現時点では最深部候補である。

## 7. 統合攻撃の可能性

最終 contract が必要とするのは、三係数を個別に最良化することではない。

$$\sigma+\tau_e+\tau_n\le(n-1)(1+\varepsilon)$$

が成立すればよい。

したがって、次のような support–multiplicity balance theorem が得られれば、三魔核を個別に倒さず一度に貫通できる可能性がある。

```text
fresh support が大きい
  -> repeated valuation multiplicity は小さい

valuation multiplicity が深い
  -> support carrier は強く制限される
```

DkMath 的には、これは

```text
花弁の種類を増やす世界
と
同じ花弁を深く重ねる世界
は同時に最大化できない
```

という天秤保存則に相当する。

## 8. 現時点で主張しないこと

本 workbench の成果から、次は主張しない。

```text
ABC conjecture is proved
abc_main_axiom is removed
uniform budgets exist
all non-exceptional high lifts are excluded
GN is generally squarefree
probabilistic / density routes are unnecessary
```

また、最終 global theorem は `T.a > 0`、`T.b > 0` の positive triple を対象とする。`a = 0` または `b = 0` の coprime endpoint を `abc_main_axiom` と同一 surface へ接続する薄い wrapper は未実装である。

## 9. 再開時の推奨順序

### Phase A: exceptional multiplicity

```text
q | n
LTE / padicValNat / boundary coprimality
  -> fixed-exponent exceptional excess budget
```

ここで `tau_e = 0`、`D_e = D(n)` 型を第一候補とする。

### Phase B: support growth reconnaissance

```text
non-exceptional fresh support
primitive / cyclotomic / Petal channels
  -> lifted radical support geometry
```

最初から強い一様定理を置かず、fixed `n`、prime `n`、squarefree exponent、特定 family など、成立する最小 domain を探索する。

### Phase C: non-exceptional high-lift depth

```text
q ∤ n
q^2 | GN
  -> unique Hensel lift
  -> p-adic logarithmic depth
  -> total valuation-mass budget
```

個別 prime の局所定理と、全 carrier の総和評価を分離する。

### Phase D: balance theorem

A–C を別々に最良化するより、support と multiplicity の同時制御が見える場合は、最終 contract の margin へ直接接続する。

## 10. Closure

本 workbench は、ABC 予想を解いた project ではない。

しかし、ABC の GN route において、次は完了した。

```text
曖昧な radical obstruction
  -> exact support budget

曖昧な repeated-prime obstruction
  -> exact valuation-excess budget

二予算
  -> explicit K_epsilon

一様仮定
  -> global positive-triple ABC theorem
```

したがって、現在の未解決 Big は、Lean の外に隠れていない。

```text
uniform support growth
uniform exceptional multiplicity
uniform non-exceptional multiplicity
```

という三つの明示的な Gap として theorem contract 上に露出している。

ここで本 workbench を一旦停止し、魔王討伐に必要な数論装備を準備する。

再開するときは、`FINAL_REPORT.md`、`report-007.md`、`GNFinalBudgetBridge.lean` を最初に読むこと。
