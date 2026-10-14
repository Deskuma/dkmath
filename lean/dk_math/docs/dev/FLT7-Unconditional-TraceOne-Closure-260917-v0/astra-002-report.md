# Astra-002 — 現行 FLT7 provenance からの打開策調査

## 調査ログ

このレポートは `astra-002.md` の研究依頼に対応する。R46 の結論を再利用する
だけでなく、六次 cyclotomic carrier・14乗・ノルム変分・校正値排除の入力を
現行ソースから照合する。調査と検証を段階的に保存する。

- 開始時のブランチは `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`、
  toolchain は Lean v4.34.0。R46 の scratch とレポートは現行ソースに存在する。
- 文書の指定どおり、Lean 実装の前に歴史層と現行層の仮定を調査した。
- 歴史層の conjugate-prime / valuation ownership / loaded residual 定理は
  `RamifiedSignedRootRoutingPacket` とその `QuotientPrimeSupport` に依存する。
  これらの `quotientRoot` は現行 `C=gcd(R,S)` と定義上同じではない。
  `CyclotomicLinearPrimeAddress` は既に residue field への向き付き評価を含み、
  任意の実三次 split prime にそのまま適用できる定理ではない。
- 商側の素点で **元の** `p.rho` と `rotateEquiv p.rho` の比を取る候補を発見。
  `seventhQuotient = 0`、互いに素、`q != 7` から非自明な 7 次根を得れば
  `q % 7 = 1` に強化できる。抽出後の gap root を再始動する議論ではない。
  この段階では Lean 未検証。
- `astra-002-exact-probe.py` を保存し、SymPy による厳密剰余環計算を実行した。
  `alpha^3 = 2*alpha^2 + alpha - 1` と `rho0 = -alpha^3` に対して
  `theta^2*rho0 = 2 - 6*alpha + alpha^2`。
  `sigma(x)-x = K*theta^2*rho0` は
  `x = a + K*alpha + K*alpha^2` を強制する。
  このとき七乗の alpha 係数と alpha^2 係数の差は厳密に
  `-49*K^2*(3*a^5+40*a^4*K+295*a^3*K^2+1293*a^2*K^3+3145*a*K^4+3278*K^5)`。
  一方、元の source はその二係数が等しい。
  現行正規化の `K=7^(10+14*k)*u^14` は非零かつ `7 | K`。
  従って差が零なら括弧内を mod 7 で評価して `7 | a`、
  これは元の根の theta residue 非零に反する。
  **校正値排除 `W != rho0` の具体的な証明候補**であり、次に Lean で検証する。
- `DkMathTest/FLT/SevenCalibrationExclusionAstra02Scratch.lean` を追加し、
  `lake env lean DkMathTest/FLT/SevenCalibrationExclusionAstra02Scratch.lean` が
  exit 0 で通過した。
  `directOrbitDeepJetWUnit_ne_calibration` は現行 `h`, `hc`, `eta`, `heta`
  のみを入力とし、`W != rho0` を結論する。
  `#print axioms` は `[propext, Classical.choice, Quot.sound]`。
  検証の初期段階の座標簡約エラーは修正済み。
  `C=1` 全体の排除ではないが、R46 時点で残っていた校正点を
  **元の七乗 source の二次以上の係数条件**で排除できた。
- `DkMathTest/FLT/SevenQuotientPrimeAstra02Scratch.lean` も単独実行で exit 0。
  `directOrbitCommonPrime_q_mod_seven_one` は
  `h : DirectOrbitCanonicalCommonFactorPacket p`, `q.Prime`, `q | h.c` から
  `q % 7 = 1` を証明する。公理は同じ三つのみ。
  `q % 7 = 6` の枝を実際に排除し、R46 の「この枝で Kummer 条件が自動」
  という局所条件の弱さを、**別の商側素点の元の根の比**で補った。
- 同じ scratch で `twist_ratio_cyclic_product` も証明し、再度 exit 0。
  三つの共役にわたる比の積 `R*sigma(R)*sigma^2(R)=-1` を kernel 検証した。
  三つの監査対象定理の公理はすべて `[propext, Classical.choice, Quot.sound]`。

## A. 三つの候補

以下では元の根を `x = p.rho`、固定校正 unit を `rho0 = directOrbitDeepJetRho`
と区別する。`sigma = rotateEquiv`、`t = h.squareRefinement` とする。

| 候補 | この調査での到達点 | 矛盾の範囲 |
| --- | --- | --- |
| 1. 元の七乗 source による校正値排除 | `W != rho0` を kernel 検証 | `W = rho0` という追加仮定を排除 |
| 2. 商側素点での元の根の比 | `q % 7 = 1` を kernel 検証 | 共通素因子の `q % 7 = 6` 枝を排除 |
| 3. 位相比較を伴う六次共役素点への接続 | exact target と不足補題を特定 | 接続だけではまだ矛盾にならない |

### A1. 元の七乗 source による校正値排除 — 検証済み

**Exact statement.** 現行の `source`, `r`, `p` のもとで、任意の
`h : DirectOrbitCanonicalCommonFactorPacket p` に対し、

```lean
(hc : h.c = 1)
(eta : SevenRealCubicIntˣ)
(heta : h.squareRefinement.gapSquareRoot =
  (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt))
⊢ directOrbitDeepJetWUnit h.squareRefinement eta ≠ directOrbitDeepJetRho
```

を証明した。証明本体は
[SevenCalibrationExclusionAstra02Scratch.lean](../../../DkMathTest/FLT/SevenCalibrationExclusionAstra02Scratch.lean)
の `directOrbitDeepJetWUnit_ne_calibration`。

**独立な方程式と証明。**

```text
theta^35 * thetaSevenUnit^12 = -7^11 * (2 + alpha + alpha^2)
source = L*R + 7^11*G^14*(2 + alpha + alpha^2)
(x^7).snd = (x^7).thd
```

これは `norm W=1` や `Phi(W)=0` ではなく、`p.source_eq_pow` の正確な
七乗方程式から得られる。`W=rho0` を仮定すると、正規化は

```text
sigma(x)-x = K*theta^2*rho0,   K = 7^(10+14*k)*u^14
theta^2*rho0 = 2 - 6*alpha + alpha^2
x = a + K*alpha + K*alpha^2,   K != 0,   7 | K
```

となる。七乗の二係数の差は

```text
-49*K^2*F(a,K)
F(a,K) = 3*a^5 + 40*a^4*K + 295*a^3*K^2
       + 1293*a^2*K^3 + 3145*a*K^4 + 3278*K^5.
```

したがって `F(a,K)=0`。これを mod 7 に写すと `3*a^5=0`、従って `a=0`。
元の根の `thetaResidue x = a+12*K` も零となり、
`p.thetaResidue_ne_zero` と矛盾する。

**依存。**

- `PrimeTraceOneDirectCyclotomicUnitCongruence.lean`:
  `directChosenQuotientRealSource`。
- `PrimeTraceOneDirectRealCubicOrbit.lean`:
  `DirectRealCubicRootPacket.source_eq_pow`, `thetaResidue_ne_zero`。
- `PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean`,
  `PrimeTraceOneDirectRealCubicSquareRefinement.lean`:
  `gap_eq`, `gapCore_eq`, `gapRoot_eq`。
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`:
  `directOrbitDeepJet_normalization`, `directOrbitDeepJetRho_val`。
- `SevenRealCubicThetaSeventhPower.lean`:
  `thetaLinear_pow_seven`, `thetaSquare_pow_seven`。既存の展開定理を再利用した。

**不足補題。** この bridge 自体の不足は scratch で解消した。
`C=1` 全体の矛盾には、残る `W=rho0*t^(7^9)` を元の source と合わせて
排除する追加定理が要る。例えば、この provenance のもとで `W=rho0` を強制する
rigidity があれば今回の定理と衝突するが、その rigidity は本調査の結論ではない。

**非循環性。** 歴史層の terminal theorem は呼ばない。
主定理は現在の同じ `source/r/p/h` を最後まで保持し、校正値不等式を
仮定していない。`PairedDeepJet` の import も不要と確認した。
`7^9` からさらに高い深さを取り出す議論ではない。

**到達点・規模。** 単なる正規形追加ではなく校正枝の厳密排除。
約 150 行の独立 scratch で完了。production 化は既存証明の移設・命名整理・
facade/test 接続を含む小規模 checkpoint にできる。

### A2. 商側素点での原始七乗根 — 検証済み

**Exact statement.**

```lean
(h : DirectOrbitCanonicalCommonFactorPacket p)
(q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c)
⊢ q % 7 = 1
```

[SevenQuotientPrimeAstra02Scratch.lean](../../../DkMathTest/FLT/SevenQuotientPrimeAstra02Scratch.lean)
の `directOrbitCommonPrime_q_mod_seven_one`。
その直下の入力を弱めた版は、任意の square-refinement packet と
`q | natAbs(norm gapSquareRoot)`, `q | natAbs(norm quotientSquareRoot)` で成り立つ。

**証明。** 商側の素点 `Q` を選び、complete split から residue field を
`F_q` と同型にする。評価 `f` は `quotientSquareRoot` を零にするので
`f(seventhQuotient (sigma x) x)=0`。
元の二根の互いに素性から `f(x), f(sigma x)` はともに非零。
`q != 7` なので二つの評価が等しければ商は `7*f(x)^6 != 0` となり矛盾。
よって `f(sigma x)/f(x)` は位数 7 の unit であり、`7 | q-1` を得る。

**依存。**

- `PrimeTraceOneDirectRealCubicSquareIdealSupport.lean`:
  `directOrbitSquareRefinement_exists_distinct_prime_ideals`,
  `directOrbitSquareRefinement_mem_of_principal_dvd`。
- `PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean`:
  `common_norm_prime_complete_split`。
- `PrimeTraceOneDirectRealCubicResidueSupport.lean`:
  `residueField_card_of_inertiaDeg_one`。
- `PrimeTraceOneDirectRealCubicOrbitSplit.lean`:
  `directOrbit_roots_isCoprime`。
- `SevenRealCubicAxisDrop.lean`:
  `pow_seven_sub_pow_seven_factorization`。
- Mathlib の `FiniteField.ringEquivOfCardEq`, `orderOf_eq_prime`,
  `ZMod.orderOf_units_dvd_card_sub_one`。

**不足・非循環性。** この合同式 bridge は完成。
歴史層 `SevenRamifiedFusionCyclotomicPrimeAddress.lean` の
`prime_dvd_quotientRoot_modSeven_eq_one` の位数論は参考にしたが、その歴史
packet を構成したり結論を適用したりせず、中立な評価補題を証明した。
新しい根の restart は行わず、元の `p.rho` を使う点が重要。

**到達点・規模。** `q % 7 = 6` 枝の実際の矛盾。ただし `C>1` 全体は残る。
`379 % 7 = 1` であり、R38 scratch の `(beta,z)=(206,29)` は
新しい合同式でも除かれない。この例は reduced Kummer 方程式の局所解であって、
現行 packet や元の 14乗条件を実現した例ではない。主 bridge は約 110 行。

### A3. 位相を明示した六次共役素点 bridge — 提案段階

**Exact proposed statement.** A2 の商側 residue 評価
`f : SevenRealCubicInt →+* F_q` と `tau=f(sigma x)/f(x)` を固定する。
`A6 = SevenCyclotomicDegreeSixInt.Ring` とする。この同じ評価に対して

```text
exists j : Nat, 1 <= j <= 6,
exists e : A6 ->+* F_q,
  e.comp(ofReal) = f
  e(zeta)^j = tau
  Pplus  = ker(e)
  Pminus = ker(e.comp(starRingEnd))
  Pplus, Pminus are distinct maximal ideals
  Ideal.map ofReal (ker f) = Pplus * Pminus
  ofReal(sigma x) - zeta^j * ofReal(x) belongs to Pplus, not Pminus.
```

ここで `Pplus`, `Pminus` は表示した定義、`j` は現行 `Q` に合う位相である。
`j=1` の固定を無証明で行ってはいけない。

**依存と不足。**

- `SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean` の
  `zeta_quadratic_relation`, `localEval` の証明。
- `SevenRamifiedFusionCyclotomicConjugatePrimePair.lean` の
  `ratio_val_ne_inv`, `conjugatePrimeProduct_le_realPrimeFiberIdeal`,
  `realPrimeFiberIdeal_eq_conjugateProduct` の線形代数部分。
- `SevenRamifiedFusionGlobalOrientedPrimeFactorization.lean` は六次回転と共役の
  可換性を提供するが、後段の load family は歴史 packet に依存する。
- 必要なのは、原始七乗根の三つの実 trace と `f(alpha)` を対応付ける位相補題、
  および `localEval` / 共役積証明を歴史 packet から独立させる中立版。
  `f(alpha)=1+tau+tau^-1` を入力なしに決めることはできない。

**非循環性。** A2 が作った商側評価から出発し、歴史側 quotientRoot の素数で
あるとは仮定しない。packet の名前だけを置き換える橋ではない。

**到達点・規模。** これは orientation を失わない正確な接続であり、
接続そのものは矛盾ではない。局所版は数百行程度と見積もる。
さらに global valuation ownership を現行 carrier 全体へ運ぶには、
全 prime support と multiplicity の一致が必要で、別の中～大規模作業。
偶数重複度と共役素点への片側配分は両立するので、14乗というだけで
parity contradiction は出ない。

## 補足監査 — 指定された六つの優先事項

### 六次 fusion / real pair / load

`SevenRamifiedFusionOrientedCarrierValuationOwnership.lean` の
`realKernel_product_eq_span_prime`, `carrier_mem_orientedKernelPower_iff`,
`globalCarrierFactorIdeal_pair_exact` は歴史側の carrier と load support の定理。
`SevenRamifiedFusionLoadedResidualIdealBridge.lean` の
`carrierIdealPair_eq_ramified_sq_mul_loadHalves_mul_residualPair_pow` は
**共役との積**の分解であって、任意の現行 carrier の片側分解ではない。
`SevenRamifiedFusionRealPairCoprimalityNormGate.lean` の
`realPairCores_pairwiseCoprime` や `quotientRoot_signedSeventhPower_iff_row2_cells`
も signed-root routing / row2 cell を要求する。
従って「one-to-two 配分があるから歴史の終端を呼べる」とはならない。

### 14乗の平方成分と三素点の積

`directOrbitCommonPrime_fourteen_power_ratio` の正確な出力を
`y^14 = R`、`directOrbitCommonPrime_global_seventh_correction` を
`R = kappa*w^7` と書く。ここで `R=-c2/c1`, `kappa=alpha*(1+alpha)`。
R38 の変数変換は `z=y^2/f(w)` なので、捨てた情報は

```text
z^7 = f(kappa)  と  z*f(w) = y^2
```

の後半である。`z` や `f(kappa)` 自身が平方だとは言えない。
補正 unit `w` の平方性が必要になる。

三つの twist 係数のノルムはすべて 1 であり、`norm R=-1`。
従って正確な積は `R*sigma(R)*sigma^2(R)=-1`。
この積等式は `SevenQuotientPrimeAstra02Scratch.twist_ratio_cyclic_product`
として kernel 検証済み。
これを一つの residue 評価に写し、二次指標を適用すれば積は `chi(-1)`。
しかし現行定理が 14乗を保証するのは向き付けた **gap 素点での一つの比**。
回転すれば消える root の添字と係数比も変わるので、同じ `R` の三評価が
すべて平方だとはならない。
例えば抽象的な指標配分 `(+,+,-)` は「一評価は平方」と「積は -1」に
両立する。この配分を global packet として構成したという主張ではなく、
積条件だけでは符号矛盾に不足することの確認である。

### ノルム一次変分と新しい方程式

`SevenRealCubicNormFirstVariation.lean` の
`norm_add_seven_cube_axis_mul` は中立で再利用可能。
ただし現行の二元 `x,sigma(x)` に適用すると
`norm(sigma(x))-norm(x)=0` である。
歴史の `RamifiedNormFirstVariationPacket.coefficient_eq_gapRoot` は、
別途与えた signed-root norm gap から非零右辺を得ており、
これを現行の共役二元へ転用できない。
今回実際に独立情報を与えたのは norm 差ではなく、A1 の **七乗 source の係数差**。

### 同型 provenance の小さい successor

`PrimeTraceOneDirectRealCubicSuccessorAudit.lean` の小さいノルムは、
抽出した twisted root のノルムであり、新たな自然数反例の構成ではない。
`PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean` の
`directOrbit_no_ordinary_homogeneous_restart`,
`directOrbit_twistedCoeff1_not_unit_gauge` は依然有効。
square restart の非平方障害も維持される。ここで「coefficient zero」は
値が零という意味ではなく **添字 0 の係数**。
同型の `PrimitiveCounterexampleRamifiedProvenance` を得るには、自然数三つ、
非零性・原始性・Fermat 方程式・routing・同じ尺度での strict decrease を
再構成する必要がある。今回の不等式と合同式はそれを供給しない。

## B. 最優先候補 — A1 の校正値排除を選択

次の一手は **A1 のみ**とする。

- generic Thue 完全分類より小さい。解集合の上界は不要で、元の source が
  特定の校正方向を許さないことを整数多項式と mod 7 で証明できた。
- 基本 unit の明示計算より小さい。unit 群の生成・regulator・指数 1 を使わない。
- finite Hensel の延長とは異なる。深さを増やさず、既存の射影で失った
  元の七乗方程式を保持して、実際の候補を一つ排除した。
- A2 も有効だが、`C>1` で許される `q=379` 型の局所データは残る。
  A1 は R46 の明示的な「校正値排除が無い」という障壁を直接取り除く。

この選択は FLT7 完成を約束するものではない。
新しい frontier は「校正値を含む正規形」から
**「校正値を除外した高冪 coset と source の同時制約」**へ変わった。

## C. R47 checkpoint

[astra-002-r47-checkpoint.md](astra-002-r47-checkpoint.md) に実装用仕様を分離した。
主目標は A1 の一つの public bridge。
既存の重い `SevenRealCubicThetaSeventhPower.lean` や
`PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean` に追記せず、
独立した `PrimeTraceOneDirectRealCubicCalibrationExclusion.lean` を使う。
A2 と A3 を同じ checkpoint へ混ぜない。

## D. 停止条件と検証

**credible bridge は存在し、A1 と A2 は scratch で検証できた。**
従って今回の判定は「何も打開できない」ではない。
ただし、現在の追加結果だけを使った一般の `False` や descent は結論しない。

- `C=1` の終端には、元の source を保持した rigidity / 非校正解排除が必要。
  norm-one trace-plane unit の完全分類そのものを今回証明したわけではない。
- `C>1` の終端には、`q=1 mod 7` でなお許されるデータを排除する
  global な orientation/character 制約が必要。A3 の接続だけでは不足。
- 今後 A3 が単に局所 factorization を言い換えるだけに留まったら、
  valuation や符号の不一致が明示されるまで矛盾へ進めない。
- finite-Hensel の追加一段、unit 群の明示生成、有限実験の完全性を補わない。

検証はすべて `lean/dk_math` で **一件ずつ**実施。
SymPy の厳密演算は発見用であり、主要な恒等式と二つの bridge は
Lean の証明を別途用意した。実行記録は
[astra-002-verification.log](astra-002-verification.log) に保存した。
