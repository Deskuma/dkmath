# ASTRA-000 — cubic orientation / boundary reconnaissance

## 判定

**Outcome B — partial theorem survives but main gain is unproved.**

H1 の gcd・重複支持分離、さらに両向きの実際の repeated modulus の互いに素性と、H2 の実定義による `t = 3/8` target boundary bound が scratch Lean で成立した。局所定理は production 化できる。一方、大プロファイルの和、固定和での一様な paired counting、元の ABC radical/quality との coupling は未証明である。ABC の無条件 endpoint は得ていない。

今回の依頼は ABC 予想の Lean 形式化であり、添付資料はその初期段階を指定する計画文書として扱った。現在 active と記された ASTRA-000 の調査・反証・scratch 検証・報告を実行し、後続段階への自動的な実装拡張は行っていない。

## 1. Workspace と検証資料

- 日付: 2026-09-06。
- Repository: `/home/deskuma/develop/lean/dkmath`。
- Source/build cwd: `lean/dk_math`。
- Branch: `wip/ABC-GN-astra-260906-v0`。
- HEAD: `1a829484842bc4343beab45f6a9f3625b932bbf8`。
- ローカル `develop` と取得済み `origin/develop`: `cb89c5a747f0f74cc9aa10a0cc50cf97bb569ed8`。
- `develop..HEAD`: `7f22f584b` README、`a8bf599a1` roadmap、`1a8294848` instruction の3文書コミット。Lean ソースの差分はない。
- 比較対象は現在のローカル refs / workspace であり、GitHub の最新状態を再取得した比較ではない。
- 作業開始時の worktree は clean。Lean toolchain は `leanprover/lean4:v4.32.2`。

再現資料:

- [scratch-000.lean.txt](scratch-000.lean.txt): 検証済み scratch の保存用テキスト。production import surface には含まれない。
- [numeric-000.py](numeric-000.py): exact integer factorization、有限探索、固定和 CRT、有限 Hensel/CRT 実験。SymPy 1.12 を使用。
- [validation-000.txt](validation-000.txt): build、Lean dependency audit、数値出力。

最初に指定された次の9ファイルを読み、その後、定義・利用箇所・import を追跡した。

```text
DkMath/ABC/GNExcessLargeBoundaryPacket.lean
DkMath/ABC/GNWieferichAccumulation.lean
DkMath/ABC/GNCubicPetalWieferich.lean
DkMath/ABC/GNCubicOrientedContract.lean
DkMath/ABC/GNJointContractEquivalence.lean
DkMath/NumberTheory/GNThreePrimeArithmetic.lean
DkMath/NumberTheory/GNThreeHenselLift.lean
DkMath/NumberTheory/GNThreeHenselDepth.lean
DkMath/NumberTheory/GNWieferich.lean
```

追加で `GNExcessActiveProfiles`、`GNExcessEulerMajorant`、`GNPrimeSupportOrder`、`GNJointPressureOddPrime`、`ABCEpsilonIdentity`、`ABCEpsilonJointPressureBridge`、`ABCMainTheorem` と関連定義を確認した。`ABCMainTheorem.lean` の `abc_main` は現在も `abc_main_axiom` を適用している。

## 2. Task A — exact frontier theorem map

以下の省略識別子は、特記しない限り `DkMath.ABC` 名前空間。

### Arithmetic / support / modulus

| 層 | 現在の識別子と内容 |
|---|---|
| repeated part の支持 | `repeatedPrimePowerPart_factorization_support`: factorization support を valuation ≥ 2 で filter した集合 |
| square-tail 表現 | `GNNonExceptionalRepeatedPart_eq_piSqRad_mul_sqTail`、`GNNonExceptionalRepeatedPart_eq_piSqRad_sq_mul_twoTail` |
| target active support | `GNExcessActivePrimeSet_target_eq_repeatedSupport` |
| target modulus | `GNExcessJointDepthModulus_target_eq_repeatedPart` |
| active / Wieferich 同値 | `mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift`: membership ↔ `¬ q ∣ p ∧ GNWieferichLift p a b q` |
| Wieferich / repeated 同値 | `GNNonExceptionalWieferichPrimeSet_eq_repeatedSupport` |
| full depths の積 | `GNNonExceptionalRepeatedPart_eq_wieferichPrimePowerProduct`: `∏ q ∈ GNNonExceptionalWieferichPrimeSet p a b, q ^ padicValNat q (GN p a b)` |
| large packet | `GNExcessLargeBoundaryPacket.of_target`、`GNWieferichAccumulationPacket.of_target` |

最初の target support / modulus 同定は `hp : Nat.Prime p`、`a ∈ Icc 0 X`、`Nat.Coprime a b` を要求する。Wieferich 同値・積表現には正の `a,b` が加わる。packet はさらに `X+1 < modulus` を仮定し、counting estimate を提供しない。

`N = GNNonExceptionalPart p a b` とすると、厳密に

```text
M = repeatedPrimePowerPart N
  = piSqRad N * sqTail N
  = (piSqRad N)^2 * twoTail N.
```

### 実際の mass と charge

`GNExcessActiveProfiles.lean` の定義は、有限素数族 `Q` と excess profile `e` に対し

```text
e_q = GNExcessProfileValue Q e q
S   = GNExcessActivePrimeSet Q e = {q ∈ Q | 0 < e_q}
mass = GNExcessActiveProfileMass Q e = ∑ q ∈ Q, e_q * log q
M    = GNExcessJointDepthModulus Q e = ∏ q ∈ S, q^(e_q+1)
R    = GNExcessRootAddressCharge Q p e = (p-1)^|S|.
```

自然数から実数への cast は上記数式では省略した。target は
`Q = GNNonExceptionalIntervalPrimeFamily p b X`、
`e = GNExcessDepthProfileAt Q p b a` であり、`e_q = v_q(GN p a b)-1` は自然数の切り捨て減算。

`GNExcessActiveProfileMass_target_eq_log_sqTail` が `mass = log (sqTail N)` を与える。`GNExcessRootAddressCharge_target_le_piSqRad` は `R ≤ piSqRad N`、`GNExcess_target_boundaryWeight_le_repeatedPart_rpow` は正の互いに素な target に対し

```text
R * exp ((1/2) * mass) ≤ M^(3/4)
```

を与える。名前は一般素数を許し、ここに oddness の仮定はない。

### 開いたままの和

`GNExcessLargeBoundaryProfileSum Q p b X t` は、`GNExcessDepthProfileSpace` 内で `X+1 < M(e)` を満たす **全 profile** の `R(e) * exp(t * mass(e))` の和である。実現された互いに素な target だけの和ではない。

`card_GNExactExcessProfileEvent_le` は

```text
card exactFiber ≤ R * ((X+1)/M + 1)
```

を与える。`card_GNExactExcessProfileEvent_le_largeBoundary` では `M>X+1` により商が0になり、`card exactFiber ≤ R` が残る。

`exp_GNExcessMassAt_sum_le_finiteEuler_add_large` は任意の実数 `t` について有限 Euler 項とこの境界和に分解する。`exp_GNExcessMassAt_sum_le_halfEuler_add_large` は `t=1/2` で

```text
∑ a ∈ Icc 0 X, exp ((1/2) * GNExcessMassAt Q p b a)
 ≤ 2*(X+1)*GNExcessHalfEulerConstant p
   + GNExcessLargeBoundaryProfileSum Q p b X (1/2)
```

まで。後者の和を一様に制御する定理は、この利用鎖にない。

`DkMath/**/*.lean` の `boundaryWeight`、`3/8`、`3 / 8`、`GNExcessLargeBoundaryProfileSum` と関連語の検索では、対象評価の後続改善・和の閉鎖は見つからなかった。既存の cubic Petal / oriented contract はこの評価の改善ではない。

### ABC 強度の境界

- `Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime` は例外的 valuation excess を消去する。
- `Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass` は lifted joint pressure と fresh support + non-exceptional excess を同定する。
- `Triple.nonExceptionalChannelMassBudget_iff_log_GN_le` は例外 support 項を保持した `log GN` 上界と同値。
- `ABCRawBound_iff_nonempty_GNOddPrimeJointContract` と `ABCRawBound_iff_nonempty_GNCubicOrientedContract` は、`ε>0` の下でそれぞれの uniform contract が raw ABC と同じ強度であることを示す。provider を構成する定理ではない。
- `Triple.quality_eq_one_add_abcEpsilon`、`Triple.abcEpsilon_eq_valuationExcess_sub_log_rad_ab_div_log_rad_abc` は正の triple の厳密な座標恒等式。
- `eventually_quality_lt_one_add_of_oddPrime_jointPressure` も joint budget と radical の発散を仮定する。

`exists_oriented_cubicPetalWieferichPacket` の分岐は、選ばれた primitive prime の valuation ≤ 1 **または** Wieferich lift である。片向き全体が squarefree という命題ではない。

## 3. Task B — Lean で成立した orientation arithmetic

保存 scratch の `Astra000` 名前空間で次を証明した。

| 識別子 | 証明済みの内容 |
|---|---|
| `orientation_identity` / `orientation_identity_swap` | 指定された2本の整数係数恒等式 |
| `orientation_gcd_dvd` | `Nat.Coprime a b → Nat.gcd (GN 3 a b) (GN 3 b a) ∣ 14` |
| `no_common_prime_square` | 任意の素数 `q` について両向きに `q²` が同時には割り込まない |
| `wieferich_disjoint` | 実際の `GNNonExceptionalWieferichPrimeSet` 同士の `Disjoint` |
| `repeated_parts_coprime` | 正の互いに素な `a,b` の実際の `GNNonExceptionalRepeatedPart` 同士の `Nat.Coprime` |

`GN_three_dual_explicit` により `F=a²+3ab+3b²`、`G=b²+3ab+3a²`。自然数 GN 値を明示的に `ℤ` へ cast し、`ring` で恒等式を検証した。共通 divisor は `14a³` と `14b³` を割り、`gcd(a³,b³)=1` により14を割る。

14は squarefree なので `q² ∣ 14` はどの素数でも不可能。`q=2,7` を除外する追加仮定は不要である。7が両 GN 値に一度以上現れることは許される。実際、指定回帰例は F に `7¹`、G に `7³` を持つ。このため通常の prime support の分離とは区別する。

`wieferich_disjoint` は定義を直接使い、positivity なしで証明できた。実際の repeated part の互いに素性への transport では、GN の非零性を確保するため正の `a,b` を仮定した。

## 4. Task C — exact regressions / counterexamples

### 指定例は正しい

`605 + 370688 = 371293`、`gcd(605,370688)=1`。

```text
GN 3 605 370688 = 412901944777 = 7 * 37² * 1777 * 24247
GN 3 370688 605 = 138083490139 = 7³ * 41413 * 9721
```

因数の素数性も Lean で検証した。重複素数集合は `{37}` と `{7}`、non-exceptional repeated modulus は `1369` と `343`。共通 gcd は7である。

### 強すぎる主張への反例

| 主張 | 反例 / 結果 |
|---|---|
| 片向きは常に squarefree | `(a,b)=(11,40)`: `F=79²=6241`、`G=7²*67=3283` |
| 片向きは常に Wieferich-free | 同じ例で `GNWieferichLift 3 11 40 79` と `GNWieferichLift 3 40 11 7` を Lean 証明 |
| 両 repeated moduli は同時に大きくなれない | 「大きい」を共通 `X=c` に対する `M>X+1` と明示すると、`(56,59,115)` が反例。`F=13²*139=23491`、`G=151²=22801`、`M_F=169>116`、`M_G=22801>116` |
| 重複支持そのものの分離が偽 | 反例なし。有限探索による推測ではなく Task B の一般 Lean 証明で成立 |
| paired CRT なら境界 `+1` を消せる | 次節の固定和例が pure density bound の反例 |

`2≤c≤1000`、`1≤a<b`、`a+b=c`、`gcd(a,b)=1` の152,095組を exact integer arithmetic で走査した。`gcd(F,G) ∣ 14` と共通 repeated prime の不在を検査し、反例0件。列挙順は `c`、次に `a` の昇順。上の `(11,40)`、`(56,59)` はこの走査で最初に検出した該当例である。走査は対角 `a=b=1` とゼロ座標を含まないが、一般 Lean gcd / support 定理は含む。

さらに `b=1` で `7^k ∣ GN 3 a 1` と `13^k ∣ GN 3 1 a` を Hensel digit と CRT で同時に満たす例を `k=2,4,8,16` で構成・整数検算した。例えば `k=16` では

```text
a = 8231168636035898637629074937191
7^16  = 33232930569601
13^16 = 665416609183179841.
```

これは有限深さの計算証拠であり、一様密度定理でも、無限族の Lean 定理でもない。「large」に別の高さ依存閾値を置く主張まで反証したとは扱わない。

## 5. Task D — actual cubic 3/8 bound

`Astra000.cubic_boundary_three_eighths` は `ha>0`、`hb>0`、`haX : a∈Icc 0 X`、`Nat.Coprime a b` の下で、依頼にある **そのままの定義** に対して

```text
(GNExcessRootAddressCharge Q 3 E : ℝ)
  * exp ((3/8) * GNExcessActiveProfileMass Q E)
≤ (GNNonExceptionalRepeatedPart 3 a b : ℝ)^(3/8)

Q := GNNonExceptionalIntervalPrimeFamily 3 b X
E := GNExcessDepthProfileAt Q 3 b a
```

を証明した。large 仮定は不要で、canonical target 全体に成立する。

実際に使った congruence API は `Triple.mod_eq_one_of_mem_GNNonExceptionalSupport Nat.prime_three ha`。`GNExcessActivePrimeSet_target_eq_repeatedSupport` と `GNNonExceptionalPart_factorization_support` で active prime をこの API に運び、`q%3=1` と prime から `7≤q` を得る。

`A=piSqRad N`、`C=sqTail N`、`R=2^|S|` とおくと、各 `q∈S` に対する整数不等式 `256=2^8≤7^3≤q^3` の積から

```text
R^8 ≤ A^3
log R ≤ (3/8) log A
mass = log C
M = A*C
```

となり、`R*exp((3/8)*mass)≤M^(3/8)` が従う。depth `k≥2` での `2*q^((3/8)*(k-1))≤q^((3/8)*k)` を全体の厳密な積・対数座標で実現した証明である。

中間 `1/2` theorem は経由せず直接通った。以前の `t=1/2`、右辺指数 `3/4` と比べ、**重みパラメータも右辺指数も変更**している。`t=1/2` を固定したまま右辺だけ `3/8` に改善した命題ではない。

この証明は既存 exact-order support と square-tail identity だけで成立し、新しい Hensel theorem は使用しない。Hensel は deep lift を排除できないという戦略上の監査に効いている。既存コードに同じ target bound は見つからなかった。

## 6. Task E — small-profile parameter audit

定義と積分解は既に一般の `t : ℝ` を持つ。

- `GNExcessLocalDensityWeight p q j t` は `j=0` なら1、`j>0` なら `(p-1)*exp(t*j*log q)/q^(j+1)`。
- `GNExcessLocalDensityFactor`、`GNExcessLocalDensityTail`、`GNExcessFiniteEulerDensity` も一般の `t`。
- `sum_GNExcessProfileDensityWeight_eq_prod`、`GNExcessFiniteEulerDensity_le_envelope`、`GNExcessFiniteEulerDensity_le_envelope_of_tail`、moment split も一般の `t`。
- 一方、`GNExcessLocalDensityTail_half_le`、`GNExcessFiniteEulerDensity_half_le`、`exp_GNExcessMassAt_sum_le_halfEuler_add_large` は構文上 `1/2` に固定されている。

prime `q` では `log q>0`、`j≥0` なので、`3/8≤1/2` により各 local weight は既存 half weight 以下となる。正の depth の連続比は `q^(t-1)`、したがって `q^(-1/2)` から `q^(-5/8)` へ小さくなる。最初の正の depth も `q^(-3/2)` から `q^(-13/8)` へ改善する。

最小追加 surface は local weight の `t` 単調性と有限和への transport である。その結果を `GNExcessLocalDensityTail_half_le` に合成し、既存の `GNExcessHalfPowerEnvelope` とその summability、`GNExcessFiniteEulerDensity_le_envelope_of_tail` を再利用すれば、同じ定数の `3/8` Euler bound を得る設計になる。新しい無限積理論の再構築は不要。

これは source と数式の監査結果であり、この checkpoint では要求どおり refactor / 新しい small-profile Lean theorem は実装していない。また、小さい `t` は同じ閾値に対する Chernoff の `exp(-t*threshold)` を弱める面もあるため、local decay の改善だけから最終 tail estimate の改善を宣言できない。

## 7. Task F — fixed-sum paired CRT の実験と限界

`c=a+b` を固定し、同じ移動座標 `a` を使うと整数多項式は

```text
F_c(a) = a² - 3ca + 3c²
G_c(a) = a² + ca + c².
```

Task B により **実際の target** の `M_F,M_G` は互いに素。ただし既存の片向き interval machinery は `b` を固定して `a` を動かすものであり、`b=c-a` を代入する paired family への counting transport は別途必要である。

`c=115`、`M_F=13²=169`、`M_G=151²=22801` の exact finite CRT 実験では

```text
F_c の roots mod 169   = [56,120]
G_c の roots mod 22801 = [56,22630]
積の法                = 3853369
CRT addresses          = [56,455849,2097748,2553541]
1 ≤ a ≤ 114 の解        = [56].
```

したがって `card≤4*114/3853369` という境界項なしの密度上界は偽である。積の法に移しても、正しい形は各 address の `floor(length/modulus)+1` を保持する。実現 target があるため、大きな積の法だけでは解を0個にできない。

この有限例は、fixed-sum relation と coprime moduli が常に congruence incompatibility を起こすという期待を否定する。一方、pair 全体の sparsity、頻度、height に応じた分布の一様評価を否定する例ではない。有限 Hensel の uniqueness からそれらを導くこともできない。

## 8. 残る正確な障害

1. `3/8` theorem は実現された正の coprime target の単項上界。`GNExcessLargeBoundaryProfileSum` の全 profile は未実現の profile も含み、そのまま target theorem を適用できない。
2. target 単項上界の右辺 `M^(3/8)` は増加量であり、profile 数・配置の制御を与えない。和を取っても独立な一様 provider は得られない。
3. paired moduli の互いに素性から積の法は得られるが、CRT boundary `+1` が残る。固定和例でこの問題が実際に現れる。
4. large `abcEpsilon` と両向きの repeated debt を結び、境界和の制御または厳密な下降を与える theorem がない。fresh support mass と repeated depth を取り違えてはいけない。
5. `ABCRawBound` と同値の contract を仮定して穴を埋めることは独立な前進にならない。

## 9. instruction-001 への推奨

次の checkpoint は **選択肢 A: orientation gcd / repeated-support disjointness の production 化**を推奨する。gcd → prime-square exclusion → actual Wieferich disjointness → repeated-parts coprimality の鎖は全て scratch Lean で検証でき、paired route に必要な独立の新しい arithmetic input である。positivity が不要な層と必要な transport 層を分け、今回の数値回帰を保持する。

選択肢 B の actual cubic `3/8` target theorem も production 化可能であり、後続の短い checkpoint にできる。small-profile 側は単調性を追加する小さな接続で足りる見込み。ただしそれだけを長く積み重ねても境界和は閉じない。

選択肢 C を行う場合は、固定和多項式・同じ移動座標・actual paired profile・CRT boundary 項を明示した有限 counting 実験に限定する。`+1` を制御する追加構造または ABC quality coupling の独立な利得を見つけることを go gate とする。普遍的な no-lift / no-simultaneous-large への復帰は反例により棄却する。現時点で route 全体を選択肢 D として破棄する根拠はない。

## 10. 検証結果と再現方法

`lean/dk_math` から実行:

```bash
./lean-build.sh DkMath.ABC.GNCubicOrientedContract DkMath.NumberTheory.GNThreeHenselDepth
cp docs/dev/ABC-GN-Astra-260906-v0/scratch-000.lean.txt /tmp/astra000-replay.lean
lake env lean /tmp/astra000-replay.lean
python docs/dev/ABC-GN-Astra-260906-v0/numeric-000.py
```

focused build と最終 scratch compile は exit 0。保存コードは一時ファイルへコピーして検証した。数値実験も完了した。

build は既存 `ZsigmondyCyclotomicResearch.lean:147` の `declaration uses sorry` warning を replay した。新しい scratch theorem と利用鎖の `#print axioms` は全て `[propext, Classical.choice, Quot.sound]` のみ。`sorryAx`、`abc_main_axiom`、研究用仮定への依存はない。import closure 中の未完成宣言と、実際に利用した theorem の依存を区別した。

追加の scratch audit では `GNCubicOrientedContract` と `ABCEpsilonIdentity` を import し、Petal existence、2つの contract equivalence、quality identity、odd-prime exceptional-zero、support-order theorem の `#print axioms` も同じ標準3公理のみであることを確認した。contract equivalence の証明が健全であることは、contract の無条件 existence を意味しない。

production の `DkMath/ABC`・`DkMath/NumberTheory` ソースは変更していない。本 checkpoint の成果物は、この報告と再現可能な検証資料である。
