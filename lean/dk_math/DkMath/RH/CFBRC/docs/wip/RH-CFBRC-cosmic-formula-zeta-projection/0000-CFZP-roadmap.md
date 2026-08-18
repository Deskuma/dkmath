# CFZP-0000 — 宇宙式からリーマンゼータ関数へ向かう CFBRC 射影 ROADMAP

## 0. Status

- Repository: `Deskuma/dkmath`
- Base: `develop`
- Base commit: `8fec261552dbc9757b972cf68613aa602b284461`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- 日本語を正本とする。

このフェーズでは、これまでの RH prime-side 解析を出発点にしない。

正本の向きを次に固定する。

```text
宇宙式
  ↓
Big / Body / Core / Beam / Gap
  ↓
CF2D / ThreeElement
  ↓
finite prime-power projection
  ↓
finite Euler / CFBRC observable
  ↓
completed-zeta / standard zeta
```

目的は「ゼータ関数を宇宙式に見立てる」ことではない。

宇宙式で先に Big を構成し、その Big に内在する Gap を exact に回収し、射影後の同じ量が既存 CFBRC / prime-side / zeta observable と一致するところまで Lean で橋を掛ける。

---

## 1. DkMath の正本 Core

一般 Core は変更しない。

`DkMath.CosmicFormula.CoreBeamGap` は既に一般次数について

`Big = Body + Gap`

`Body = Core + Beam`

`Big = Core + Beam + Gap`

を持つ。

二次の正本は

`Core = x^2`

`Beam = 2*x*u`

`Gap = u^2`

`Big = (x+u)^2`

である。

`DkMath.CosmicFormula.ThreeElement.Basic` は同じ二次構造を plus / minus の二観測へ拡張し、

`plusWhole = Core + interactionBeam + Gap`

`minusWhole = Core - interactionBeam + Gap`

`plusWhole - minusWhole = 2 * interactionBeam`

`plusWhole + minusWhole = 2 * squareMass`

を exact に持つ。

さらに `ThreeElement.Assimilation` / `ThreeElement.Collision` は same-object の pair-whole assimilation と interaction assimilation の衝突を一般 theorem として持つ。

この一般層へ RH 固有定義を逆流させない。

---

## 2. 新フェーズの第一原則 — Big を先に置く

これまでの prime-side sign mechanism では、最終的に有限 rectangle ledger の差

`RectangleBackground - TopZetaMismatchScalar`

が frontier として残った。

新フェーズでは、この差を最初から `Gap` と呼ばない。

順序は逆にする。

### Synthesis

宇宙式の source から

`Big_cosmic = Body_cosmic + Gap_cosmic`

を構成する。

### Recovery

同じ Big から

`Gap_recovered = Big_cosmic - Body_cosmic`

を回収する。

### Internal audit

Lean で

`Gap_recovered = Gap_cosmic`

を証明する。

これが閉じて初めて、その Gap は外から足した補正ではなく Big に内在する completion Gap と認める。

---

## 3. 三種類の Gap を混同しない

現時点では少なくとも三つの Gap 候補が存在する。

### 3.1 Cosmic coordinate Gap

中心座標を `δ` とすると二次宇宙式の純 Gap は

`Gap_cosmic = δ^2`。

RH の top-edge integration variable `u` と混同しないため、このフェーズでは中心からの実方向変位を `δ` と書く。

### 3.2 Prime-mirror amplitude Gap

既存 `PrimeMirrorOffsetCore` は positive-base mode `n` に対し

`L_n(δ) = exp (-δ * log n)`

`R_n(δ) = exp ( δ * log n)`

を持つ。

その product は exact に `1` であり、

`MirrorGap_n(δ) = (L_n(δ) - R_n(δ))^2`

は非負。

さらに `n > 1` では

`MirrorGap_n(δ) = 0 ↔ δ = 0`。

`δ = centeredSigma (Re s)` とすれば

`MirrorGapAt_n(s) = 0 ↔ Re(s) = 1/2`。

また既存 source は

`squareMass(L_n,R_n) = interactionBeam(L_n,R_n) + MirrorGap_n`

を持ち、interaction は product invariant により `2` である。

従って mode level では既に

`MirrorBig_n = 2 + MirrorGap_n`

という「Big から Gap を読む」exact completion がある。

### 3.3 Rectangle/source remainder

`RectangleBackground - TopZetaMismatchScalar`

は現時点では Gap と同一視しない。

この量が 3.1 または 3.2 の Gap の射影像であることを exact theorem が示した場合にのみ、Gap と呼ぶ。

---

## 4. Prime-mirror Big を最初の RH 固有 Big とする

最初の RH 固有 Big 候補は、既に source-derived な mirror amplitude pair から作る。

```text
MirrorBig_n(δ) := squareMass (L_n δ) (R_n δ)
MirrorBody_n(δ) := interactionBeam (L_n δ) (R_n δ)
MirrorGap_n(δ) := (L_n δ - R_n δ)^2
```

既存 theorem から

`MirrorBig_n = MirrorBody_n + MirrorGap_n`

`MirrorBody_n = 2`

`0 ≤ MirrorGap_n`

`n > 1 → (MirrorGap_n = 0 ↔ δ = 0)`

が得られる。

ここでは `MirrorBody` という語を暫定的に使う。一般 `CoreBeamGap.BodyN` と definitional equality であるとは仮定しない。

第一実装目標は、この mode-level completion を新しい branch 上の projection API として名前を整理することである。

---

## 5. CFZP-001 — prime-power mode factorization

### 目的

finite PHZ を構成する実際の prime-power mode を、

```text
common radial carrier
× mirror amplitude
× cycle state
```

へ exact に分解する。

自然数 label `q > 1`、

`s = 1/2 + δ + i*t`

に対し概念的には

`q^(-s)`

を

`q^(-1/2) * exp(-δ*log q) * cycle_q(-t)`

へ、reflected point `1-s` では

`q^(-(1-s))`

を

`q^(-1/2) * exp(+δ*log q) * cycle_q(+t)`

へ分解する。

実際の theorem は既存 `eulerPrimePowerMode` / natural-label `Complex.cpow` 定義に合わせる。

### Firewall

- `arg` を導入しない。
- global `Complex.log` branch を導入しない。
- positive natural base の既存 `Complex.cpow` API だけを使う。
- infinite Euler product を使わない。

### 成功条件

左右 mode の実振幅部分が既存 `primeMirrorLeftAmplitude` / `primeMirrorRightAmplitude` と exact に一致する theorem を得る。

---

## 6. CFZP-002 — cosmic Gap と mirror amplitude Gap の analytic Beam

`δ^2` と `MirrorGap_n(δ)` は同じ量ではない。

次に求めるのは同一視ではなく factorization である。

概念目標は

`MirrorGap_n(δ) = δ^2 * MirrorGapBeam_n(δ)`

の形。

`MirrorGapBeam_n` は `δ = 0` でも regular に定義される analytic divided-difference / exponential Beam とする。

この theorem が閉じれば

```text
Cosmic coordinate Gap δ^2
  ↓ analytic Beam
Prime-mirror amplitude Gap
```

という PowerGapBeam の解析関数版が得られる。

### 重要

`MirrorGap_n = 0 ↔ δ = 0` が既にあるからといって、factorization theorem を省略しない。

零点集合の一致と、量そのものの射影 bridge は別である。

---

## 7. CFZP-003 — finite positive aggregate Big / Gap

finite prime-power support 上で von Mangoldt weight を用い、mode-level Big / Body / Gap を有限集約する。

まず非負の amplitude ledger を作る。

候補：

```text
AggregateMirrorBig_X
AggregateMirrorBody_X
AggregateMirrorGap_X
```

ここでは重みの positivity を保つ。

期待する exact theorem は

`AggregateMirrorBig_X = AggregateMirrorBody_X + AggregateMirrorGap_X`。

さらに cutoff が少なくとも一つ `n > 1` の positive-weight mode を含む場合、

`AggregateMirrorGap_X = 0 ↔ δ = 0`

まで source-derived に閉じるかを監査する。

### Firewall

これは amplitude mass の theorem であり、CS38 の signed Mellin-weighted scalar mismatch とはまだ別物。

---

## 8. CFZP-004 — interaction observable への polarization

CS37 / CS38 の finite-PHZ mirror rate は線形 observable である。

一方 `MirrorGap` は二次 observable。

従って

`SymmetricEulerRate = MirrorGap`

のような直接同一視は禁止する。

必要なのは既存 ThreeElement / CF2D polarization を介した

```text
quadratic Big
↔ plus/minus whole
↔ interaction Beam
↔ linear projected source
```

の exact bridge である。

この段階で、既存 CS25 の common-carrier cancellation と CS17/18 の plus/minus polarization を再利用する。

目標は「finite PHZ mirror channel がどの interaction Beam の射影なのか」を同じ object 上で確定すること。

---

## 9. CFZP-005 — Mellin weight を含む projection

次に actual Mellin weight を導入する。

ここで初めて CS38 の

`TopZetaMismatchScalar = (1/π) * orientedHalfIntegral(MirrorScalarDensity)`

へ接続する。

projection `Π` は概念的に

```text
finite cosmic mode ledger
  ↓ common carrier / cycle transport
finite PHZ mirror rate
  ↓ Mellin weight
mirror scalar density
  ↓ oriented half integral
TopZetaMismatchScalar
```

となる。

各矢印を theorem とし、定義上の rename だけで済ませない。

特に orientation、係数 `2`、`π`、共役、mirror reflection の符号は Lean に決定させる。

---

## 10. CFZP-006 — Big の source projection

Gap だけを projection しない。

同じ `Π` で Big / Body / Gap の三つを運ぶ。

目標形：

```text
Π(Big_cosmic)  = SourceBig
Π(Body_cosmic) = SourceBody
Π(Gap_cosmic)  = SourceGap
```

かつ

`SourceBig = SourceBody + SourceGap`。

ここで初めて既存 CS30 rectangle ledger と比較する。

### 最重要監査

もし

`SourceBig = RectangleBackground`

`SourceBody = TopZetaMismatchScalar`

が exact に出るなら、

`SourceGap = RectangleBackground - TopZetaMismatchScalar`

が theorem として得られる。

その場合に限り、過去の rectangle frontier を completion Gap と再解釈する。

逆に一致しないなら、違う Big / Body を探す。Gap の名前を合わせるために source を変形しない。

---

## 11. CFZP-007 — finite completion と limit closure を分離する

もし rectangle difference が genuine nonnegative Gap と同定された場合、有限段階でその Gap を負にしようとしない。

frontier を二段へ分割する。

### Finite completion

`SourceBig = SourceBody + SourceGap`

`0 ≤ SourceGap`。

### Limit closure

source-derived な limit において

`SourceGap → 0`。

この二段階を混同しない。

特に `finite Gap > 0` と `Gap → 0` は矛盾ではない。

同じ有限 object を zero/nonzero に強制する theorem がない限り collision を主張しない。

---

## 12. CFZP-008 — completed zeta への projection

finite source identity が閉じてから completed zeta へ接続する。

再利用する既存経路：

```text
finite Euler-renormalized zeta residual
→ residual negLogDeriv
→ mirror paired residual
→ completed-zeta functional-equation factorization
→ branch-free paired rate
```

このフェーズでは CS30〜CS38 の theorem を projection target として使う。

新しい infinite Euler product を導入しない。

functional equation を再証明しない。

---

## 13. CFZP-009 — standard zeta との same-observable bridge

最終目標は「似ている」ではなく同一 observable theorem である。

理想的な最終 surface は概念的に

```text
CosmicBig(s)
  ↔ CFBRC finite Big(s)
  ↔ completed-zeta Big(s)

CosmicGap(s)
  ↔ CFBRC finite Gap(s)
  ↔ zeta / completed-zeta source defect(s)
```

となる。

必要なら最後に Mathlib `riemannZeta` へ展開する。

ここでも zero-set equality だけで量の同一性を代用しない。

---

## 14. `1/2` の位置づけ

このフェーズで `1/2` は結論として先に置かない。

まず mirror involution の centered coordinate

`δ(s) := Re(s) - 1/2`

を使う。

既存 mode Gap は

`MirrorGapAt_n(s) = 0 ↔ δ(s) = 0`

を与える。

したがって `1/2` は

```text
mirror amplitude Big の completion Gap が消える唯一の実座標
```

として source-derived に現れる。

さらに宇宙式の balanced quadratic witness

`x = u = 1/2`

では primitive kernels

`x^2 = x*u = u^2 = 1/4`

となる。

ただし、この balanced witness と zeta zero location を同一視する theorem はまだ存在しない。

接続は projection theorem が得られた後にのみ主張する。

---

## 15. 旧 prime-side phase の位置づけ

`wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1` で得た CS1〜CS38 は廃棄しない。

それらは新フェーズでは

```text
projection target / audit oracle
```

として扱う。

特に再利用するもの：

- finite PHZ / prime-power source;
- CF2D polarization;
- common-carrier interaction cancellation;
- finite holomorphic potential;
- finite rectangle telescope;
- finite Euler-renormalized zeta residual;
- phase/amplitude polar transport;
- mirror-paired half interval;
- completed-zeta functional-equation fold;
- branch-free paired rate;
- mirror-weighted source recovery;
- Core–Beam–Gap amendment;
- `PrimeMirrorOffsetCore`。

これまでの解析は「RH を直接閉じるための一本道」から、

```text
宇宙式 source を ζ へ射影したときに
同じ observable が現れることを検証する target library
```

へ役割を変える。

---

## 16. 成功判定

### Green

- Big を宇宙式 source から構成。
- Gap を Big から exact に回収。
- prime-mirror / finite PHZ / Mellin source へ exact projection。
- 既存 rectangle または completed-zeta source と same-observable equality を証明。

### Green-B

- mode / finite aggregate / polarization projection までは exact。
- rectangle / zeta source との final same-observable bridge が未完成。

### Yellow

- `Background - Mismatch` を単に Gap と rename。
- desired projection equality を structure field / provider として仮定。
- zero-set equality だけから量の equality を主張。

### Red

- zero-side fixed defect / RH-equivalent theorem を prime-side Gap provider に使用。
- `Complex.arg` / global complex-log branch を本質 bridge として導入。
- infinite Euler product や limit exchange を未証明で使用。
- `MirrorGap = 0 ↔ Re(s)=1/2` だけから RH を結論。
- finite positive Gap と vanishing limit を矛盾扱い。

---

## 17. 最初の実装順

1. `develop` 上の `CoreBeamGap`, `ThreeElement`, `PrimeMirrorOffsetCore` をそのまま import する。
2. prime-power natural label の complex mode を common radial carrier / mirror amplitude / cycle state に exact factorization する。
3. mirror amplitude Gap を Big から subtraction で回収する API を整える。
4. `δ^2` から mirror amplitude Gap への analytic PowerGapBeam factorization を試す。
5. von Mangoldt positive weight による finite aggregate Big / Body / Gap を作る。
6. ThreeElement polarization により quadratic aggregate と finite-PHZ interaction observable を接続する。
7. CS38 Mellin-weighted mirror densityまで projection を運ぶ。
8. Big / Body / Gap の三つを同時に rectangle ledger へ比較する。
9. genuine source Gap が見つかった場合のみ finite completion / limit closure を分離する。
10. completed-zeta、最後に standard zeta へ same-observable bridge を閉じる。

---

## 18. このフェーズの中心命題

最初から RH を証明しようとしない。

まず次を Lean に問う。

```text
宇宙式で構成した Big から回収される Gap は、
prime-mirror mode、finite von Mangoldt source、Mellin-weighted rectangle observable、
completed-zeta / standard-zeta sourceへ射影しても同じ Gap なのか？
```

この問いが exact に Yes となった地点で、CFBRC はリーマンゼータ関数の説明模型ではなく、同じ source observable を別の代数座標で表す体系へ昇格する。

## 19. CFZP-006Z closeout / CFZP-007 re-steering

CFZP-006Z までに、interaction chain と phase-cell localization は有限・条件付きの exact API として閉じた。rectangle completion remainder は signed のままであり、source ray 側の minus whole は nonnegative だが、両者の差は common-baseline defect

`D_X = G_0 - C_X`

として残る。現在の exact relation は

`π * CompletionRemainder_X = Eminus_X + D_X`。

したがって CFZP-006 の original exit condition に対する stage status は Green-B とする。`D_X = 0` と amplitude-side Gap から ray-minus-whole への exact projection bridge は未解決であり、CompletionRemainder を無条件に genuine SourceGap と同一視しない。

CFZP-007 は limit closure へ直行せず、まず次の二つへ再誘導する。

1. common-baseline alignment `D_X = 0` の finite/canonical surface audit。
2. amplitude Gap から source ray minus whole への exact projection bridge。

この二つが閉じた場合にのみ、finite completion と limit closure を再開する。

CFZP-007 は prime-power event monotonicity を追わず、OOL-KND の drift-free carrier 候補を completed-zeta の `Gammaℝ` critical-line factor から branch-free に同定する段階へ再誘導する。critical-line の `s(t) / 2 = 1/4 + i t/2`、unit GammaR carrier、critical-line completed-zeta の realness、Hardy carrier、および Archimedean phase-rate を exact API として追加する。006 の common-baseline alignment と amplitude-Gap/ray-minus bridge は backlog のまま保持する。

007 Green 後は、OOL の旧 phase convention を比較する normalization audit へ進むか、006 backlog へ戻るかを改めて判定する。

CFZP-007 は Green-A とする。critical-line `Gammaℝ` unit carrier、Hardy real carrier、および Archimedean phase-rate は exact に同定された。

CFZP-008 では、零でない critical-line zeta の unit carrier を `HardySign × conj(GammaR unit)` に exact 分解し、二乗によって Hardy sign を消去した projective doubled-phase carrier equality を閉じた。これは branch-free に歴史的 OOL の doubled-phase 規約を正規化する。

008 の real angle lift、unwrapped phase、zero-crossing jump ledger は未解決のまま `Cfzp008RealAngleLiftAndZeroJumpLedgerGap` に境界化する。`Complex.arg`、global `Complex.log`、zero-counting identification、RH、006 の common-baseline / amplitude-source projection backlog は導入・解決しない。

008 終了後は、projective carrier を 006 の source bridge に接続できるかを大局監査する。接続しない場合は phase investigation を closeout し、006 backlog へ戻る。

CFZP-008 Green-A closeout: projective doubled-phase / OOL normalization は branch-free に exact 化され、phase investigation は一旦完了した。

CFZP-009 では、common-baseline defect を universal finite identity ではなく polarized whole-mass baseline reach problem として再分類した。`C_X = (Eplus_X + Eminus_X) / 2`、`D_X = G_0 - C_X`、cutoff-zero の `C_0 = 0` と `D_0 = G_0`、および finite reach predicate の同値を exact に固定した。

009 は finite reach の存在、common-energy の monotonicity、cofinal limit、source projection bridge を主張しない。残る frontier は finite/cofinal reach provider と amplitude-side Gap から source ray-minus whole への exact projection である。

## 20. CFZP-0034 — critical-line zeta angular velocity / phase-rate amendment

CFZP-0034 は CFZP-009 を再オープンせず、0031–0032 の critical-line phase toolkit に不足していた局所位相速度を補完した。`cfzpComplexAngularVelocity` により、複素状態と速度の branch-free Cartesian observable を定義し、非零状態では `Im(dz / z)` との exact identity を固定した。

critical-line zeta path については、複素 chain rule と実スカラーの Fréchet 微分を用いて `Re`/`Im` の実微分を exact に得た。したがって Gate D まで、OOL の Cartesian phase-velocity surface、`Re(ζ'/ζ)`、および `-Re(pascalXiOrdinaryZetaNegLogDeriv)` の一致が Green である。

completed-zeta の real-path derivative transportから `cfzpRiemannSiegelPhaseRate` への最終 balance は、0035 で exact に閉じた。`Complex.arg`、global `Complex.log`、zero-counting、RH、および 006 の common-baseline / amplitude-source projection backlog は導入・解決しない。

0034 完了後は phase investigation を拡張せず、CFZP-009 で残した finite/cofinal reach provider と amplitude-side Gap から source ray-minus-whole への exact projection backlog へ戻る。

## 21. CFZP-0035 — critical-line completed-zeta angular balance amendment

CFZP-0035 は 0034 で残した completed-zeta angular balance の一穴を閉じた。`cfzpCriticalLineCompletedProductPath` を `ζ(s(t)) * Gammaℝ(s(t))` として定義し、0031 の completed-zeta critical-line realness と factorization により、全ての `t` でその虚部が零であることを exact に固定した。

さらに zeta path と `Gammaℝ` path を実パラメータで微分し、product rule と `imCLM` を通して
`Re(ζ'(s) * Gammaℝ(s) + ζ(s) * Gammaℝ'(s)) = 0` を得た。非零 zeta point では completed product の実値性・非零性を用いて
`Re(ζ'/ζ) + Re(logDeriv Gammaℝ) = 0` を exact に証明し、0034 の angular velocity と 0031 の `cfzpRiemannSiegelPhaseRate` を接続した。

0035 により `cfzpCriticalLineZetaAngularVelocity_eq_neg_riemannSiegelPhaseRate` が Green となった。0031〜0035 の critical-line phase toolkit は GammaR carrier、Hardy/projective normalization、Cartesian angular velocity、および zeta/GammaR phase-rate balance まで閉じたため、以後は CFZP-009 の source-side backlogへ戻る。

## 22. CFZP-010 — amplitude-Gap / ray-minus observable-shape audit

CFZP-010 は、CFZP-009 で残った amplitude-side Gap と source-side
ray-minus whole の直接 projection を、まず observable shape の exact audit
として再分類した。amplitude 側は same-height mirror-mode difference の
modewise `normSq` を足し上げる diagonal Gap ledger であり、source 側は各
prime の有限 complex geometric ray を先に和として作ってから
`normSq (Z - 1)` を取る。後者は baseline `1` と signed interaction に加え、
一般には ordered Gram/interference cross terms を含む。

したがって 010 の Green-A は、direct
`amplitude-Gap = ray-minus-whole` は現在の有限代数からは正当化されず、
成立し得る bridge は次の三層を同時に輸送する必要がある、という exact
classification である。

1. mirror amplitude mode から source geometric mode への transform。
2. finite Gram/interference ledger の transport。
3. source baseline `1` と interaction normalization。

有限 Gram 恒等式と二つの等しい mode による反例により、
`normSq (sum modes) = sum normSq(modes)` を無条件には使えないことも固定した。
新しい `Cfzp010AmplitudeGapToRayMinusSameObservableBridgeGap` はこの三層
bridge が未提供であることを明示する。0035 までの critical-line phase
toolkit は再オープンしない。

010 後の source-side frontier は、次の二つに整理される。

1. common-baseline の finite/cofinal reach provider。
2. mode-transform + interference + normalization bridge。

いずれも 010 の結果だけでは証明済みとしない。また、finite shape audit
から infinite cutoff exchange、RH、または amplitude Gap と ray-minus の
rename equality は導入しない。

## 23. CFZP-011 — same-height mirror/source mode-transform audit

CFZP-011 は CFZP-010 の三層 bridge のうち Layer 1 だけを閉じた。
既存の finite source summand を `weight(t) * q^(-sR(t))` として明示し、
同じ height を保った `criticalMirror(sR(t))` の mirror summand を追加した。
その結果、各 prime-power mode について

```text
mirrorSourceSummand - rightSourceSummand
  = MellinWeight * sameHeightMirrorModeDifference
```

が exact になった。さらに modewise `normSq` では Mellin weight の
`normSq` factor を残したまま、既存の mirror carrier / primeMirrorOffsetGap
へ展開できることを固定した。weight を無条件に 1 とする同一視は行わない。

既存 exponent support 上の finite same-height mirror ray についても、right
ray との差を weighted same-height mode-difference の有限和として exact に
再構成した。最後に

```text
ZR - 1 = (ZR - ZM) + (ZM - 1)
```

およびその `normSq` 展開を証明し、ray-minus の未解決部分を mirror baseline
residual `ZM - 1` と、transformed amplitude part との interference に局在化
した。

したがって 011 の分類は Green-A とする。

```text
Layer 1: CLOSED
  mirror amplitude mode -> Mellin-weighted same-height source pair

Layer 2: OPEN
  weighted modewise diagonal -> finite Gram/interference transport

Layer 3: SHARPENED
  ray-minus -> mirror baseline residual + its interference
```

残る marker は `Cfzp011MirrorBaselineResidualAndInterferenceBridgeGap` とし、
mirror baseline residual の collapse や aggregate weighted Gram transportを
証明済みとは扱わない。finite shape と algebraic decomposition の範囲を越えて
common-baseline reach、無限極限、RH、または amplitude Gap と ray-minus の
直接 equality は導入しない。

## 24. CFZP-012 — mirror-baseline functional-reflection height-reversal audit

CFZP-012 は、0037 で残った mirror baseline residual
`Z_M - 1` を、既存の functional-reflection channel と right-edge height
reversal の有限 exact surfaceへ分類した。right edge
`s_R(t) = σ + i t` について、critical mirror は

```text
criticalMirror(s_R(t)) = 1 - s_R(-t)
```

となることを証明した。この座標 identity により、same-height mirror mode
は height-reversed functional-reflection mode と、
`q^(-s_R(-t)) - q^(-s_R(t))` の vertical displacement に分解される。

この分解を Mellin-weighted source summand と既存 exponent support 上の
finite rayへ持ち上げ、

```text
Z_M = functionalReflectionPart + reweightedReversedRightRay
Z_M - 1 = functionalReflectionPart
        + (reweightedReversedRightRay - 1)
```

を exact に固定した。ここで current-time Mellin weight は保持され、
`weight(t) = weight(-t)` や `weight(-t) = conj(weight(t))` は仮定していない。

さらに reweighted reversed-right ray と actual right ray at `-t` の差を、
有限和の explicit weight-reversal correction として表現した。従って 012 の
classification は Green-A とする。

```text
CFZP-011 Layer 1: CLOSED
CFZP-012 mirror baseline identity: CLASSIFIED
Layer 2 weighted Gram/interference: OPEN
common-baseline finite/cofinal reach: OPEN
```

weight reversal / conjugation の provider は
`Cfzp012WeightReversalConjugationGap` として残した。したがって 012 は
baseline collapse、common-energy defect との rename equality、無限 cutoff
交換、RH を主張しない。次の判断は、explicit correction を既存 completed
source geometryへ接続するか、Layer 2 の finite weighted Gram/interference
transportへ戻るかである。

## 25. CFZP-013 — weight-reversal conjugation and ray self-recurrence audit

CFZP-013 は CFZP-012 で残した weight-reversal correction を有限 exact に
監査した。`τ = 0` の Mellin weight について、既存の quadratic-weight と
log-average の共役則を再利用し、

```text
weight(conj z) = conj(weight z)
weight(node(-t)) = conj(weight(node(t)))
```

を証明した。また positive natural prime-power mode について

```text
q^(-s_R(-t)) = conj(q^(-s_R(t)))
```

を exact に固定した。これらを掛け合わせ、source summand と finite right
ray の height-reversal conjugation

```text
Z_R(-t) = conj(Z_R(t))
```

を閉じた。

CFZP-012 の reweighted reversed-right correction は、weight skew

```text
skew(t) = weight(t) - conj(weight(t))
```

と有限 bare reversed-mode sum の積に rewrite した。skew は
`conj(skew) = -skew`、`Re(skew) = 0`、および `2 * I * Im(weight)` の形を
持つが、skew の消滅は主張していない。

従って mirror baseline residual は exact に

```text
functionalReflectionPart
+ (conj(Z_R(t)) - 1)
+ skewCorrection(t)
```

へ再分解された。さらに
`normSq(conj(Z_R(t)) - 1) = normSq(Z_R(t) - 1)` を証明した。ただし
functional-reflection contribution、skew correction、および interference
を含むため、`normSq(Z_M - 1) = normSq(Z_R - 1)` や baseline collapse は導かない。

013 の Green-A classification は次の通り。

```text
CFZP-012 weight-reversal classification:
  conjugation law: CLOSED
  actual right-ray height reversal: CLOSED
  weight mismatch: IDENTIFIED as pure-imaginary skew correction

mirror baseline residual:
  functional-reflection contribution
  + conjugate copy of the original right-ray residual
  + explicit skew correction
```

残る marker は `Cfzp013FunctionalReflectionSkewInterferenceClosureGap` とし、
direct baseline collapse、amplitude Gap との equality、無限 cutoff、RH は導入
しない。次段階は Layer 2 の finite weighted Gram/interference transport、
common-baseline reach、または既存 CS37/CS38 aggregate channel への有限 transport
のいずれかを選択する。

0040 の reinforcement では、Gate B の positive prime-power conjugation proof を
`Complex.cpow_def_of_ne_zero` と `Complex.natCast_log` による explicit exponential
routeへ置換した。positive natural base の非零性だけを使い、theorem statement、
downstream self-recurrence surface、および 013 の Green-A classification は維持する。

## 26. CFZP-014 — functional-reflection prime-ray canonical aggregate transport

CFZP-014 は、013 の prime ごとの functional-reflection ray contribution を
既存の Pascal prime support、`(p,k)` pair support、および canonical prime-power
supportへ有限 exact に再集約した。`log p` を明示した prime-weighted aggregateを
導入し、既存の pair-label image と injectivity を使って

```text
AggregateFunctionalReflectionPrimeRayAmplitude
  = weight(node(t)) * canonicalFunctionalReflectionSource
```

を reversed right-edge point `s_R(-t)` で証明した。さらに既存の
`cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate`
を再利用し、同じ aggregate が finite symmetric Euler rate に一致することを固定した。
`canonicalPrimePowerShadowCost q` は引き続き canonical base-prime の `log p` として
扱い、`log q` への誤同一視は行っていない。

したがって CFZP-014 の core classification は Green-A とする。

```text
functional-reflection per-prime ray -> canonical finite aggregate: CLOSED
canonical functional-reflection source -> finite symmetric Euler rate: CLOSED
reversed right-edge source -> CS38 top-edge source: OPEN
```

最後の edge relocation は既存 exact contour transport provider が未提供のため、
`Cfzp014FunctionalReflectionRightToTopEdgeTransportGap` に境界化した。top-edge
observable との rename equality、contour relocation、無限 cutoff exchange、
baseline collapse、amplitude Gap との equality、および RH は導入しない。

## 27. CFZP-015 — arithmetic radial domination margin frontier

CFZP-015 は、CFZP-014 で閉じた canonical finite source と既存の scalar surface
を接続し、有限 cutoff ごとの arithmetic radial domination margin を導入した。
margin は

```text
WholeShiftedPlusEnergy - WholeShiftedMinusEnergy
  - 4 * π * FixedRadialSecondMomentFunctional
```

と定義し、既存の shifted-energy difference と scalar Mellin excess の exact
identity から

```text
margin = -4 * π * ArithmeticDefectApproximant
```

を証明した。したがって margin の非負性は finite arithmetic defect approximant
の非正性と同値であり、同じ条件を shifted-energy gap および scalar radial
comparison の形でも読める。局所の `hε : 0 < ε` は明示的に保持した。

ordered finite radial domination は、全ての正の ε について cutoff X の atTop で
margin が eventually 非負であるという命題
`Cfzp015OrderedFiniteRadialDomination` として公開した。ただし、その命題の
inhabitant や独立した eventual provider は導入していない。もしこの provider を
別途仮定すれば、既存の ordered-limit transport により endpoint defect の非正性、
fixed defect の非正性を得られる。さらに fixed second-moment defect の安全半径
上の非負性と zero iff を合わせると fixed defect は零となり、finite window の
criticality を得る。

この段階の classification は Green-A とする。

```text
finite arithmetic radial margin identity: CLOSED
margin sign <-> finite defect sign: CLOSED
ordered finite radial domination proposition: CLOSED as a conditional interface
independent eventual domination provider: OPEN / GAP
```

従って、この実装は global provider、極限交換、source completion、baseline collapse
または global RH を主張しない。CFZP-014 の right-edge から top-edge への relocation
gap と common-baseline reach も引き続き未解決の frontier として保持する。

## 28. CFZP-016 — cofinal radial-domination frontier minimization

CFZP-016 は、CFZP-015 の eventual finite radial domination provider を、現在の
ordered-limit route で十分な、より弱い二重 cofinal sign condition へ縮小した。
まず CFZP-015 の finite margin の endpoint と fixed limit を first-class に定義し、
既存の arithmetic defect convergence と定数倍の Tendsto だけから

```text
M_X(ε,W) -> EndpointMargin(ε,W)
EndpointMargin(ε,W) -> FixedMargin(W)  as ε -> 0+
```

を exact に transport した。`Frequently (0 ≤ f x)` と実数 Tendsto から
`0 ≤ limit` を得る局所補題も追加し、fixed `ε` について cofinally many cutoff
margin の非負性が endpoint margin の非負性を強制することを閉じた。

さらに
`Cfzp016DoublyCofinalRadialDomination W` を、`𝓝[>] 0` で cofinally many の正の
`ε` が fixed-`ε` cutoff cofinal domination を持つ命題として定義した。この条件から
fixed margin の非負性、fixed arithmetic defect の非正性、safe-radius nonnegativity
との組み合わせによる fixed defect の零性、および有限 zero window の criticality
を得る。CFZP-015 の stronger eventual provider からこの doubly-cofinal provider
への implication も hierarchy adapter として閉じた。

この段階の classification は Green-A とする。

```text
finite margin -> endpoint margin -> fixed margin: CLOSED
frequently nonnegative + convergence -> nonnegative limit: CLOSED
fixed-ε cofinal cutoff domination -> endpoint sign: CLOSED
double cofinal radial domination -> finite-window criticality: CLOSED conditionally
CFZP-015 eventual provider -> CFZP-016 cofinal provider: CLOSED
independent doubly-cofinal provider: OPEN / GAP
```

従って「minimal」は絶対的な論理最小性ではなく、現行 ordered-limit route に対する
strictly weakened / sharpened sufficient frontier を意味する。phase-cell coverage、
prime-power arithmetic coverage、equidistribution、zero counting などを provider と
して仮定していない。joint `(ε,X)` limit、limit exchange、unconditional margin sign、
contour relocation、common-baseline reach、global RH も導入しない。

## 29. CFZP-017 — radial-margin prime-threshold decomposition

CFZP-017 は、CFZP-015 の finite radial margin を、`X` に依存しない background
threshold と normalized prime contribution の excess に分解した。threshold は

```text
FixedRadialSecondMomentFunctional
  - NormalizedArchimedeanContribution
  - NormalizedElementaryContribution
  - NormalizedTopContribution
```

で定義し、既存の four-term normalized arithmetic decomposition と scalar-surface
identity から

```text
WholeShiftedRadialMargin
  = 4 * π * (NormalizedPrimeContribution - NormalizedPrimeThreshold)
```

を有限 exact に証明した。従って margin の非負性は prime contribution が
threshold を越えることと同値である。

さらに既存の CS25 API により、同じ crossing を

```text
π * NormalizedPrimeThreshold ≤ AggregateRayInteractionEnergy
```

および `2 *` von Mangoldt finite mode sum の形へ transport した。CFZP-016 の
fixed-ε cofinal radial domination と cofinal prime-threshold crossing は同値であり、
外側の `ε → 0+` cofinality を含む doubly-cofinal provider も同値になる。そのため
CFZP-016 の finite-window criticality を threshold-crossing provider から再公開した。

sign-only route と magnitude route は明示的に分離した。threshold が非正なら
prime contribution の非負性で margin 非負性を得られるが、正の threshold に対して
prime contribution の非負性だけでは不十分であることを実数 countermodel で固定した。
したがって CFZP-006W/006Y の pointwise phase-cell sign を integrated threshold
crossing へ rename していない。

この段階の classification は Green-A とする。

```text
radial margin -> prime/background threshold decomposition: CLOSED
threshold crossing -> aggregate interaction/mode sum: CLOSED
cofinal radial domination <-> cofinal prime-threshold crossing: CLOSED
independent doubly-cofinal threshold-crossing provider: OPEN / GAP
phase-cell sign -> integrated threshold crossing: OPEN analytic route
```

phase-cell coverage、equidistribution、threshold-crossing provider、joint limit、
limit exchange、pointwise/integrated rename equality、common-baseline reach、global RH
は導入しない。

## 30. CFZP-018 — prime-threshold approximate-reach frontier

CFZP-018 は、CFZP-017 の normalized prime threshold を既存 CS24 correction source
へ戻し、さらに zero-cutoff radial contact deficit と同一化した。有限 exact に

```text
Threshold = FixedRadialSecondMomentFunctional - IndependentCorrectionSourceReal
π * Threshold = ZeroCutoffRadialContactDeficit
```

を証明した。これにより CFZP-017 の finite margin は CS22 の radial-contact
coordinates で

```text
WholeShiftedRadialMargin = -4 * FiniteRadialContactDeficit
```

となり、exact prime-threshold crossing は finite radial deficit の nonpositive
crossing と同値になる。さらに CS25 の aggregate interaction identity により、
threshold crossing は zero-cutoff deficit 以下の aggregate interaction reach として
も読める。

次に exact crossing を、任意の正の normalized slack `δ` と任意に大きい cutoff `N`
に対し

```text
Threshold - δ ≤ NormalizedPrimeContribution(ε,W,X)
```

を満たす `X ≥ N` が存在するという `Cfzp018CofinalPrimeThresholdApproximateReachAt`
へ弱めた。この条件と既存 CS22 の
`PascalCenteredXiPrimeSideCofinalRadialContactZeroAt` は、`η = π * δ` の正の
スケール変換を通じて exact に同値である。従って fixed-ε endpoint defect の非正性、
outer `ε → 0+` の doubly-cofinal approximate reach、safe-radius nonnegativity、
finite-window criticality までを条件付きに再公開した。

CFZP-017 の doubly-cofinal exact crossing は CFZP-018 の approximate reach を含意
するが、逆 implication は主張しない。pointwise の positive slack が exact crossing
を含意しない実数 countermodel も置き、三つの frontier を分離した。

```text
π * normalized threshold = zero-cutoff radial deficit: CLOSED
whole shifted margin = -4 * finite radial deficit: CLOSED
exact crossing = finite deficit zero-crossing: CLOSED
approximate reach <-> CS22 cofinal radial contact zero: CLOSED
017 exact crossing -> 018 approximate reach: CLOSED
independent doubly-cofinal approximate-reach provider: OPEN / GAP
phase-cell sign -> approximate magnitude reach: OPEN analytic route
```

phase-cell sign、phase equidistribution、exact/approximate provider existence、joint
limit、limit exchange、contour relocation、common-baseline reach、global RH は導入しない。

## 31. CFZP-019 — branch-free prime-power signed-mass budget

CFZP-019 は、CFZP-006V/006Y の既存 branch-free prime-power event を同じ canonical
pair support 上で正質量と負債へ分解した。各 event について

```text
event = positiveMass(event) - negativeDebt(event)
```

を `max` による canonical algebraic identity として証明し、有限 ledger を

```text
branchFreeTrigLedger
  = positiveEventMass - negativeEventDebt
```

へ exact に展開した。safe-frequency regime `0 < ε < log 2` では既存 radial-deficit
identity と合成して

```text
finiteRadialContactDeficit
  = zeroCutoffBaseline + negativeEventDebt - positiveEventMass
```

を得た。従って任意の geometric slack `η > 0` について

```text
finiteRadialContactDeficit ≤ η
  ↔ zeroCutoffBaseline + negativeEventDebt
       ≤ positiveEventMass + η
```

である。

006Y の既存 phase-cell sign theorem は local adapter として再利用し、nonnegative
event では debt が消え、nonpositive event では positive mass が消えることを証明した。
有限 support 全体の sign-only 仮定から debt が消えることも閉じたが、非負 mass だけでは
固定 baseline を arbitrary slack まで支払えない実数 firewall を併記した。

safe-frequency restriction は `Real.log 2 > 0` により outer `ε → 0+` で eventually
成立する。したがって doubly-cofinal safe signed-mass budget は CFZP-018 の
approximate-reach frontier と exact に同値であり、既存 finite-window criticality へ
は条件付き adapter を与えた。

この段階の classification は Green-A とする。

```text
one-event positive/negative decomposition: CLOSED
branch-free ledger = positive mass - negative debt: CLOSED
finite radial deficit = baseline + debt - positive mass: CLOSED
slack radial contact <-> signed-mass budget: CLOSED
safe fixed-ε signed-mass budget <-> CFZP-018 approximate reach: CLOSED
safe-frequency restriction near ε -> 0+: NO STRENGTH COST
006Y local phase-cell sign -> local mass/debt elimination: CLOSED
local sign -> global signed-mass budget: OPEN / NOT INFERRED
independent doubly-cofinal signed-mass budget provider: OPEN / GAP
```

positive/debt の個別 cutoff monotonicity・increment theorem は既存 public API に無いため
本段では追加せず、次段の監査対象として残す。phase equidistribution、universal
phase-cell coverage、budget provider、joint limit、limit exchange、global RH は導入しない。

## 32. CFZP-020 — signed-mass cutoff frontier increments

CFZP-020 は CFZP-019 の cumulative positive event mass / negative event debt を
canonical prime-power pair support の cutoff frontier へ分解した。membership
characterization から `X ≤ Y` に対する support inclusion を示し、`X + 1` の新規部分を

```text
frontier(X) = support(X + 1) \ support(X)
support(X + 1) = support(X) ∪ frontier(X)
```

として exact に固定した。

この disjoint partition 上で、positive mass と negative debt の one-step recurrence、
双方の nonnegativity・cutoff monotonicity、signed branch-free ledger の increment

```text
ledger(X + 1) - ledger(X)
  = frontierPositiveMass(X) - frontierNegativeDebt(X)
```

を証明した。safe-frequency regime `0 < ε < log 2` では radial contact deficit の
中心 recurrence も

```text
G_(X + 1) = G_X + frontierNegativeDebt(X) - frontierPositiveMass(X)
```

として閉じた。

さらに frontier 上の全 event sign を仮定した local-to-frontier adapter により、
nonnegative frontier では debt が消えて deficit が非増加、nonpositive frontier では
positive mass が消えて deficit が非減少となることを示した。empty frontier では mass、
debt、ledger、radial deficit が不変である。

この段階の classification は Green-A とする。

```text
pair-support cutoff monotonicity: CLOSED
one-step frontier partition: CLOSED
positive/debt one-step recurrence: CLOSED
positive/debt cutoff monotonicity: CLOSED
signed ledger frontier increment: CLOSED
radial deficit one-step recurrence: CLOSED
frontier event sign -> one-step deficit direction: CLOSED
frontier sign provider / quantitative dominance: OPEN / GAP
cofinal signed-mass budget provider: OPEN / GAP
```

個別 frontier sign の conditional theorem は cofinal/eventual provider ではない。frontier
events の eventual sign、net-positive dominance、cofinal signed-mass budget、phase-cell
coverage、asymptotic density、joint limit、limit exchange、finite-window criticality の
無条件化、global RH は導入しない。

## 33. CFZP-021 — von Mangoldt pulse compression

CFZP-021 は既存 CFZP-006R の signed cutoff increment を

```text
Pulse(n) = 2 * Λ(n) * FiniteModeKernel(n)
```

という public pulse observable として再公開した。finite von-Mangoldt mode sum の
`Finset.range` successor identity により

```text
Aggregate(X + 1) = Aggregate(X) + Pulse(X + 1)
```

を exact に証明した。

safe-frequency regime では既存 branch-free ledger と CFZP-020 frontier net flow を
同じ pulse に transportし、radial contact deficit について

```text
G_(X + 1) = G_X - Pulse(X + 1)
frontierPositiveMass(X) - frontierNegativeDebt(X) = Pulse(X + 1)
```

を閉じた。pulse の符号から one-step deficit direction への adapterも追加したが、
pulse 自体の符号は仮定している。

`¬ IsPrimePow (X + 1)` では `Λ(X + 1) = 0` により pulse、aggregate、ledger、radial
deficit が不変となる。frontier pair の exact natural label が `X + 1` であることを
canonical support の injectivity から証明し、prime-power witness `X + 1 = p^j` では
pulse が既存 branch-free prime-power event と一致することを閉じた。

006Y の phase-cell theorem は一つの prime-power pulse の符号と one-step deficit方向へ
のみ transportした。これは eventual sign、block dominance、cofinal reach を意味しない。

この段階の classification は Green-A とする。

```text
one-mode von Mangoldt pulse: CLOSED
aggregate one-step pulse identity: CLOSED
branch-free ledger increment = pulse: CLOSED
frontier net increment = pulse: CLOSED
radial deficit pulse recurrence: CLOSED
non-prime-power quiescence: CLOSED
prime-power pulse/event identification: CLOSED
pulse sign -> one-step deficit direction: CLOSED
phase-cell -> one-pulse sign: CONDITIONAL / CLOSED
cofinal net-positive pulse accumulation: OPEN / GAP
signed-mass budget provider: OPEN / GAP
```

`Λ(n) ≥ 0` から pulse の符号を推論せず、one-step identity から global monotonicityを
推論しない。phase equidistribution、block dominance、joint limit、limit exchange、
cofinal provider、global RH は導入しない。

## 34. CFZP-022 — finite pulse-block compensation

CFZP-022 は CFZP-021 の one-mode pulse を有限の右閉区間 `(A, B]` へ持ち上げた。
`Finset.Ioc` による pulse block について、aggregate interaction、branch-free ledger、
radial contact deficit の三つの finite telescope を exact に証明した。radial telescope
は `0 < ε` だけで閉じ、branch-free ledger だけが safe-frequency regime を要求する。
また block の one-step singleton、concatenation、additive telescope を公開した。

radial deficit の endpoint payment は

```text
G_B ≤ η ↔ G_A ≤ PulseBlock(A,B) + η
```

であり、safe-frequency regime では block を

```text
positiveEventMassBlock - negativeEventDebtBlock
```

へ書き換えた。従って終点の radial slack は、始点の deficit と finite signed pulse
block compensation の不等式と同値である。raw pulse payment contract と signed block
budget contract をそれぞれ first-class Prop とし、後者は既存 CFZP-019 signed-mass
budget、CFZP-018 approximate reach、CS22 cofinal radial-contact zero と fixed-`ε`
で exact に同一化した。

非 prime-power mode の pulse block が消える quiescence lemma と、独立の cofinal
signed block-budget provider が未導入であることを表す Gap marker も追加した。

```text
finite `(A, B]` pulse block: CLOSED
aggregate / ledger / radial finite telescope: CLOSED
one-step block and block concatenation: CLOSED
G_B ≤ η <-> G_A ≤ PulseBlock + η: CLOSED
finite pulse block = positive mass - negative debt: CLOSED
radial slack <-> finite block compensation: CLOSED
finite block compensation <-> CS22 cofinal contact zero: CLOSED
cofinal signed block budget <-> CFZP-019/018 fixed-ε interfaces: CLOSED
non-prime-power block quiescence: CLOSED
independent cofinal signed block-budget provider: OPEN / GAP
```

本段は有限和と有限不等式に限定し、block dominance、phase equidistribution、
infinite sum、joint limit、limit exchange、finite-window criticality の無条件化、
global RH は導入しない。

## 35. CFZP-023 — quantitative prime-power pulse margins

CFZP-023 は CFZP-006W/X の safe-frequency prime-power event factorization と
exact derivative API を、有限区間上の quantitative derivative hypothesis へ接続した。
centered phase-magnitude interval の幅

```text
right - left = 2 * ε
```

を first-class theorem として固定し、centered interval 上で
`Profile'(u) ≤ -κ` を仮定すると

```text
2 * ε * κ ≤ Profile(left) - Profile(right)
Event(p,j) ≥ 2 * log(p) * CriticalScale(p^j) * κ
```

を証明した。event factorization に含まれる `(2 * ε)⁻¹` と interval width の
`2 * ε` は exact に相殺される。`κ > 0` の場合の event の strict positivity も
追加した。

同じ centered interval の absolute derivative envelope `|Profile'(u)| ≤ K` から、
profile difference、event、prime-power von-Mangoldt pulse の absolute upper bound を
公開した。さらに event の quantitative credit を CFZP-019 の positive mass へ、
absolute envelope を negative debt へ transportし、prime-power pulse へ同じ bounds を
transportする adapterを追加した。

この段階の classification は Green-A とする。

```text
generic derivative-drop / absolute envelope: CLOSED
centered phase-magnitude width: CLOSED
quantitative centered profile drop: CLOSED
event width-normalization cancellation: CLOSED
strict quantitative event positivity: CLOSED
event / pulse absolute envelope: CLOSED
positive-mass / negative-debt adapters: CLOSED
prime-power pulse quantitative transport: CLOSED
independent uniform derivative-margin provider: OPEN / GAP
```

`κ` や `K` は明示的な theorem hypothesis であり、prime-power geometry からの uniform
margin provider は導入していない。phase sign から quantitative margin、eventual
positivity、block dominance、phase-cell coverage、density/equidistribution、infinite
sum、joint limit、limit exchange、finite-window criticality の無条件化、global RH は
導入しない。

## 36. CFZP-024 — certified block credit/debt dominance

CFZP-024 は CFZP-023 の one-prime-power quantitative certificate を、有限 canonical
prime-power pair block `(A, B]` へ合算した。block support を

```text
pascalPrimePowerPairSupportUpTo B \
  pascalPrimePowerPairSupportUpTo A
```

として明示し、CFZP-022 の positive mass / negative debt increment をこの support
差分上の finite sum として再表示した。任意に選んだ `Good` subset とその補集合
`Bad` の union、disjointness、subset を公開した。

`Good` 上では CFZP-023 の derivative-drop margin `κ` を合算した
`cfzp024CertifiedGoodCredit` を定義し、

```text
CertifiedGoodCredit ≤ BlockPositiveMass
```

を証明した。各 Good pair の event は nonnegative となるため、Good の negative debt
sum は exact に `0` へ消える。一方、`Bad` 上の absolute derivative envelope `K` を
合算した `cfzp024CertifiedBadDebtEnvelope` を定義し、

```text
BlockNegativeDebt ≤ CertifiedBadDebtEnvelope
```

を証明した。これらを CFZP-022 の signed block budget と合成し、独立の
`Cfzp024CertifiedBlockDominance` から終点の radial deficit `G_B ≤ η` を得る theorem
を追加した。

さらに fixed-`ε` の cofinal certified-dominance provider interface を定義し、その仮定
から CFZP-022 の signed pulse-block budget、続いて CFZP-018 approximate reach へ
一方向に transportする conditional adapterを追加した。

この段階の classification は Green-A とする。

```text
pair block-support difference: CLOSED
block mass/debt exact finite sums: CLOSED
Good/Bad finite support split: CLOSED
Good quantitative credit ≤ positive block mass: CLOSED
Good negative debt = 0: CLOSED
block negative debt ≤ Bad envelope: CLOSED
certified dominance → finite radial payment: CLOSED
cofinal certified dominance → CFZP-022/018: CONDITIONAL / CLOSED
independent certified-dominance provider: OPEN / GAP
```

certificate の `Good`、`κ`、`K` は明示的な有限データであり、これらを供給する
arithmetic/phase theoremは導入していない。phase equidistribution、density、uniform
margin、eventual positivity、automatic block dominance、infinite sum、joint limit、
limit exchange、finite-window criticality の無条件化、global RH は導入しない。

## 37. CFZP-025 — quantitative phase-core margin synthesis

CFZP-025 は CFZP-024 の Good certificate に含まれていた derivative-level margin を、
CFZP-006X/Y の dimensionless phase core から合成する spine を追加した。
centered prime-power frequency interval の右端で評価した

```text
PrefactorFloor = exp(-a * right) / right^3
```

を定義し、safe-frequency regime では正であること、interval 内の exact positive
prefactor `exp(-a*u) / u^3` がこの floor 以上であることを有限不等式として証明した。

phase-angle interval 上の
`PhaseDerivativeCore ≤ -δ` を first-class contract として定義し、angle/magnitude
endpoint identities と exact coordinate formula により frequency derivative core の
`≤ -δ` へ transportした。さらに正の prefactor と符号を明示的に管理して

```text
PhaseCore ≤ -δ
  -> Profile' ≤ -(PrefactorFloor * δ)
  -> CFZP-023 event credit
  -> prime-power pulse credit
```

を閉じた。

quantitative third-quadrant の pure real algebra theoremも追加した。`A₀`, `B₀`, `s`,
`c` の非負性、sin coefficient / trigonometric lower boundsを明示的に仮定し、

```text
PhaseDerivativeCore α θ ≤ -(A₀*s + B₀*c)
```

を証明する。phase-cell membership や bounds 自体は自動供給しない。

最後に Good pair ごとの phase-core margin `δ` から、explicit prefactor floor による
`κ = PrefactorFloor * δ` を持つ CFZP-024 finite certificate を構成する constructor
を追加した。Bad 側の envelope dataは従来どおり明示的仮定である。

この段階の classification は Green-A とする。

```text
centered derivative prefactor floor: CLOSED
phase-core quantitative margin interface: CLOSED
phase-core -> derivative-core transport: CLOSED
phase-core margin -> CFZP-023 derivative margin: CLOSED
phase-core margin -> event/pulse credit: CLOSED
quantitative third-quadrant algebra: CLOSED
phase-core Good-data -> CFZP-024 certificate: CLOSED
independent quantitative phase-cell coverage provider: OPEN / GAP
```

prime-power phase centersの good-cell membership、density/equidistribution、uniform
positive `δ`/`κ`、cofinal certified dominance、CFZP-018 provider、joint limit、limit
exchange、finite-window criticality の無条件化、global RH は導入しない。

## 38. CFZP-026 — periodic third-quadrant phase-cell certificate

CFZP-026 は CFZP-025 の abstract な phase-core margin を、周期的な第三象限の
trimmed cell に対する有限 containment から構成する API を追加した。
`k : ℕ` と `0 < τ ≤ π/4` に対して

```text
left  = π + 2πk + τ
right = 3π/2 + 2πk - τ
```

を first-class endpoint とし、セル内の角度について periodicity と monotonicity
から

```text
sin θ ≤ -sin τ
cos θ ≤ -sin τ
```

を純粋な実数・三角関数の補題として証明した。prime-power centered angle interval
の cell containment、center/half-width 形式、さらに

```text
left + T*ε ≤ T * (j * log p)
T * (j * log p) + T*ε ≤ right
```

という explicit arithmetic hit 形式の同値 adapterも公開した。

cell の endpoint coefficient floors `A₀`, `B₀` を定義し、`0 ≤ aspectRatio ≤ 1`、
`0 ≤ A₀` のもとで `δ = (A₀ + B₀) * sin τ` 型の phase-core margin を構成する。
この margin は CFZP-025 の prefactor floor、CFZP-023 の event/pulse credit、
CFZP-024 の finite Good certificate constructorへ直接 transportされる。
Good pair ごとの `k`、`τ`、cell containment と Bad 側 envelope を入力する
`cfzp026FiniteBlockCertificate_of_periodicThirdQuadrantCellHits` も追加した。

この段階の classification は Green-A とする。

```text
periodic third-quadrant cell geometry: CLOSED
cell membership -> quantitative sin/cos margins: CLOSED
prime-power centered interval containment: CLOSED
containment <-> explicit T*j*log(p) inequalities: CLOSED
phase coefficient endpoint floors: CLOSED
cell containment -> explicit phase-core δ: CLOSED
cell certificate -> event/pulse quantitative credit: CLOSED
periodic-cell Good data -> CFZP-024 certificate constructor: CLOSED
cofinal quantitative third-quadrant hit provider: OPEN / GAP
```

全 prime-power pair の Good-cell membership、任意 block の Good pair 存在、density/
equidistribution、`j * log p` の無条件稠密性、uniform positive `τ`/`δ`/`κ`、automatic
cofinal dominance、CFZP-018 provider、infinite sum、joint limit、limit exchange、
finite-window criticality の無条件化、global RH は導入しない。

## 39. CFZP-027 — subcritical large-cell coefficient readiness

CFZP-027 は CFZP-026 に残っていた Good pair ごとの
`0 ≤ PhaseSinCoeffFloor α L R` 入力を、subcritical aspect ratio と explicit
large-cell readiness contract から自動生成する API を追加した。

`Cfzp027SubcriticalPhaseAspect W` は
`cfzpModePhaseAspectRatio W < 1` を first-class にし、`0 < 1 - α^2`、および
`α < 1 ↔ cfzpModePhaseAbscissa W < W.rectangle.T` を証明する。さらに trim `τ`
を外した第三象限 cell の coefficient floor を定義し、`0 ≤ τ` の下で

```text
UntrimmedFloor α k ≤ TrimmedFloor α k τ
```

を exact finite algebra として閉じた。

ready contract は

```text
4 ≤ (1 - α^2) * (2πk)
3π + 2 ≤ 2 * (2πk)
```

という有限不等式であり、これから untrimmed floor、続いて任意の trimmed cell
floor の非負性を構成する。`Tendsto Nat.cast atTop atTop` と正の定数倍だけを用いて、
subcritical `α` では ready cell index が任意の finite cutoff より上に存在することも
証明した。これは phase hit や density を仮定・証明するものではない。

center target の width

```text
π/2 - 2τ - 2*T*ε
```

と、target interior の同値条件 `τ + T*ε < π/4` を first-class にした。
`Cfzp027PrimePowerReadyThirdQuadrantHit` は arithmetic hit と readiness を束ね、
CFZP-026 の containment、explicit positive phase-core margin、event/pulse credit
へ接続する。さらに per-pair `hA` を要求しない CFZP-024 certificate constructor
を追加した。

この段階の classification は Green-A とする。

```text
subcritical aspect gap positivity: CLOSED
subcritical aspect <-> a<T adapter: CLOSED
untrimmed floor is worst trimmed floor: CLOSED
explicit large-cell readiness -> A0≥0: CLOSED
cofinally large cells are ready: CLOSED
center target exact width: CLOSED
target interior condition: CLOSED
ready arithmetic hit -> CFZP-026 hA: CLOSED
ready hit -> event/pulse credit: CLOSED
ready-hit Good data -> CFZP-024 certificate: CLOSED
cofinal ready phase-hit provider: OPEN / GAP
```

`cfzpModePhaseAspectRatio W < 1` 自体の全 window での成立、prime-power phase hit、
`T * log p / (2π)` の irrationality、density/equidistribution、automatic Bad debt
control、automatic cofinal dominance、CFZP-018 provider、infinite sum、joint limit、
limit exchange、finite-window criticality の無条件化、global RH は導入しない。

## 40. CFZP-028 — additive-circle irrational rotation and cofinal phase hits

CFZP-028 は固定 prime `p` の一指数 phase increment

```text
T * log p
```

を `AddCircle (2π)` の first-class rotation step として定義した。
`Irrational ((T * log p) / (2π))` から、Mathlib の additive-circle
irrational-rotation theorem と compact-group の integer/natural orbit bridge を
用いて natural multiples の dense orbit を得る。さらに任意 cutoff より後の
natural hit を、target の逆平行移動で構成し、`AddCircle.openPartialHomeomorphCoe`
の fundamental chart を通じて実数 representative と natural periodic cell index
へ lift した。

first-period target は

```text
π + τ + T*ε < residue < 3π/2 - τ - T*ε
```

であり、CFZP-027 の target interior から open/nonempty target と
`Cfzp026PrimePowerQuantitativeThirdQuadrantHit` への exact adapter を閉じた。
phase center の正の線形成長を使い、cell index cutoff と CFZP-027 の readiness
threshold の最大値以上を選ぶことで、次を conditional に閉じた。

```text
irrational fixed-prime rotation
  -> dense natural AddCircle orbit
  -> arbitrarily late target hits
  -> cofinal periodic cell indices
  -> Cfzp027PrimePowerReadyThirdQuadrantHit
  -> Cfzp027CofinalReadyThirdQuadrantHitsForPrime
```

この段階の classification は Green-A（conditional）とする。

```text
fixed-prime rotation step and positivity: CLOSED
rotation irrationality interface: CLOSED / explicit hypothesis
irrationality -> dense natural AddCircle orbit: CLOSED
fundamental QIII target open/nonempty: CLOSED
arbitrarily late natural target hits: CLOSED
circle hit -> periodic natural cell lift: CLOSED
cofinal cell-index lift: CLOSED
irrational rotation -> CFZP-027 cofinal ready-hit provider: CONDITIONAL / CLOSED
independent irrationality provider: OPEN / GAP
subcritical-window provider: OPEN / GAP
cofinal credit-debt dominance: OPEN / GAP
```

任意 window の subcriticality、`T * log p / (2π)` の irrationality、positive
density/equidistribution、Bad debt envelope の制御、automatic block dominance、
infinite sum、joint limit、limit exchange、finite-window criticality の無条件化、
global RH は導入しない。

## 41. CFZP-029 — universal prime-power Bad-debt envelope

CFZP-029 は CFZP-027 に残っていた Bad pair ごとの解析入力を自動化した。
centered frequency cell の左端から derivative prefactor ceiling を作り、
dimensionless phase derivative core を `|sin| ≤ 1`, `|cos| ≤ 1` と右端角度で
抑える universal polynomial envelope を導入した。これにより safe prime power
ごとに、次の explicit finite spine を閉じた。

```text
left prefactor ceiling
  -> centered derivative absolute envelope
  -> event / prime-power pulse absolute bound
  -> one-event negative-debt bound
  -> finite Bad-debt envelope sum
  -> CFZP-027 certificate with no per-Bad K / henvelope inputs
```

critical scale は既存の
`cfzpModeCriticalScale n = exp (-(1 / 2) * log n)` をそのまま用いるため、
prime-power `p^j` では exponent とともに減衰する。universal core envelope は
`α ≤ 1` を仮定せず、`|1 - α^2|` によって任意の非負 aspect ratio に適用する。

この段階の classification は Green-A（finite and conditional interfaces）とする。

```text
left-endpoint derivative prefactor ceiling: CLOSED
universal phase-core absolute envelope: CLOSED
centered derivative-core absolute envelope: CLOSED
automatic CFZP-023 derivative envelope for every safe prime power: CLOSED
automatic event/pulse absolute envelope: CLOSED
automatic one-event negative-debt bound: CLOSED
automatic finite Bad-debt sum: CLOSED
CFZP-024 certificate constructor without per-Bad K/henvelope: CLOSED
weighted Good-credit vs Bad-debt dominance: OPEN / GAP
```

cofinally many Good hitsから weighted credit/debt dominance、automatic Bad sum の
小ささ、任意 window の subcriticality、prime phase rotation の irrationality、
positive density/equidistribution、infinite sum、joint limit、limit exchange、
finite-window criticality の無条件化、CFZP-018 provider、global RH は導入しない。

## 42. CFZP-030 — weighted prime-power credit/debt factorization

CFZP-030 は Good credit と CFZP-029 の automatic Bad debt に共通する arithmetic
carrier

```text
2 * log(p) * cfzpModeCriticalScale(p^j)
```

を first-class に切り出した。critical scale の prime-power specialization は
exact に

```text
cfzpModeCriticalScale(p^j)
  = exp(-(j / 2) * log p)
```

となり、Good 側の normalized shape は
`CenteredDerivativePrefactorFloor * PhaseCoreMargin`、Bad 側の normalized shape は
CFZP-029 の automatic centered derivative bound で表される。さらに finite Good sum
から finite automatic Bad sum を引く `cfzp030CertifiedNetBalance` を定義し、
CFZP-024 の dominance inequality を net-balance inequality に書き換える代数 API と
既存の radial-deficit endpoint bridge を追加した。

この段階の classification は Green-A（finite exact factorization）とする。

```text
common critical carrier and positivity: CLOSED
prime-power critical-scale exponent factorization: CLOSED
Good local carrier factorization: CLOSED
Bad local carrier factorization: CLOSED
Good prefactor floor <= Bad prefactor ceiling sanity: CLOSED
finite automatic net balance: CLOSED
explicit finite Good/Bad weighted-sum identity: CLOSED
CFZP-024 dominance rewrite through net balance: CLOSED / explicit equality bridge
independent weighted finite-balance provider: OPEN / GAP
prime-axis weighted mass provider: OPEN / GAP
```

本段は weighted Good sum の優越、prime-axis mass の収束・発散、cofinal dominance、
arbitrary window の subcriticality、rotation irrationality、infinite sum、joint limit、
limit exchange、CFZP-018 provider、global RH を導入しない。

## 43. CFZP-031 — universal-envelope efficiency ledger

CFZP-031 は CFZP-029 の automatic Bad envelope を safe prime-power cell の
reference mass `μ(p,j)` とし、ready Good shape を同じ mass に対する dimensionless
efficiency `ρ(p,j)` で正規化した。これにより、finite block の Good contribution は
`ρ * μ`、Bad contribution は `-μ` として、Good-minus-Bad ledger を構成できる。

新しい finite API は、reference mass の automatic Bad debt との一致、ready Good
efficiency の正値性、prefactor efficiency の exact factorization と `≤ 1` bound、
Good local credit との積表示、finite ledger の local-credit-minus-automatic-debt
表示、および block support 上の一つの reference-mass-weighted signed occupancy sum
を閉じる。既存の CFZP-030 radial-contact endpoint adapter も ledger bound の有限
形として再利用する。

この段階の classification は Green-A（有限の正規化 ledger）とする。

```text
universal reference mass = automatic Bad envelope: CLOSED
strict positivity on safe prime-power cells: CLOSED
ready Good efficiency and positive efficiency: CLOSED
prefactor efficiency exact relation and upper bound: CLOSED
Good credit = efficiency * reference mass: CLOSED
finite efficiency ledger identity: CLOSED
single weighted signed occupancy representation: CLOSED
finite radial-contact endpoint adapter: CLOSED / existing bridge
weighted occupancy dominance: OPEN / GAP
positive weighted density and prime-axis mass: OPEN / GAP
subcritical window, irrational rotation, infinite sum, and limit exchange: OPEN / GAP
global RH: OPEN / OUT OF SCOPE
```

本段は weighted occupancy dominance、positive density/equidistribution、automatic
subcritical window provider、prime-axis weighted mass、infinite sum、joint limit、
limit exchange、finite-window criticality の無条件化、CFZP-018 provider、global RH を
導入しない。

## 44. CFZP-032 — uniform ready-Good efficiency floor and weighted coverage

CFZP-032 は CFZP-031 の efficiency ledger を、Good efficiency の uniform floor と
reference-mass coverage の有限 criterion へ接続した。まず Good efficiency を

```text
ReadyGoodEfficiency
  = PrefactorEfficiency * ReadyGoodPhaseEfficiency
```

に分解し、Bad 側の universal phase envelope の右端単調性と、subcritical aspect
ratio における共通 quadratic coefficient
`q(α) = 1 + 2α - α²` を固定した。large-cell quadratic-vs-linear inequalities と
prefactor の左端条件を明示する `Cfzp032UniformReadyCell` を導入した。さらに
`k ≥ 1` と `j ≥ 3` からこの contract を内部で生成する threshold theorem を閉じ、そこから

```text
exp(-(a * 2ε)) * sin(τ) / 128
```

という prime/exponent-independent な positive efficiency floor を得る有限 theorem
を追加した。cell threshold は caller-supplied hypothesis ではなく、明示的な有限
index threshold から内部生成される。

さらに block 全体と Good subset の reference mass を定義し、

```text
(1 + ρ₀) * GoodReferenceMass - BlockReferenceMass
  ≤ EfficiencyLedger
```

を証明した。これにより、finite weighted reference-mass coverage inequality から
radial-contact endpoint へ到達する API を閉じた。fixed-prime cofinal hit の強化は
既存 provider と finite readiness threshold を条件にした theorem とし、density や
mass share を自動的には主張しない。

この段階の classification は Green-A（有限 exact factorization と条件付き floor）と
する。

```text
direct EfficiencyLedger endpoint adapter: CLOSED
prefactor/phase efficiency factorization: CLOSED
phase-envelope right-endpoint monotonicity: CLOSED
common subcritical quadratic coefficient: CLOSED
internal finite large-cell threshold: CLOSED
uniform positive efficiency floor independent of p,j: CLOSED
CFZP-028 cofinal hit -> cofinal uniformly-efficient hit: CLOSED / irrationality-conditional
weighted reference-mass split and ledger lower bound: CLOSED
weighted coverage endpoint criterion: CLOSED
weighted Good reference-mass coverage provider: OPEN / GAP
```

本段は equidistribution、positive density、PNT、automatic weighted coverage、prime-axis
mass theorem、infinite sum、joint limit、limit exchange、finite-window criticality の
無条件化、CFZP-018 provider、global RH を導入しない。

## 45. CFZP-033 — reference-mass axis diagnostics and sigma-decay normalization

CFZP-033 は CFZP-032 の finite reference mass を prime-power logarithmic coordinate
`u = j * log p` に展開した。phase center、left/right magnitude、right angle の exact
adapter と exponent-axis successor identity を追加し、critical carrier
`exp(-(1/2)u)` と boundary factor `exp(-(σ-1/2)(u-ε))` を

```text
exp((σ - 1/2)ε) * exp(-σu)
```

へ再結合した。従って reference mass の exponential decay exponent は rectangle
parameter `σ` であることを generic real-coordinate theorem として固定した。

さらに reference mass を

```text
2 * log p * exp((σ - 1/2)ε) * exp(-σu) * ReducedShape(u)
```

へ exact factorization し、subcritical window の finite large-coordinate region で
`ReducedShape` を `T²/u` と `64*(T+1)²/u` の間に挟んだ。これにより prime axis
`j = 1` では `log p` が有限 comparison の中で cancel し、fixed-prime exponent axis
では `1/j` が残ることを theorem/API として記録した。

```text
prime-power logarithmic coordinate adapters: CLOSED
critical-scale/boundary exponential recombination to σ: CLOSED
exact reference-mass sigma-decay factorization: CLOSED
subcritical reduced-shape polynomial normal form: CLOSED
large-coordinate reduced-shape lower bound c1/u: CLOSED
large-coordinate reduced-shape upper bound c2/u: CLOSED
prime-axis finite two-sided mass comparison: CLOSED / subcritical-conditional
fixed-prime exponent-axis finite two-sided mass comparison: CLOSED / subcritical-conditional
axis diagnostic without infinite-sum claims: CLOSED
weighted Good reference-mass coverage provider: OPEN / GAP
```

本段は fixed-prime total mass の収束、prime-axis total mass の発散、prime-axis dominance、
weighted Good coverage、prime reciprocal divergence、PNT/Mertens、density、infinite
sum、summability、limit exchange、CFZP-018 provider、global RH を導入しない。

## 46. CFZP-034 — prime-axis mass reservoir reduction and finite residual decomposition

CFZP-034 は prime axis `j = 1` の large-prime threshold を正式に開き、有限 block の
reference mass を eligible prime-axis、exceptional prime-axis、higher-prime-power の
三つの有限質量へ exact に分解した。rectangle の `σ > 1/2` と
`exp(-σ log p)` による canonical prime-axis weight を固定し、
`3ε ≤ log p` から CFZP-032 の prefactor threshold
`2ε ≤ phaseMagnitudeLeft` を回収した。

また `Cfzp032UniformReadyCell` を直接受ける generic efficiency adapter を追加し、
prime axis `j = 1` について `k ≥ 1`、eligible、ready hit、subcritical window の下で
CFZP-032 の uniform positive efficiency floor を得た。eligible support 上では
CFZP-033 の finite two-sided comparison を項別に加え、lower/upper constants と
sigma-weight sum の比較を閉じた。exceptional prime-axis mass と higher-power mass は
捨てずに named finite residual として保持し、これらを含む具体的 reservoir inequality
から CFZP-032 の radial-contact endpoint へ流す theorem を追加した。

Gate H では higher-power の sigma factor を prime-axis weight の有限自然数冪へ正規化した。
prime-log phase の weighted occupancy、PNT/Mertens、Dirichlet、prime reciprocal divergence、
positive density、infinite sum、summability、limit exchange、CFZP-018 provider、global RH
は導入していない。prime phase occupancy と exceptional/higher residual elimination は
explicit Gap のままである。

```text
σ > 1/2 and prime-axis weight: CLOSED
prime-axis j = 1 threshold 3ε ≤ log p: CLOSED
prime-axis uniform ready-Good floor: CLOSED
prime-axis/higher-power exact support split: CLOSED
eligible/exceptional exact support split: CLOSED
exact three-way finite reference-mass decomposition: CLOSED
eligible sigma-weighted upper bound: CLOSED
Good sigma-weighted lower bound: CLOSED
finite prime-axis reservoir -> radial endpoint: CLOSED / residual-conditional
higher-power sigma-weight normalization: CLOSED
prime-log phase weighted occupancy provider: OPEN / GAP
exceptional and higher-power residual elimination: OPEN / GAP
```

## 47. CFZP-035 — exact signed efficiency normalization

CFZP-035 は CFZP-034 の粗い reservoir 定数と、実際の branch-free prime-power event
との間を exact signed efficiency で正規化した。safe prime-power cell ごとに

```text
signedEfficiency(p,j) = branchFreeEvent(p,j) / referenceMass(p,j)
```

を定義し、reference mass との積が actual event に戻ること、および signed score が
`[-1, 1]` に入ることを閉じた。CFZP-030 の ready Good credit はこの exact score の
下界であり、CFZP-034 の uniform ready-Good floor も同じ score へ移送できる。

さらに、finite block の signed efficiency mass を定義し、それが branch-free event
block、von Mangoldt pulse block、ledger subtraction、radial-contact recurrence と
exactly 一致することを証明した。eligible prime-axis、exceptional prime-axis、
higher-power の三つの actual signed contribution は envelope で置換せず、そのまま
有限 residual として保持する。prime axis では CFZP-033 の sigma weight を抽出した
signed amplitude も追加した。

Gate A の粗い係数差は有限 diagnostic として閉じた。一方、actual signed score の
prime-axis 全体にわたる優越、prime-log phase distribution、automatic subcritical
window、残差消去は明示的な `Cfzp035ExactSignedEfficiencyNormalizationGap` に残した。

```text
coarse finite coefficient obstruction: CLOSED
exact event/reference-mass signed efficiency: CLOSED
signed efficiency absolute bound: CLOSED
ready Good efficiency -> exact score lower bound: CLOSED
uniform floor -> exact score adapter: CLOSED
finite exact signed block/event/ledger identities: CLOSED
finite radial-contact recurrence and endpoint adapter: CLOSED
exact three-way signed decomposition with residuals: CLOSED
prime-axis sigma-weighted signed amplitude: CLOSED
prime-axis signed phase dominance: OPEN / GAP
prime-log signed phase distribution: OPEN / GAP
automatic subcritical window and residual elimination: OPEN / GAP
infinite sums, limit exchange, and global RH: OPEN / OUT OF SCOPE
```

本段は prime distribution、PNT/Mertens/Dirichlet、positive density、infinite sum、
summability、limit exchange、actual score が Good cell で自動的に `-1` になること、
CFZP-018 provider、global RH を導入しない。

## 48. CFZP-036 — prime-axis sigma-stripped periodic carrier

CFZP-036 は CFZP-035 の prime-axis signed amplitude から sigma weight を剥がし、
`u = log p` の coordinate amplitude を first-class にした。safe prime-power の
有限 identity から prime-axis specialization を接続し、boundary core を

```text
v * (a sin(vT) - T cos(vT)) + sin(vT)
```

へ exact に分解した。従って coordinate amplitude は、単一の periodic carrier と
有限 rational remainder の和になる。remainder は `p` や `u` に依存しない定数
`K(ε,W)` により `K/u` で有限に抑えた。

さらに leading carrier を

```text
(S₀ * sin(Tu) + C₀ * cos(Tu)) / ε
```

へ exact に展開し、`S₀² + C₀² > 0` を exponential の順序と
`sin² + cos² = 1` から内部証明した。carrier period `2π/T` と、有限 remainder
envelope から positive/negative carrier margin を actual coordinate amplitude の
符号へ移す theorem も追加した。

```text
coordinate sigma-stripped amplitude: CLOSED
prime specialization to CFZP-035 amplitude: CLOSED
boundary core linear-phase decomposition: CLOSED
exact leading periodic carrier + remainder: CLOSED
finite K/u remainder envelope: CLOSED
single sin/cos coefficient normal form: CLOSED
leading coefficient nontriviality: CLOSED / internally proved
explicit period 2π/T: CLOSED
finite carrier-margin -> actual-amplitude transport: CLOSED
prime-log carrier-arc hit provider: OPEN / GAP
weighted signed carrier dominance: OPEN / GAP
infinite sums / prime distribution / global RH: OPEN / OUT OF SCOPE
```

本段は prime distribution、Bertrand、PNT/Mertens/Dirichlet、prime-log equidistribution、
positive density、infinite sum、summability、limit exchange、exceptional/higher-power
residual elimination、CFZP-018 provider、global RH を導入しない。

## 49. CFZP-037 — periodic carrier arc geometry and prime-log target intervals

CFZP-037 は CFZP-036 の非零 periodic carrier から、各自然周期 cell に同じ幅と
同じ margin を持つ positive / negative carrier arc を構成した。half-period の
符号反転、明示的な positive / negative carrier point、連続性による閉区間 arc、
自然数倍 period の翻訳を有限 theorem として閉じている。

また `K/u` remainder を吸収する explicit finite threshold と late-cell index を
導入し、late positive / negative arc 上で sigma-stripped coordinate amplitude の
一様な符号 margin を得た。log-coordinate の positive arc は `exp` によって
固定比 `exp (2 * halfWidth) > 1` の実数乗法区間へ exact に移送され、prime-log
hit predicate と sigma-weighted event の有限 lower-bound transport も追加した。

```text
carrier half-period sign reversal: CLOSED
explicit positive / negative carrier point: CLOSED
uniform positive / negative carrier arc data: CLOSED
natural-period translated arcs: CLOSED
finite late-cell threshold for K/u absorption: CLOSED
late arc -> coordinate amplitude uniform sign margin: CLOSED
log arc -> exact multiplicative real interval: CLOSED
fixed interval ratio exp (2 * halfWidth) > 1: CLOSED
prime hit -> quantitative signed event transport: CLOSED
prime-arc hit predicate and finite sigma-weighted mass frontier: CLOSED
prime occupancy / weighted prime mass in every interval: OPEN / GAP
prime distribution / positive density / infinite sums / limit exchange: OPEN / OUT OF SCOPE
exceptional or higher-power residual elimination / CFZP-018 provider / global RH: OPEN / OUT OF SCOPE
```

本段は Bertrand、PNT、Mertens、Dirichlet、prime-log equidistribution、positive
density、summability、limit exchange、`σ < 1` の新規仮定、exceptional/higher-power
residual の消去、CFZP-018 provider、global RH を導入しない。次段の arithmetic
frontier は、固定比の prime intervals に入る sigma-weighted prime mass の証明である。

## 50. CFZP-038 — prime-axis positive-carrier weighted mass reduction

CFZP-038 は CFZP-037 の positive carrier hit を、034 の eligible prime-axis pair
support と 035 の exact signed-efficiency ledger に有限かつ直接に接続した。単一 cell
および有限 cell window の Good support、witness cell elimination、late Good の
sigma-weighted positive credit、任意 subset の `-referenceMass` debt envelope、
eligible Good/Bad の exact partition を追加している。

Good credit と Bad / exceptional / higher-power の named debt envelope を組み合わせ、
残差を消去せずに exact carrier-reservoir inequality から radial contact endpoint を
得る theorem を閉じた。さらに 034 の finite sigma upper comparison を使う coarse
sigma-only reservoir corollary と、single-cell の right-end sigma floor による
cardinality-to-weighted-mass adapter も用意した。

```text
positive-arc Good pair support: CLOSED
late positive hit -> sigma-weighted actual-event credit: CLOSED
universal signed debt envelope: CLOSED
eligible Good/Bad exact split: CLOSED
exact positive-carrier reservoir -> radial endpoint: CLOSED
sigma-only Good/Bad reservoir reduction: CLOSED
right-end sigma floor: CLOSED
finite cardinality -> weighted mass adapter: CLOSED
prime count lower bound in carrier cells: OPEN / GAP
positive-arc weighted mass dominance: OPEN / GAP
prime-log weighted distribution: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、positive density、
infinite sums、summability、limit exchange、`σ < 1` の無根拠導出、ReadyThirdQuadrantHit
への偽接続、exceptional/higher-power residual の消去、CFZP-018 provider、global RH を
導入しない。Good support の occupancy と weighted mass dominance は
`Cfzp038PrimeAxisPositiveCarrierWeightedMassGap` に明示的に残している。

## 51. CFZP-039 — exact carrier/remainder signed moment

CFZP-039 は 038 の Good/Bad worst-case route を保持したまま、eligible prime-axis
全体の actual signed mass を 036 の periodic leading carrier と有限 `K / log p`
remainder に exact に分解した。remainder は sigma-weighted finite debt envelope
`Σ sigmaWeight * K / log p` によって上下から挟み、exceptional / higher-power residual
は 038 の named finite debt と組み合わせて leading-carrier reservoir から radial
contact endpoint へ接続している。

さらに、`σ < 1` を自動導出しない explicit interior-strip predicate と
`β = 1 - σ` を追加した。指数 one-period transform の coefficient pair、positive
scale、period / half-period sign reversal、positive / negative existence を有限代数
として閉じ、prime distribution bridge が後段で利用する closed-form model を first-class
にした。`Ioc` 型の有限 period-cell support、cell leading mass、cell remainder debt も
追加している。

```text
eligible signed mass = exact leading carrier + exact remainder: CLOSED
finite K/log(p) remainder debt and absolute bound: CLOSED
leading-carrier reservoir -> radial endpoint: CLOSED
explicit interior strip σ < 1 and β = 1 - σ: CLOSED
exponential transformed coefficient identities and nontriviality: CLOSED
positive-scale exponential one-period transform model: CLOSED
period / half-period sign reversal / positive-negative existence: CLOSED
finite Ioc period-cell support interface: CLOSED
prime-axis carrier-cell distribution: OPEN / GAP
prime-axis asymptotic / Abel bridge: OPEN / GAP
interval-integral identification: OPEN / GAP
exceptional prime-axis residual elimination: OPEN / GAP
higher-prime-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は Good/Bad partition を主 route に再導入せず、PNT、Mertens、Dirichlet、Bertrand、
prime-log equidistribution、infinite sums、summability、limit exchange、automatic
`σ < 1`、prime-axis carrier の無条件の符号断定、exceptional/higher-power residual の
消去、CFZP-018 provider、global RH を導入しない。未解決事項は
`Cfzp039PrimeAxisExactCarrierRemainderSignedMomentGap` に明示的に残している。

## 52. CFZP-040 — finite Abel / prime-counting discrepancy bridge

CFZP-040 は CFZP-039 の有限 prime-axis leading-carrier cell を、Mathlib の finite
Abel summation と `Nat.primeCounting` に接続した。実数軸上の carrier test function と
その derivative、prime indicator の累積和、実数端点 `Ioc` の finite Abel identity を
閉じ、指数変換した period cell の raw prime support を 039 の prime-axis finite block
へ floor/log の有限 adapter で同一視した。

さらに有限 smooth model `x / log x` と named discrepancy
`primeCounting - smoothModel` を定義し、actual finite prime carrier sum を smooth
Abel model と discrepancy functional の exact sum に分解した。これは PNT や discrepancy
decay を仮定する theorem ではない。

```text
x-axis carrier test function and derivative: CLOSED
prime indicator cumulative sum = primeCounting: CLOSED
finite Abel prime carrier identity: CLOSED
period-cell exponential endpoints / raw prime support: CLOSED
raw cell <-> CFZP-039 prime-axis cell adapter: CLOSED
Abel prime sum -> raw prime cell -> CFZP-039 carrier cell: CLOSED
prime-counting smooth/discrepancy exact split: CLOSED
smooth Abel model -> density integral: OPEN / GAP
log-coordinate density integral adapter: OPEN / GAP
prime-counting discrepancy decay / relative error: OPEN / GAP
carrier-cell asymptotic dominance: OPEN / GAP
exceptional / higher-prime-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite sums、
summability、limit exchange、Good/Bad の主 route、automatic `σ < 1`、exceptional /
higher-power residual の消去、CFZP-018 provider、global RH を導入しない。未解決の
analytic inputs は `Cfzp040PrimeAxisFiniteAbelPrimeCountingDiscrepancyGap` として
明示的に保持している。

## 53. CFZP-041 — smooth/discrepancy cell reservoir reduction

CFZP-041 は 040A の finite Abel → raw prime cell → CFZP-039 cell bridge を、自然数の
floor block 全体の eligible prime-axis support へ拡張した。cell の natural endpoints
の順序、eligible block と 039 carrier-cell support の exact equality、eligible leading
mass / remainder debt の cell 表現を有限 Finset の事実として閉じている。

さらに、039 cell leading mass を 040 の smooth Abel model と named discrepancy
functional の exact sumに接続し、discrepancy の絶対値を cell debt として定義した。
外部から有限 bound `D` が供給されると `Smooth - D ≤ actual carrier cell` が得られ、
039 の leading-carrier reservoir theorem を通じて radial contact endpoint へ運ぶ有限
reservoir theorem も閉じている。

```text
cell natural block order: CLOSED
eligible axis block = carrier-cell support: CLOSED
CFZP-039 cell mass = smooth Abel + discrepancy: CLOSED
functional discrepancy debt: CLOSED
smooth - discrepancy <= actual carrier cell: CLOSED
smooth/discrepancy cell reservoir -> radial endpoint: CLOSED
smooth Abel positive cell lower bound: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
smooth density/log-coordinate reduction: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite sums、
summability、limit exchange、automatic `σ < 1`、smooth model の無条件 positivity、
discrepancy decay、exceptional/higher-power residual の消去、CFZP-018 provider、global
RH を導入しない。未解決の analytic inputs は
`Cfzp041PrimeAxisSmoothDiscrepancyCellReservoirGap` として明示的に保持している。

## 54. CFZP-042 — smooth density and log-coordinate transform

CFZP-042 は、041 に残った finite smooth Abel cell の解析的正体を分解した。`x / log x`
の derivative density、finite integration-by-parts による x-density integral、`x = exp u`
による log-coordinate cell integral、period cell の `[0,P]` translation を順に closed
した。さらに、指数 carrier の一周期 interval integral を明示的な原始関数で評価し、
039 の exponential carrier transform と exact に同一視した。

最後に、smooth cell を

```text
exp(β U) * (q(U) * exponential transform + weight variation error)
```

へ finite integral linearity だけで exact 分解した。variation error の量的評価はこの段
の対象外であり、caller-supplied finite integrability data と smooth-cell/log-cell bridge
を明示的に要求する。

```text
smooth counting density derivative: CLOSED
smooth Abel model -> x-density integral: CLOSED
x-density integral -> log-coordinate cell integral: CLOSED
period-cell translation to [0,P]: CLOSED
exponential carrier moment = CFZP-039 transform: CLOSED
smooth cell = transform main + weight-variation error: CLOSED
weight-variation quantitative bound: OPEN / GAP
eventual smooth-cell positive lower bound: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite sums、
summability、limit exchange、automatic `σ < 1`、variation error の無条件 negligible claim、
smooth-cell の無条件 positivity、exceptional/higher-power residual の消去、CFZP-018
provider、global RH を導入しない。未解決事項は
`Cfzp042PrimeAxisSmoothDensityLogCoordinateTransformGap` に明示的に保持している。

## 55. CFZP-043 — smooth weight variation and eventual positive cells

CFZP-043 は、042 の有限一周期分解で隔離された log-density weight variation error を
first-class な有限 absolute carrier moment によって評価した。`q(u) = 1/u - 1/u^2`
について late-coordinate positivity、`q(U) >= 1/(2U)`、一周期上の variation bound
`|q(U+t)-q(U)| <= P/U^2` を閉じ、interval-integral の単調性から

```text
|WeightError(U,c)| <= Cvar(c) / U^2
```

を得た。さらに 042 の exact split に有限の `hcell`、`hA_int`、`hE_int` を入力し、
positive transform phase `M(c) > 0` と

```text
U >= max (2) (4 * Cvar(c) / M(c))
```

の下で

```text
exp(β U) * M(c) / (4U) <= SmoothCell(U)
```

および strict positivity を閉じた。cell-left のコファイナル性は carrier period の
positivity と Archimedean property だけで示し、039 の positive-transform phase と
explicit threshold を同時に選ぶ有限 theorem を公開した。

```text
log-density positivity / 1/(2U) lower bound: CLOSED
log-density one-period variation <= P/U^2: CLOSED
finite exponential carrier absolute moment: CLOSED
weight-variation error <= Cvar/U^2: CLOSED
positive-transform explicit smooth-cell lower bound: CLOSED
positive transform phase + cofinal late cell coordinates: CLOSED
explicit smooth-margin reservoir -> radial endpoint: OPEN / GAP
automatic smooth-cell analytic readiness: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
exceptional/higher-power residual elimination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite sums、
summability、limit exchange、automatic `σ < 1`、prime-counting discrepancy decay、
exceptional/higher-power residual の消去、CFZP-018 provider、global RH を導入しない。
解析的 readiness は各有限 cell の明示的 premise として残し、未解決事項は
`Cfzp043PrimeAxisSmoothWeightVariationEventualPositivityGap` に保持している。

## 56. CFZP-044 — explicit smooth-margin radial budget and late exceptional elimination

CFZP-044 は、043 の smooth positivity threshold と 041 の prime-axis eligibility
threshold を一つの radial-late threshold に統合した。positive transform phase の選択と
cell-left の cofinality から、十分 late な radial cell を有限に選べる。

late cell の prime-axis block support については、finite floor/log bridge から
`CellLeft < log p <= CellRight` を回収し、`max (3 * ε) 1 <= CellLeft` を適用することで
全 prime-axis point が eligible になることを exact に証明した。したがって exceptional
prime-axis support と reference mass は、その cell ではともに `0` となる。これは
asymptotic residual elimination ではなく、有限 support の消滅である。

さらに 043 の interval-integral readiness を公開 helper として圧縮し、

```text
ExplicitSmoothMargin(U,c) := exp(β U) * Transform(c) / (4 U)
```

を first-class にした。042 の smooth/log-cell equality を有限 premise として受け取ると、
この margin が smooth Abel cell 以下になる。exceptional mass を除いた

```text
starting radial deficit
+ prime-axis remainder debt
+ higher-power reference mass
+ discrepancy debt D
<= ExplicitSmoothMargin + η
```

という budget predicate から、041 の finite reservoir theorem によって右端 radial
contact deficit `<= η` を得る main theorem も閉じた。discrepancy regularity と
`SmoothAbel = SmoothLogCell` の readiness は caller-supplied のまま保持している。

```text
combined radial-late threshold: CLOSED
late prime-axis block = eligible prime-axis block: CLOSED
late exceptional prime-axis support/mass = 0: CLOSED
finite one-period carrier/error integrability compression: CLOSED
explicit smooth margin first-class and <= SmoothAbelCell: CLOSED
explicit smooth-margin budget -> radial endpoint: CLOSED
positive phase + cofinal radial-late cells: CLOSED
cofinal explicit-margin budget interface: CLOSED (provider remains open)
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
higher-prime-power residual domination: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite sums、
summability、limit exchange、automatic `σ < 1`、discrepancy decay、higher-power residual
の無条件 elimination、CFZP-018 provider、global RH を導入しない。残る境界は
`Cfzp044PrimeAxisExplicitSmoothMarginRadialBudgetGap` に明示的に保持している。

## 57. CFZP-045 — higher-prime-power sigma-tail envelope

CFZP-045 は、044 の radial budget に残る higher-prime-power reference mass を、各 pair
の exact sigma decay を保つ有限 tail envelopeへ置き換えた。higher-power support の
actual exponent `pk.2 + 1` が `>= 2` であることと base prime の回収を閉じ、033 の
fixed-prime upper bound を 034 の sigma-weight power identity と結合した。log-coordinate
の有限 algebra

```text
log p / (j log p) = 1 / j
```

により、各 pair の reference mass は

```text
K(ε,W) * sigmaWeight(p)^j / j
```

以下となる。これを有限 block 上で sum して、raw higher-power mass が
`K(ε,W) * HigherPowerSigmaTail` 以下になることを exact に証明した。

さらに `floor(exp U)` による current support の向きを使い、late carrier cell では
全 higher-power pair が `2 ε <= j log p` および `1 <= j log p` を満たすことを閉じた。
したがって carrier-cell higher-power mass も同じ finite sigma-tail envelope 以下であり、
044 の explicit smooth-margin budget に代入して右端 radial contact deficit `<= η` を
得る main theoremを公開した。

```text
higher-power actual exponent >= 2: CLOSED
higher-power base prime recovery: CLOSED
log p / (j log p) = 1/j: CLOSED
per-pair reference mass <= constant * sigmaWeight^j / j: CLOSED
finite higher-power sigma tail: CLOSED
raw higher-power block mass <= constant * sigma tail: CLOSED
late carrier-cell higher-power block safety: CLOSED
carrier-cell higher-power mass <= sigma-tail envelope: CLOSED
sigma-tail explicit-margin budget -> radial endpoint: CLOSED
higher-power sigma-tail cardinality bound: OPEN / GAP
higher-power sigma-tail exponential decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
actual cofinal budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、
summability、limit exchange、automatic `σ < 1`、sigma-tail の無条件 negligible claim、
CFZP-018 provider、global RH を導入しない。残る provider 境界は
`Cfzp045HigherPrimePowerSigmaTailEnvelopeGap` に明示的に保持している。

## 58. CFZP-046 — higher-prime-power deterministic cell counting and exponential envelope

CFZP-046 は、045 の有限 sigma-tail を prime distribution なしの自然数 rectangular
overcount で評価し、floor-free な指数 envelope に変換した。higher-power pair の
log-coordinate について、有限 floor/exp/log bridge から

```text
U < j * log p <= R,
p <= floor(exp(R/2)),
j <= floor(R/log 2)
```

を exact に回収した。これにより全自然数 base と exponent の有限 bounding box、support
cardinality bound、各 term の `exp(-σ U) / 2` bound、finite sigma-tail の cardinality
envelope を閉じた。

さらに floor を除去して

```text
HigherPowerSigmaTail(cell)
<= exp(R/2) * (R/log2 + 1) * exp(-σ U)
```

を証明し、`R = U + P` による canonical form
`exp(P/2) * (R/log2 + 1) * exp((1/2 - σ) U)` を公開した。045 の raw reference mass
bound と合成した explicit-envelope radial budget adapter も閉じている。

最後に smooth margin との競合を

```text
competitionKernel(U)
= 8 * U * K(ε,W) * exp(P/2) * (R/log2 + 1) * exp(-U/2)
```

として first-class にし、kernel が positive transform 以下なら higher-power envelope
が explicit smooth margin の半分以下になる有限代数 theorem を閉じた。

```text
higher-power pair log-coordinate cell interval: CLOSED
j >= 2 -> base <= exp(R/2): CLOSED
p >= 2 -> j <= R/log 2: CLOSED
deterministic finite bounding box: CLOSED
higher-power support cardinality bound: CLOSED
uniform cell sigma-tail term <= exp(-σU)/2: CLOSED
finite sigma tail <= cardinality envelope: CLOSED
floor-free exponential envelope: CLOSED
normal form exp(P/2)*(R/log2+1)*exp((1/2-σ)U): CLOSED
raw higher-power mass <= K * exponential envelope: CLOSED
exponential-envelope budget -> radial endpoint: CLOSED
higher-power vs smooth-margin competition kernel: CLOSED
kernel condition -> higher debt <= half smooth margin: CLOSED
competition-kernel eventual decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
prime-axis remainder-cell debt decay: OPEN / GAP
actual cofinal budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、prime density
theorem、infinite prime sums、summability、limit exchange、automatic `σ < 1`、unconditional
discrepancy/remainder decay、CFZP-018 provider、global RH を導入しない。base cap は全自然数
base、exponent cap は全自然数 exponent を数える deliberate overcount であり、残る
eventual kernel と cofinal budget provider は
`Cfzp046HigherPrimePowerCellCountingEnvelopeGap` に保持している。

## 59. CFZP-047 — higher-prime-power competition-kernel decay

CFZP-047 は、046 の competition kernel を cell-left coordinate `U` の profile に正規化し、
その eventual decay を標準的な実指数極限だけで閉じた。`R = U + P` を代入すると、profile
は exact に

```text
A₂ * U² * exp(-U/2) + A₁ * U * exp(-U/2)
```

へ展開できる。Mathlib の `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` を `U/2` に
compose して、二つの項がともに 0 に収束することを証明した。043 の Archimedean cell-left
cofinalityとの合成により、実際の 046 kernel も `n → ∞` で 0 に収束する。

この結果から、positive transform が存在する固定 phase では、十分 late な全 cell で

```text
competitionKernel <= positiveTransform
K * higherPowerEnvelope <= ExplicitSmoothMargin / 2
rawHigherPowerReferenceMass <= ExplicitSmoothMargin / 2
```

を得る cofinal theorem を閉じた。したがって higher-prime-power residual domination は
OPEN/GAP から CLOSED へ移った。さらに higher-power の半分を先に支払った後に残る
`ExplicitSmoothMargin / 2 + η` の finite radial budget と、044 の endpoint theorem を
接続する adapter も公開した。

```text
cell-free higher-power competition profile: CLOSED
profile quadratic/linear exponential normal form: CLOSED
U * exp(-U/2) -> 0: CLOSED
U^2 * exp(-U/2) -> 0: CLOSED
higher-power competition profile -> 0: CLOSED
carrier cell-left -> +infinity: CLOSED
actual cell competition kernel -> 0: CLOSED
positive transform eventually dominates kernel: CLOSED
higher-power exponential envelope eventually <= half smooth margin: CLOSED
raw higher-power reference mass eventually <= half smooth margin: CLOSED
positive phase + cofinal higher-power domination package: CLOSED
remaining-half budget -> radial endpoint: CLOSED
higher-prime-power residual domination: CLOSED
prime-axis remainder-cell debt decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
actual cofinal remaining-half budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、prime density theorem、
infinite prime sums、summability、limit exchange、automatic `σ < 1`、unconditional discrepancy
decay、prime-axis remainder decay、CFZP-018 provider、global RH を導入しない。残る provider
境界は `Cfzp047HigherPrimePowerCompetitionDecayGap` に保持している。

## 60. CFZP-048 — prime-axis remainder Abel/smooth-discrepancy reduction

CFZP-048 は、`K / log p` 型の prime-axis remainder を有限 Abel summationで、elementary
smooth Abel model と明示的な prime-counting discrepancy functional に分解した。指数変数
`x = exp u` による有限区間の change of variables で smooth model を log-cell integral に
移し、`u >= 2` の cell では integrand の非負性と endpoint exponential envelope を
`intervalIntegral.integral_mono_on` で閉じた。

```text
remainder test function and derivative: CLOSED
finite prime remainder sum = Abel endpoint/integral form: CLOSED
raw prime support -> eligible prime-axis pair support: CLOSED (finite exact image)
smooth Abel model + discrepancy functional split: CLOSED
smooth Abel model -> density integral: CLOSED with finite regularity certificates
density integral -> smooth log-cell: CLOSED with finite change-of-variables certificates
smooth remainder cell nonnegativity and endpoint envelope: CLOSED
smooth remainder debt <= quarter explicit smooth margin: CLOSED under threshold
remainder debt <= quarter margin + discrepancy debt: CLOSED
CFZP-047 higher-power half-margin + CFZP-048 remainder quarter-margin composition: CLOSED
remaining-quarter predicate excludes higher-power and structural smooth remainder: CLOSED
remaining-quarter budget -> CFZP-044 explicit-margin radial endpoint: CLOSED with supplied providers
prime-counting discrepancy decay: OPEN / GAP
prime-axis remainder discrepancy decay: OPEN / GAP
automatic interior-strip window provider: OPEN / GAP
automatic SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
automatic pointwise discrepancy-to-functional bound: OPEN / GAP
cofinal remaining quarter-margin budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、prime density theorem、
infinite prime sums、summability、limit exchange、automatic `σ < 1`、unconditional discrepancy
または remainder decay、CFZP-018 provider、global RH を導入しない。未証明の供給条件は
`Cfzp048PrimeAxisRemainderAbelSmoothDiscrepancyGap` に明示的に保持している。

## 61. CFZP-049 — combined prime-counting discrepancy functional envelope

CFZP-049 は、carrier と `K / log p` 型 prime-axis remainder に現れる二つの有限 discrepancy
functional を、同じ pointwise error
`E(x) = primeCounting(floor x) - x / log x` の Abel functional として共通化した。
有限 sensitivity
`|f(b)| + |f(a)| + ∫ |f'|` により、一つの pointwise bound から両 functional、combined
discrepancy debt までを明示的に支配する。relative bound からは `exp R / U` を保持した
finite cell envelope を得る。

```text
generic finite Abel discrepancy sensitivity: CLOSED
pointwise discrepancy -> carrier functional: CLOSED
pointwise discrepancy -> remainder functional: CLOSED
pointwise discrepancy -> combined discrepancy debt: CLOSED
relative discrepancy -> uniform cell bound with exp(R) / U: CLOSED
combined relative-discrepancy finite envelope: CLOSED
combined debt -> corrected CFZP-048 remaining-quarter adapter: CLOSED with supplied certificates
explicit carrier/remainder sensitivity asymptotic envelope: OPEN / GAP
relative prime-counting discrepancy decay provider: OPEN / GAP
automatic PNT/relative-error hookup: OPEN / GAP
leading SmoothAbel -> SmoothLogCell readiness: OPEN / GAP
interior-strip provider and cofinal final budget: OPEN / GAP
CFZP-018 provider / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、
summability、limit exchange、automatic `σ < 1`、unconditional discrepancy decay、CFZP-018
provider、global RH を導入しない。有限 pointwise/relative discrepancy predicate は provider
interface としてのみ使用し、未証明の小ささは
`Cfzp049CombinedPrimeCountingDiscrepancyEnvelopeGap` に残す。

## 62. CFZP-050 — combined discrepancy sensitivity explicit cell envelope

CFZP-050 は CFZP-049 の finite combined sensitivity を、一周期 cell 上の明示的な有限係数
へ落とした。leading carrier の sine/cosine pair には triangle-inequality coefficient を与え、
carrier と `K / log p` remainder の endpoint/derivative envelope は有限セル証明書として明示した。
その結果、combined sensitivity は `C_sens * exp(-sigma * U)` に抑えられ、`R = U + P` により
relative discrepancy の `exp(R) / U` と explicit smooth margin の
`exp((1-sigma) * U) / (4U)` が同じ座標スケールに正規化される。

```text
finite leading-carrier amplitude and derivative constants: CLOSED
finite carrier/remainder sensitivity coefficient API: CLOSED from actual finite-cell estimates
combined sensitivity -> explicit relative envelope: CLOSED
general margin-share coefficient cancellation: CLOSED
quarter coefficient condition and reduced remaining-quarter adapter: CLOSED
eighth coefficient constant: EXPOSED
automatic finite-cell endpoint/derivative certificate generation: CLOSED with finite integrability inputs
relative prime-counting discrepancy decay provider: OPEN / GAP
automatic interior-strip and SmoothAbel -> SmoothLogCell providers: OPEN / GAP
automatic left radial-deficit budget and cofinal final budget: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

本段は PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、
summability、limit exchange、automatic `sigma < 1`、unconditional discrepancy decay、CFZP-018
provider、global RH を導入しない。有限セルの endpoint/derivative envelope は actual test
function から有限 derivative-integrability premise のもとで生成し、未証明の漸近小ささは
`Cfzp050CombinedDiscrepancySensitivityEnvelopeGap` に保持している。

## 63. CFZP-051 — prime-counting PNT ratio to relative cell discrepancy

CFZP-051 は Mathlib v4.32.2 に PNT 定理が存在しないことを前提に、real/floor の
`primeCounting (floor x) / (x / log x)` ratio を唯一の標準 arithmetic provider として
定義した。PNT ratio の証明や外部 Lake dependency はこの checkpoint では導入せず、provider
から先の有限・filter-theoretic reduction を実装した。

```text
standard real/floor PNT ratio provider interface: DEFINED
PNT ratio -> normalized discrepancy ratio -> 0: CLOSED
PNT ratio -> eventual pointwise relative discrepancy: CLOSED
carrier exp-left -> +infinity: CLOSED
pointwise eventual bound -> eventual cell-relative bound: CLOSED
explicit positive eighth-margin tolerance: CLOSED
PNT tolerance -> CFZP-050 eighth coefficient condition: CLOSED
eighth condition -> combined debt <= explicit margin / 8: CLOSED
PNT provider -> eventual combined debt <= margin / 8: CLOSED modulo finite integrability readiness
left radial eighth-credit + discrepancy eighth -> remaining quarter budget: CLOSED
custom relative cell discrepancy provider: RETIRED in the Green-facing chain
standard PNT ratio theorem itself: OPEN / external arithmetic provider
finite derivative-integrability readiness: OPEN / finite analytic readiness input
automatic interior-strip, SmoothAbel -> SmoothLogCell, and left eighth-credit providers: OPEN / GAP
Mathlib PNT theorem: NOT AVAILABLE in current v4.32.2 dependency
external PNT+ dependency: NOT INTRODUCED in CFZP-051
CFZP-018 / global RH: OUT OF SCOPE
```

The public module
`DkMath.RH.CFBRC.CosmicFormulaZetaPrimeCountingPNTToRelativeDiscrepancyAudit` keeps the
PNT ratio, finite cell transport, eighth-margin debt theorem, and explicit
`Cfzp051PrimeCountingPNTToRelativeDiscrepancyGap` firewall together. It does not assert PNT,
explicit error terms, Mertens/Dirichlet/Bertrand input, infinite prime distribution, limit
exchange, automatic finite integrability, automatic left radial credit, or global RH.

## 64. CFZP-052 — finite discrepancy analytic readiness auto audit

CFZP-052 は CFZP-051 に残っていた四つの有限 `IntegrableOn` readiness 条件を、実際の
floor prime-counting discrepancy、smooth model、carrier/remainder の exact derivative
formula、および CFZP-050 の finite derivative envelope から自動生成した。有限セルの
measurability と boundedness だけを使い、PNT ratio や左 radial eighth-credit を新たに
仮定・証明していない。

```text
primeCounting(floor x) measurability: CLOSED
prime-counting discrepancy measurability: CLOSED
carrier derivative exact formula on late cell: CLOSED
remainder derivative exact formula on late cell: CLOSED
carrier absolute derivative finite-cell integrability: CLOSED
remainder absolute derivative finite-cell integrability: CLOSED
distribution-free finite cell discrepancy absolute bound: CLOSED
carrier derivative * discrepancy integrability: CLOSED
remainder derivative * discrepancy integrability: CLOSED
Cfzp051FiniteDiscrepancyAnalyticReadyAt from 1 <= U: CLOSED
eventual finite analytic readiness: CLOSED
PNT provider -> eventual combined debt <= margin / 8 without hReady: CLOSED
PNT + left eighth-credit provider -> eventual remaining-quarter budget: CLOSED
finite discrepancy analytic readiness GAP: RETIRED
standard PNT ratio theorem itself: OPEN / arithmetic provider
left radial eighth-credit provider: OPEN / next structural frontier
automatic interior-strip / SmoothAbel -> SmoothLogCell providers: OPEN / GAP
CFZP-018 / global RH: OUT OF SCOPE
```

The public module
`DkMath.RH.CFBRC.CosmicFormulaZetaFiniteDiscrepancyAnalyticReadinessAudit` closes
`Cfzp051FiniteDiscrepancyAnalyticReadyAt` from `1 ≤ U`, and its PNT wrapper removes the
former finite-readiness argument from the Green-facing CFZP-051 reduction. The module remains
finite and distribution-free: it does not prove PNT, infinite prime-sum convergence, limit
exchange, automatic left radial credit, the final radial budget, or global RH.
