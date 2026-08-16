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
