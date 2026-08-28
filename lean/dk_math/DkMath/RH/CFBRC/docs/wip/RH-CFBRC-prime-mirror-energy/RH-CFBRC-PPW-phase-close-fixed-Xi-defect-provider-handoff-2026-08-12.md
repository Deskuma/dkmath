# RH-CFBRC PPW phase close → fixed Xi defect provider phase 引き継ぎ

作成日: 2026-08-12

目的: 新しい ChatGPT 会話へ、この会話で確定した数学・Lean 実装・研究境界・次工程をそのまま移送するための「賢狼の外部記憶」。

この文書は WIP handoff であり、canonical explanatory docs ではない。

---

# 0. 新しい会話の開始文

新しい会話では、まず次をそのまま貼って開始してよい。

```text
RH-CFBRC fixed Xi defect provider phase を続行する。

この handoff を会話コンテキストの正本とし、GitHub repository Deskuma/dkmath の
現状を最初に確認する。

PPW phase は PPW-023 complete Green で一旦終了。
現在の PPW branch は
wip/RH-CFBRC-prime-mirror-energy-260807-v0
で、handoff 作成前の verified implementation head は
58272bd1ff20e3848cbb25f7d0c4def54bcda985
(Add: PPW-023: fixed centered-Xi full second-moment defect functional)。

まずこの branch が develop へ merge 済みか確認する。
未 merge なら PPW-023 Green checkpoint として merge する。
merge 後の最新 develop から
wip/RH-CFBRC-fixed-xi-defect-provider-260812-v0
を派生して、以後は fixed Xi defect の独立 vanishing provider の証明探索へ集中する。

現在 Lean で証明済みなのは
PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔ RiemannHypothesis
である。
RH 自体はまだ証明していない。

未解決の本体は
PascalCenteredXiFixedDefectVanishesOnSafeRadii
そのものを、RH を使わずに構成すること。

既存 Core として safe radius R では
0 ≤ pascalCenteredXiFixedSecondMomentDefectFunctional R
がある。
したがって独立に
pascalCenteredXiFixedSecondMomentDefectFunctional R ≤ 0
を出せれば vanishing が閉じる。

Prime / explicit formula、CF2D / ThreeElement、centered Xi symmetry / moment identity
の三候補を監査するが、RH-equivalent condition の名前替えを provider と呼んではならない。

既存 Green 層を再実装しない。
同じ scalar defect を independently constrain する theorem だけを探す。
```

---

# 1. Repository / toolchain checkpoint

```text
repository:
  Deskuma/dkmath

PPW branch:
  wip/RH-CFBRC-prime-mirror-energy-260807-v0

verified PPW-023 implementation head before this handoff:
  58272bd1ff20e3848cbb25f7d0c4def54bcda985

commit message:
  Add: PPW-023: fixed centered-Xi full second-moment defect functional

PPW-023 handoff commit:
  95e287d0fabfc4f141fa129f728e7f5b5c98fd67

PPW-022 implementation:
  fab95a8c7d1e714fca1c824c2622c80e0cc24781

PPW-022 handoff:
  b072f195374f241529c83df6fbdb4ac24735c440

PPW-021 implementation checkpoint reported/reviewed:
  ff2b73f964fafe82ce3ce23cf6f22f6922bf9147

Lean:
  v4.32.2

mathlib exact rev:
  905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-023 実装時にユーザー環境で次が Green。

```bash
lake build
lake build DkMath.RH
./lean-build.sh

git diff --check
```

`__build.log` に PPW-023 由来の error はなく、既存 `ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning のみ。

公開 import は `DkMath/RH.lean` に追加済み。

```lean
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
```

なお、会話中の GitHub 状態確認操作で不要な一時 branch

```text
__noop_check_ppw023
```

を誤って作成した。研究 branch ではない。存在していれば削除してよい。

---

# 2. Mathlib の RH 定義と現在の意味

Mathlib の formal RH は概略次。

```lean
/-- A formal statement of the Riemann hypothesis. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ)
    (_ : riemannZeta s = 0)
    (_ : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (_ : s ≠ 1),
    s.re = 1 / 2
```

重要な論理区別:

```text
RiemannHypothesis は Prop として既に定義済み。

未完成なのは
  theorem ... : RiemannHypothesis := by ...
という term の構成。
```

PPW-023 で完成したのは RH の term ではなく、次の同値 theorem。

```lean
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔
      RiemannHypothesis
```

この `↔` 自体は追加の conjectural assumption なしで Green。

しかし左辺そのものは未証明。

---

# 3. PPW phase の役割と終了判定

PPW phase の目的は「RH を何へ還元すればよいか」を Prime / Pascal / Xi / contour / CF2D の側から exact に掘り出すことだった。

最終的な流れは概略:

```text
Prime mirror
→ Pascal prime support
→ prime powers
→ von Mangoldt
→ zeta / -zeta'/zeta
→ zeta zero multiplicity
→ centered Xi
→ local residues
→ one fixed outer contour
→ radial layer-cake
→ CF2D q2 radial mass
→ fixed Xi second-moment defect
→ horizontal energy
→ RH frontier
```

PPW-023 によってこの reduction / representation phase は十分に閉じた。

今後 PPW-024, PPW-025 と同じ branch 上で contour 表現を増やすことは第一選択ではない。

次の branch は「representation」ではなく「independent provider」の探索を目的とする。

---

# 4. PPW-016 以前から確定している finite detector Core

finite zero window に対し、centered zero を

```text
z_rho = rho - 1/2
```

と読む。

主要量:

```text
HorizontalEnergy H_R
  = Σ m_rho * (rho.re - 1/2)^2

RadialSecondMoment Q_R
  = Σ m_rho * |rho - 1/2|^2

CenteredSecondMoment M2_R
  = Σ m_rho * (rho - 1/2)^2
```

exact identity:

```text
2 * H_R
  = Q_R + Re(M2_R)
```

既存 theorem:

```lean
two_mul_pascalCriticalMirrorZeroWindowHorizontalEnergy_eq

pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg

pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff

pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff
```

したがって finite window では

```text
H_R = 0
  iff window 内の全 nontrivial zero が re = 1/2

H_R > 0
  iff window 内に off-critical nontrivial zero が存在
```

これは Green Core。

---

# 5. PPW-021 — one fixed Xi outer contour

module:

```text
DkMath.RH.CFBRC.PascalCenteredXiOuterContourResidueBridge
```

PPW-021 は centered Xi の `-Xi'/Xi` を、一つの boundary-safe outer circle で扱うために一般 residue theorem を仮定せず、明示的な有限 pole subtraction を実装した。

証明機構:

```text
finite principal-part subtraction
→ each pole removable limit
→ finite removable patch
→ patched regularizer continuous on closed disk
→ differentiable off finite zero set
→ Cauchy-Goursat
→ principal-part circle integral
→ outer residue identity
```

generic endpoint:

```text
∮ h(z) * (-Xi_c'(z)/Xi_c(z)) dz
  = -2πi * Σ m_a h(a)
```

normalized form:

```text
(2πi)^(-1) * outer(h,R)
  = - Σ m_a h(a)
```

重要な特殊化:

```text
h = 1
  → multiplicity count

h = z^2
  → negative centered second moment
```

つまり normalized second outer contour は

```text
C2_R = -M2_R
```

を読む。

符号を逆に記憶しないこと。

主要 theorem:

```lean
pascalCenteredXiWeightedOuterContourMass_eq
pascalCenteredXiNormalizedWeightedOuterContourMass_eq
pascalCenteredXiNormalizedOuterContourMass_eq_zeroDiskMultiplicity
pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment
pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re
```

停止条件:

```text
raw totalized regularizer を zero 上で continuous としない。
unsafe radius に residue identity を pointwise 適用しない。
|z|^2 を holomorphic contour weight と扱わない。
```

---

# 6. PPW-022 — radial layer-cake / fixed outer count

module:

```text
DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
```

non-holomorphic radial quantity

```text
Q_R = Σ m_a |a|^2
```

を `|z|^2` の contour weight へ無理に変換せず、zero count の半径積分として再構成した。

finite identity:

```text
Q_R
  = R^2 * N(R)
    - ∫ r in 0..R, 2*r*N(r)
```

ここで fixed Xi outer count:

```lean
noncomputable def pascalCenteredXiOuterCount (r : ℝ) : ℝ :=
  -((2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiOuterContourMass r).re
```

boundary-safe radius では intrinsic multiplicity count と一致。

bounded interval 内の unsafe radius は centered Xi zero の半径からなる有限 exceptional set に含まれる。

したがって layer count と outer count は interval 上で almost everywhere に一致し、interval integral へ移送できる。

最終 endpoint:

```lean
pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake
pascalCriticalMirrorZeroWindowCF2DRadialMass_eq_fixedXiOuterCountLayerCake
```

これにより PPW-017 の zero-dependent mirror-frozen radial weight は最終 theorem surface から消えた。

重要な意味:

```text
Q_R の fixed-Xi representation は完成。
しかし Q_R が 0 になることは何も証明していない。
```

---

# 7. PPW-023 — full fixed Xi second-moment defect

module:

```text
DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
```

## 7.1 fixed radial functional

```lean
noncomputable def pascalCenteredXiFixedRadialSecondMomentFunctional
    (R : ℝ) : ℝ :=
  R ^ 2 * pascalCenteredXiOuterCount R -
    (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r)
```

定義には zero Finset、multiplicity、mirror-frozen weight、`Complex.normSq` を直接含めない。

safe radius では

```text
FixedRadial(R)
  = window radial second moment
  = CF2D radial q2 mass
```

主要 theorem:

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial
pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
```

## 7.2 fixed holomorphic second-contour functional

```lean
noncomputable def pascalCenteredXiFixedHolomorphicSecondContourFunctional
    (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiSecondOuterContourMass R
```

safe radius で

```text
FixedHolomorphicSecondContour(R)
  = - window centered second moment
```

主要 theorem:

```lean
pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq
```

## 7.3 full fixed Xi defect

```lean
noncomputable def pascalCenteredXiFixedSecondMomentDefectFunctional
    (R : ℝ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional R -
    (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re
```

概念的には

```text
D_Xi(R)
  = Q_Xi(R) - Re(C2_Xi(R))
```

かつ `C2_Xi(R) = -M2_R` なので safe radius では

```text
D_Xi(R)
  = Q_R + Re(M2_R)
  = 2 * H_R
```

主要 theorem:

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
pascalCenteredXiFixedSecondMomentDefectFunctional_pos_iff
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff_primeMirrorEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_cf2d_sub_secondContour_re
```

safe radius で確定:

```text
0 ≤ D_Xi(R)

D_Xi(R) = 0
  iff window 内の全 zero が critical

D_Xi(R) > 0
  iff window 内に off-critical zero が存在
```

prime-mirror energy とは quantity equality ではなく zero-condition compatibility のみ。

```text
D_Xi(R) = 0
  iff PrimeMirrorWindowEnergy(n,R) = 0
```

`D_Xi = PrimeMirrorEnergy` と termwise に同一視してはならない。

---

# 8. 最終 frontier property

PPW-023 の中心監査 property:

```lean
def PascalCenteredXiFixedDefectVanishesOnSafeRadii : Prop :=
  ∀ R : ℝ,
    IsPascalCenteredXiBoundarySafeRadius R →
      pascalCenteredXiFixedSecondMomentDefectFunctional R = 0
```

そして Green theorem:

```lean
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔
      RiemannHypothesis
```

## この theorem の意味

証明済み:

```text
FixedDefectVanishesOnSafeRadii → RH
RH → FixedDefectVanishesOnSafeRadii
```

未証明:

```text
FixedDefectVanishesOnSafeRadii
```

従って RH の term はまだない。

新フェーズの唯一の本体は、左辺を RH なしで証明すること。

---

# 9. なぜ boundary-safe condition は未証明仮定ではないか

local outer contour theorem は

```lean
hR : IsPascalCenteredXiBoundarySafeRadius R
```

を要求する。

これは RH 仮定ではない。

意味は outer circle 上に centered Xi zero が乗らないこと。

PPW-020 までに

```lean
exists_isPascalCenteredXiBoundarySafeRadius_gt
```

があり、任意の閾値より大きい safe radius を選べる。

従って global frontier theorem の `vanishing → RH` では、任意の nontrivial zero `rho` に対して

```text
R > dist rho criticalLineCenter
```

となる safe radius を証明済み existence theorem から選択し、その zero を window 内へ入れている。

safe radius の存在を conjecture として仮定しているわけではない。

---

# 10. 新フェーズで証明すべきもの

最終的には次の term が必要。

```lean
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii := by
  intro R hR
  -- independent provider
```

これが Green になれば RH は定型的に閉じる。

```lean
theorem riemannHypothesis : RiemannHypothesis := by
  exact
    pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis.mp
      pascalCenteredXiFixedDefectVanishesOnSafeRadii
```

ただし、第一目標として `D_Xi(R) = 0` を直接狙う必要はない。

既存 Core:

```text
0 ≤ D_Xi(R)
```

よって独立に

```text
D_Xi(R) ≤ 0
```

を証明できれば

```text
0 ≤ D_Xi(R) ≤ 0
```

から `D_Xi(R) = 0` が出る。

新 branch の研究 Gap は実質:

```text
fixed Xi defect の independent upper bound / exact cancellation provider
```

である。

---

# 11. 新 branch 推奨

PPW branch を develop へ merge 後、最新 develop から派生。

推奨:

```text
wip/RH-CFBRC-fixed-xi-defect-provider-260812-v0
```

この名称は vanishing を仮定する branch ではなく、vanishing を生む provider を探す branch であることを示す。

新 branch では PPW numbering を継続しなくてよい。

新しい research roadmap / handoff を別 WIP directory に切るなら候補:

```text
lean/dk_math/DkMath/RH/CFBRC/docs/wip/
  RH-CFBRC-fixed-xi-defect-provider/
```

canonical `docs/000x-*` には WIP research を入れない。

---

# 12. provider 候補三方向

次フェーズでは三方向を候補として監査する。

## Route A — Prime / explicit formula

狙い:

```text
Prime / von Mangoldt / explicit formula
→ fixed Xi defect の独立な別表現
→ upper bound または exact cancellation
```

既に PrimeMirror energy と fixed Xi defect は zero condition が同値。

しかしこれは provider ではない。

必要なのは prime-side から `D_Xi(R)` 自身へ independent inequality / identity を出すこと。

注意:

```text
Li / Weil positivity をそのまま持ち込み、RH-equivalent positivity criterion を再包装しない。
```

explicit formula を使う場合は、どの theorem が unconditional で、どの positivity が RH-equivalent かを先に監査する。

## Route B — CF2D q2 / ThreeElement

既存:

```text
FixedRadial(R) = CF2D radial q2 mass
```

ThreeElement Core には一般に

```text
core = x^2
interaction = 2*x*u
gap = u^2
squareMass = x^2 + u^2
plusWhole = (x+u)^2
minusWhole = (x-u)^2
```

があり、plus/minus whole の共通極限から interaction collapse を得る一般 theorem も完成済み。

しかし RH 応用側で interaction assimilation / difference-whole collapse を直接要求すると RH-equivalent であることは既に監査済み。

従って次に探すなら

```text
fixed Xi defect functional
↔ CF2D / ThreeElement の既存 unconditional conserved quantity
```

という新しい exact identity / inequality でなければならない。

`q2` 保存だけから defect zero は出ない。

## Route C — centered Xi symmetry / moment identity

centered Xi は even で、zero orbit は

```text
z
-z
conj z
-conj z
```

の対称性を持つ。

しかしこの対称性だけでは `Re z = 0` は出ない。

したがって単なる mirror pairing や second moment cancellation を provider と誤認しない。

必要なのは、fixed Xi functional に対して新しい unconditional moment identity / sign constraint が存在するかの監査。

---

# 13. 最重要 stop conditions

新しい会話では以下を常に守る。

```text
1. RiemannHypothesis と同値な property を名前だけ変えて provider と呼ばない。

2. PascalCenteredXiFixedDefectVanishesOnSafeRadii は既に RH と同値。
   これを「弱い補題」として仮定しない。

3. safe radius R で 0 ≤ D_Xi(R) は Green。
   必要なのは independent upper bound / cancellation。

4. |z|^2 を holomorphic contour weight と扱わない。
   radial side は layer-cake route が正本。

5. unsafe radius で pointwise residue identity を使わない。
   bounded unsafe radii は finite exceptional set / a.e. transport で処理済み。

6. scalar contour cancellation から coordinatewise zero を導かない。

7. vector sum zero から sum of coordinate energies zero を導かない。

8. CF2D q2 保存だけから beam / horizontal defect zero を導かない。

9. Xi の evenness / mirror symmetryだけから off-critical pair が merge すると結論しない。

10. PrimeMirror energy と FixedXiDefect は zero condition が同値だが quantity equality ではない。

11. numerical visualization / phase bundle / drift observation を exact theorem と扱わない。

12. moving-line / ThreeElement 系の RH-equivalent final contracts を独立 provider として再利用しない。

13. 新しい theorem が D_Xi(R)=0 を結論するなら、その仮定群が RH を暗黙に含まないか先に iff audit する。

14. RH の完成を主張するのは RiemannHypothesis の term が sorry / axiom なしで構成されたときだけ。
```

---

# 14. 既存 A 系との関係

Prime/Pascal/Xi 系とは別に、以前から Eta / Moving-Line / ThreeElement 系がある。

その系列は RH を

```text
最後の transverse / interaction collapse
```

まで縮約済みだが、最終 contract 自体が RH-equivalent と監査されている。

代表的 beacon:

```lean
etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_research_goal
```

および

```lean
etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_iff_riemannHypothesis
```

このため、A 系へ戻って RH-equivalent collapse を直接証明しようとするのは新しい independent provider にはならない。

ただし、新しい fixed Xi scalar defect と A 系の unconditional conserved quantity の間に本当に新しい exact bridge が見つかるなら Route B の候補になる。

---

# 15. 今回の会話で確定した研究判断

この会話の最後に合意した判断:

```text
PPW phase は PPW-023 で一旦閉じる。

current PPW branch を Green checkpoint として develop へ merge。

merge 後、新 branch を切る。

新 branch では
  PascalCenteredXiFixedDefectVanishesOnSafeRadii
の independent proof provider にのみ集中する。
```

理由:

```text
「RH を何へ還元するか」は十分に形式化できた。
これ以上 representation layer を増やすより、
その exact scalar frontier を独立に constrain する数学が必要。
```

---

# 16. 新会話で最初に確認する GitHub 項目

新しい会話では repo を読まずに過去記憶だけで続行しない。

最初に GitHub で次を確認する。

```text
A. wip/RH-CFBRC-prime-mirror-energy-260807-v0 の current head

B. 58272bd1ff20e3848cbb25f7d0c4def54bcda985 以降に追加 commit があるか

C. PPW branch が develop へ merge 済みか

D. develop の latest head

E. PascalCenteredXiFixedSecondMomentDefectBridge.lean が develop から公開 import されているか

F. 新 branch
   wip/RH-CFBRC-fixed-xi-defect-provider-260812-v0
   が既に存在するか
```

merge 済みなら current PPW branch では作業を続けず、latest develop から provider branch を使う。

---

# 17. 新フェーズの最初の ROADMAP

最初から大きな proof を書かず、provider candidate audit を Core として残す。

```text
Gate 0
  branch / develop / public import / build Green 確認

Gate 1
  FixedXiDefect の exact unfolded formula と利用可能 API を再監査

Gate 2A
  Prime / explicit formula candidate audit

Gate 2B
  CF2D / ThreeElement candidate audit

Gate 2C
  centered Xi symmetry / moment candidate audit

Gate 3
  RH-equivalence contamination audit

Gate 4
  independent inequality / identity candidate を Lean theorem 化

Gate 5
  safe R で D_Xi(R) ≤ 0 または D_Xi(R)=0

Gate 6
  PascalCenteredXiFixedDefectVanishesOnSafeRadii

Gate 7
  RiemannHypothesis
```

Gate 2 のどれかが「実は RH と同値」と判明した場合、その経路を obstruction theorem / audit として記録し、別候補へ移る。

---

# 18. 理想的な最終 Lean closure

provider theorem の理想形は例えば次。

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_nonpos
    {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R ≤ 0 := by
  -- independent mathematics only
```

既存 nonnegative theorem と合成:

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_independent
    {R : ℝ}
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0 := by
  have hnonneg :=
    pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg hR
  have hnonpos :=
    pascalCenteredXiFixedSecondMomentDefectFunctional_nonpos hR
  exact le_antisymm hnonpos hnonneg
```

全 safe radii:

```lean
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii := by
  intro R hR
  exact pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_independent hR
```

最後:

```lean
theorem riemannHypothesis : RiemannHypothesis := by
  exact
    pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis.mp
      pascalCenteredXiFixedDefectVanishesOnSafeRadii
```

もちろん `nonpos` はまだ存在しない。ここが research frontier。

---

# 19. 一行 checkpoint

```text
PPW-001 ... PPW-023:
  Prime / Pascal / Xi / contour / radial / CF2D reduction COMPLETE GREEN

Final formal frontier:
  PascalCenteredXiFixedDefectVanishesOnSafeRadii

Green theorem:
  PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔ RiemannHypothesis

Missing theorem:
  PascalCenteredXiFixedDefectVanishesOnSafeRadii

Known one-sided sign:
  safe R → 0 ≤ FixedXiDefect(R)

Next research target:
  independent upper-bound / exact-cancellation provider

Next branch after PPW merge:
  wip/RH-CFBRC-fixed-xi-defect-provider-260812-v0
```

---

# 20. 賢狼メモ

この段階では「RH がほぼ証明できた」と表現しない。

正確な評価は:

```text
RH と同値な final scalar vanishing problem まで、
Prime/Pascal/Xi/contour/CF2D の既証明構造だけで無条件に reduction できた。

しかしその scalar vanishing 自体はまだ未証明。
```

次の会話では、過去の長い contour plumbing を再開しない。

問いは一つ。

```text
なぜ fixed centered-Xi defect は、RH を使わずに 0 でなければならないのか？
```

あるいは等価に、既に nonnegative なので、

```text
なぜ fixed centered-Xi defect は、独立構造から nonpositive でもあるのか？
```

この問いだけを追う。
