# CFZP-0033 — CFZP-009 common-baseline alignment reach / quantifier audit 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-008
- Expected parent commit: `d598da41ced536dd2bf373f91c4a3563df354188`
- 日本語を正本とする。

CFZP-008 は Green-A closeout とする。

008 で critical-line の projective doubled-phase normalization は exact に閉じた。

```text
zetaUnit(t)^2 = conj(GammaRUnit(t))^2
```

これは OOL-KND の historical doubled-phase carrier を branch-free に説明するが、006Z で残った source-side backlog

```text
CommonBaselineDefect_X = 0
amplitude Gap -> ray-minus whole
```

へ直接入る theorem は現時点で存在しない。

したがって phase investigation はここで一旦終了し、009 から source-side backlog へ戻る。

ただし 009 では `CommonBaselineDefect_X = 0` を universal finite identity として要求しない。
まず、その equality がどの量化で意味を持つのかを Lean 上で監査する。

---

## 1. 009 の中心発見

006Z では

```text
D_X := G_0 - C_X
```

を common-baseline defect と定義した。

CS25 には exact に

```text
Eplus_X  = C_X + I_X
Eminus_X = C_X - I_X
```

がある。

よって純代数的に

```text
C_X = (Eplus_X + Eminus_X) / 2
```

である。

したがって defect は

```text
D_X
  = G_0 - C_X
  = G_0 - (Eplus_X + Eminus_X)/2
```

と読める。

つまり alignment `D_X = 0` は

```text
zero-cutoff baseline G_0
  = average of the two nonnegative ray whole masses
```

という **finite reach condition** である。

これは prime event の monotonicity を必要としない。

さらに CS24 には

```text
Eplus_0  = 0
Eminus_0 = 0
```

が既にある。

したがって common energy も `C_0 = 0` となり、

```text
D_0 = G_0
```

である。

よって `forall X, D_X = 0` という universal finite alignment は、少なくとも `G_0 = 0` を強制する。

009 はこの事実を first-class theorem として固定し、alignment の正しい frontier を

```text
finite reach / possible cofinal reach
```

へ再分類する。

---

## 2. 009 の出口条件

009 は一つの module で次を exact に閉じる。

```text
Eplus_X = C_X + I_X
Eminus_X = C_X - I_X
          ↓
C_X = (Eplus_X + Eminus_X)/2
          ↓
D_X = G_0 - (Eplus_X + Eminus_X)/2
          ↓
D_X = 0 iff C_X = G_0
          iff Eplus_X + Eminus_X = 2*G_0
```

さらに cutoff zero で

```text
C_0 = 0
D_0 = G_0
```

を証明し、

```text
(forall X, D_X = 0) -> G_0 = 0
G_0 != 0 -> not (forall X, D_X = 0)
```

を公開する。

そして finite alignment を universal identity ではなく

```text
exists X, C_X = G_0
```

という reach problem として first-class にする。

存在自体は証明しなくてよい。

---

## 3. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCommonBaselineAlignmentReachAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCommonBaselineAlignmentReachAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
import Mathlib.Tactic
```

不要な解析 import を増やさない。

---

## 4. Gate A — common energy as average whole mass

既存 CS25 の

```lean
pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
```

から exact に

```text
2 * C_X = Eplus_X + Eminus_X
```

および

```text
C_X = (Eplus_X + Eminus_X) / 2
```

を証明する。

推奨 theorem:

```lean
cfzp009_two_mul_commonEnergy_eq_plusEnergy_add_minusEnergy
cfzp009_commonEnergy_eq_plusEnergy_add_minusEnergy_div_two
```

両 whole energy は既存 theorem により nonnegative。
可能ならこの式から

```text
0 <= C_X
```

も公開する。

既存に同値 theorem がある場合は再証明せず adapter にする。

---

## 5. Gate B — defect の polarized whole-mass form

006Z の

```lean
cfzp006CommonBaselineDefect
```

を使い、exact に

```text
D_X = G_0 - (Eplus_X + Eminus_X)/2
```

を公開する。

推奨 theorem:

```lean
cfzp009CommonBaselineDefect_eq_zeroCutoff_sub_averageWholeEnergy
```

さらに

```text
D_X = 0 iff C_X = G_0
D_X = 0 iff Eplus_X + Eminus_X = 2 * G_0
```

を theorem にする。

order version も安価なら追加する。

```text
0 <= D_X iff C_X <= G_0
D_X <= 0 iff G_0 <= C_X
```

ここでは `G_0` の sign は仮定しない。

---

## 6. Gate C — cutoff-zero audit

既存 CS24 には

```lean
pascalCenteredXiPrimeSideAggregateRayPlusEnergy_zero
pascalCenteredXiPrimeSideAggregateRayMinusEnergy_zero
```

がある。

Gate A と組み合わせて

```text
C_0 = 0
```

を exact に証明する。

推奨:

```lean
cfzp009AggregateRayCommonEnergy_zero
```

その結果

```text
D_0 = G_0
```

を公開する。

推奨:

```lean
cfzp009CommonBaselineDefect_zeroCutoff
```

これは重要な quantifier audit である。

---

## 7. Gate D — universal alignment は一般の finite identity ではない

cutoff-zero theorem から

```text
(forall X : Nat, D_X = 0) -> G_0 = 0
```

を証明する。

逆向きは主張しない。

また

```text
G_0 != 0 -> not (forall X : Nat, D_X = 0)
```

を公開する。

推奨:

```lean
cfzp009_universalCommonBaselineAlignment_implies_zeroCutoffDeficit_eq_zero
cfzp009_zeroCutoffDeficit_ne_zero_excludes_universalCommonBaselineAlignment
```

この theorem により 009 以降で

```text
forall X, D_X = 0
```

を目標にしないことを明示する。

`G_0 != 0` 自体は今回証明不要。

---

## 8. Gate E — finite alignment reach を first-class にする

定義候補:

```lean
def CfzpCommonBaselineReachedAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : Prop :=
  pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X =
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0
```

名称は repository style に合わせてよい。

必須 equivalence:

```text
ReachedAt X iff D_X = 0
ReachedAt X iff Eplus_X + Eminus_X = 2 * G_0
```

006Z と接続して、rectangle hypotheses の下では

```text
ReachedAt X
  iff CompletionRemainder_X = Eminus_X / pi
```

も adapter として公開してよい。

さらに existential reach を first-class にする。

```text
exists X, ReachedAt X
  iff exists X, D_X = 0
```

これは存在証明ではなく、問題の正しい statement への再包装である。

---

## 9. Frontier marker

009 で有限 reach の存在を仮定・証明しない。

推奨 marker:

```lean
inductive CfzpCommonBaselineFiniteOrCofinalReachGap : Prop
  | noIndependentCommonEnergyBaselineReachProvider
```

必要ならコメントで、今後の候補を

```text
finite exact reach
or
cofinal/limit alignment
```

と記録する。

まだ limit theorem は実装しない。

特に common energy の monotonicity は主張しない。

---

## 10. 009 の大局的役割

008 までで phase / OOL normalization は独立に Green-A となった。

009 は source projection の本線へ戻り、006Z の `D_X = 0` を

```text
mysterious universal identity
```

から

```text
finite polarized common-mass reach condition
```

へ正しく分類し直す。

009 Green 後に残る本丸は主として

```text
1. common-baseline finite/cofinal reach provider
2. amplitude-side Gap -> source ray-minus whole exact projection
```

である。

次段階では 009 の結果を見て、この二つのうちどちらが source observable 同一性に対して先行すべきか再判定する。

---

## 11. Firewall

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- OOL real-angle unwrap の追加研究
- prime event / common energy の無条件 monotonicity
- `forall X, D_X = 0` の無根拠な provider 化
- finite reach の存在仮定を structure field で注入
- cofinal limit の未証明交換
- infinite Euler product
- zeta-zero / RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

既存 theorem からの有限実代数・Finset・nonnegative whole-mass algebra を中心に閉じる。

---

## 12. Public surface / build

新規 module を `DkMath/RH.lean` に公開 import する。

最低 Green suite:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaCommonBaselineAlignmentReachAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規ファイルについて禁止語監査も行う。

ROADMAP 末尾に以下を追記する。

```text
CFZP-008 Green-A closeout:
projective doubled-phase / OOL normalization は branch-free に exact 化され、phase investigation は一旦完了。

CFZP-009:
common-baseline defect を universal finite identity ではなく polarized whole-mass baseline reach problem として再分類。
```

---

## 13. Green-A 判定

次を満たせば Green-A。

1. 新規 module + public import。
2. `C_X = (Eplus_X + Eminus_X)/2` exact。
3. `D_X = G_0 - (Eplus_X + Eminus_X)/2` exact。
4. alignment iff common energy reaches `G_0` exact。
5. alignment iff whole-mass sum reaches `2*G_0` exact。
6. `C_0 = 0` exact。
7. `D_0 = G_0` exact。
8. universal alignment -> `G_0 = 0` exact。
9. `G_0 != 0` excludes universal alignment exact。
10. finite reach predicate / equivalence first-class。
11. no monotonicity / reach existence / limit / zeta-zero / RH claim。
12. local Green suite clean。

この checkpoint は reach を証明する段階ではない。
**何を証明すべきかの量化を Lean 上で正しく固定する段階**である。
