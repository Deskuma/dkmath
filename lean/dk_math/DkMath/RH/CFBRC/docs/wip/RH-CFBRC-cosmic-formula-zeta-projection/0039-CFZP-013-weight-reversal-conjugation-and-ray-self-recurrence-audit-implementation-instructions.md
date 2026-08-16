# CFZP-0039 / CFZP-013

## weight-reversal conjugation and ray self-recurrence audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-011: same-height mirror/source mode transform — Green-A
- CFZP-012: mirror-baseline functional-reflection height-reversal audit — Green-A candidate

本段の目的は、CFZP-012 で明示した `Cfzp012WeightReversalConjugationGap` を、
`τ = 0` の実際の Mellin weight と positive natural mode の complex conjugation
を使って exact に監査し、`Z_M - 1` が元の right-ray residual の conjugate copy
を含む self-recurrent observable であるかを確定することにある。

ここでは baseline collapse、sign provider、infinite cutoff exchange、RH、
`amplitude Gap = ray-minus whole` を導入しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization`
- 必要なら `DkMath.Analysis.MellinMultiplicativeApproxIdentity`
- `Mathlib.Tactic`

既存 API を優先し、不要な再定義を避ける。

---

## 2. Gate A — `τ = 0` Mellin weight の conjugation law

CFZP source ray が使う weight は

```lean
pascalCenteredXiMellinSecondDifferenceWeight ε 0
```

である。

まず `0 < ε` の下で、少なくとも次の pointwise real-structure law を証明する。

```lean
pascalCenteredXiMellinSecondDifferenceWeight ε 0 (conj z)
  = conj (pascalCenteredXiMellinSecondDifferenceWeight ε 0 z)
```

証明 route は自由だが、既存の

```lean
pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
```

を使う route を第一候補とする。

box approximation は real parameter 上の symmetric logarithmic average なので、
complex conjugation と Bochner / interval integral の交換を exact に処理する。
既存 `integral_conj` 等が利用できるなら再証明しない。

重要:

- `PascalCenteredEvenWeight` は `h (-z) = h z` であり、今回の
  `h (conj z) = conj (h z)` とは別 theorem である。
- evenness だけで Gate A を済ませない。
- global `Complex.log` branch を新規に導入しない。

次に CFZP-012 の

```lean
cfzp012ModePhaseNode_neg_eq_conj
```

と接続し、

```lean
weight (node (-t)) = conj (weight (node t))
```

を theorem として出す。

---

## 3. Gate B — positive natural mode の height-reversal conjugation

right-edge point

```lean
sR(t) := pascalSymmetricRectangleRightEdge W.rectangle.σ t
```

に対し、positive natural base `q > 0` について

```text
q^(-sR(-t)) = conj (q^(-sR(t)))
```

を exact に証明する。

prime-power 版を直接使いやすい形で出してよい。

```lean
{p k : ℕ} (hp : Nat.Prime p)
```

または base positivity だけで十分なら一般化してよい。

positive real base の `cpow` であることを使い、branch-sensitive `Complex.arg`
や新しい global logarithm convention を導入しない。

---

## 4. Gate C — source summand / finite right ray の conjugation

Gate A/B を掛け合わせ、actual source summand について

```text
rightSourceSummand(-t) = conj(rightSourceSummand(t))
```

を証明する。

既存 exponent support は `t` に依存しないので、その有限和まで持ち上げて

```text
Z_R(-t) = conj(Z_R(t))
```

を exact にする。

推奨 theorem shape:

```lean
pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p (-t)
  = conj (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t)
```

必要な仮定は最小化する。`0 < ε` と `Nat.Prime p` が自然なら明示する。

---

## 5. Gate D — CFZP-012 weight correction の sharp rewrite

CFZP-012 は

```text
reweightedReversedRightRay(t) - actualRightRay(-t)
```

を weight mismatch の有限和として exact にした。

Gate A/C を使って、この correction を少なくとも次の shape に rewrite する。

```text
(weight(t) - conj(weight(t)))
  * finiteBareReversedModeSum(t)
```

既存 geometric core がそのまま使えるなら利用する。難しい場合は有限 bare sum を
本 module 内で named definition として置いてよい。

weight skew を first-class にするなら、例えば

```lean
noncomputable def cfzp013WeightConjugationSkew (...) : ℂ :=
  weightAt t - conj (weightAt t)
```

とし、exact に

```text
conj(skew) = -skew
Re(skew) = 0
```

を証明する。

可能なら

```text
skew = 2 * I * Im(weightAt t)
```

まで出してよい。

ただし `skew = 0` は主張しない。一般の right-edge centered node は実軸上ではない。

---

## 6. Gate E — mirror baseline residual の self-recurrent decomposition

CFZP-012 の

```text
Z_M - 1
  = functionalReflectionPart
  + (reweightedReversedRightRay - 1)
```

に Gate C/D を代入して、少なくとも次を exact にする。

```text
Z_M(t) - 1
  = functionalReflectionPart(t)
  + (conj(Z_R(t)) - 1)
  + weightSkewCorrection(t)
```

括弧や加法順序は Lean で扱いやすい形でよい。

さらに algebraic companion として

```text
normSq (conj(Z_R(t)) - 1) = normSq (Z_R(t) - 1)
```

を証明する。

これにより、mirror baseline residual が「未知 baseline の単独量」ではなく、
元の ray-minus residual の conjugate copy を exact に内包することを明示する。

ここから

```text
normSq(Z_M - 1) = normSq(Z_R - 1)
```

を推論してはならない。functional-reflection part と skew correction、および
それらの interference が残る。

---

## 7. Gate F — frontier の再分類

CFZP-012 の marker を単純に「解消」と書かず、結果に応じて再分類する。

Gate A〜E が Green なら、例えば新 marker:

```lean
inductive Cfzp013FunctionalReflectionSkewInterferenceClosureGap : Prop
  | noFunctionalReflectionSkewInterferenceClosureProvider
```

を置く。

roadmap には次を明記する。

```text
CFZP-012 weight-reversal classification:
  conjugation law: CLOSED
  actual right-ray height reversal: CLOSED
  weight mismatch: IDENTIFIED as pure-imaginary skew correction

mirror baseline residual:
  contains functional-reflection contribution
  + conjugate copy of the original right-ray residual
  + explicit skew correction
```

したがって direct baseline collapse は得られていない。

---

## 8. Hard exit

以下が Green なら CFZP-013 はそこで閉じる。

1. `τ = 0` Mellin weight conjugation law。
2. positive natural mode の height-reversal conjugation。
3. source summand / finite right ray の conjugation。
4. CFZP-012 correction の weight-skew rewrite。
5. `Z_M - 1` の functional + conjugate-right-residual + skew decomposition。
6. conjugate right residual と original ray-minus の `normSq` equality。
7. 未解決部分を functional/skew/interference frontier として明示。

`013A`, `013B` の連番には入らない。

013 完了後に改めて theorem graph を監査し、

- Layer 2 finite Gram/interference aggregate transport へ進むか、
- CFZP-009 common-baseline finite/cofinal reach へ戻るか、
- functional-reflection contribution の既存 CS37/CS38 aggregate API への transport が
  一段で閉じるならそこだけ先に閉じるか

を判定する。

---

## 9. Firewall

- 新規 `Complex.arg` 禁止。
- branch-sensitive global `Complex.log` 導入禁止。
- infinite Euler product を導入しない。
- `X → ∞` をこの段で使わない。
- RH conclusion を導入しない。
- `normSq (sum) = sum normSq` を使わない。
- conjugation invariance から sign / cancellation を推論しない。
- source ray-minus と amplitude Gap の direct equality を復活させない。

---

## 10. Public surface / verification

実装後:

1. `DkMath/RH.lean` に公開 import。
2. `0000-CFZP-roadmap.md` に CFZP-013 結果を追記。
3. focused build。
4. `lake build DkMath.RH`。
5. 可能なら `./lean-build.sh`, `./lean-test.sh`。
6. `git diff --check`。
7. 新規ファイルの `sorry`, `admit`, `axiom`, `native_decide`, `Complex.arg` 監査。

ローカル Lean Green を正本とする。
