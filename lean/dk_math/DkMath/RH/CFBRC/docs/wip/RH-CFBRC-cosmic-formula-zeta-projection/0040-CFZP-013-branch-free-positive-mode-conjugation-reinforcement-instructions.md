# CFZP-0040 / CFZP-013 reinforcement
## branch-free positive-mode conjugation proof replacement — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段 implementation:

`f91e6f28e8f94513c3d76ab2a63a28b22aec4e77`

対象 module:

`DkMath.RH.CFBRC.CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit.lean`

---

## 0. 目的

CFZP-013 の数学的 theorem surface は維持する。
今回の補強は Gate B の theorem

```lean
cfzp013PrimePowerMode_rightEdge_neg_eq_conj
```

の proof route だけを branch-free route へ置換する。

現実装は `Complex.cpow_conj` の side condition を処理するため
`Complex.arg` を局所使用している。しかし 0039 instruction は positive real
base の構造だけを使い、branch-sensitive `Complex.arg` や新しい global
logarithm convention を導入しないことを要求していた。

したがって現時点の CFZP-013 は数学的には Green だが project firewall 上は
Green-B reinforcement とみなし、本補強が Green になった時点で Green-A に戻す。

新しい研究仮説、provider、baseline collapse、無限極限、RH は追加しない。

---

## 1. Gate R1 — theorem statement を維持

原則として theorem statement を変更しない。

```lean
/-- A positive prime-power mode reverses height by complex conjugation. -/
theorem cfzp013PrimePowerMode_rightEdge_neg_eq_conj
    {p k : ℕ} (_hp : Nat.Prime p)
    (W : PascalCenteredXiResidueTransportWindow) (t : ℝ) :
    (((p ^ (k + 1) : ℕ) : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)))) =
      conj (((p ^ (k + 1) : ℕ) : ℂ) ^
        (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))) := by
  ...
```

`_hp` を実際に使う形へ rename してよい。

---

## 2. Gate R2 — `Complex.arg` / `Complex.cpow_conj` route を除去

現 proof の以下の構造を削除する。

```lean
have harg : ... .arg ≠ Real.pi := ...
have hcpow := Complex.cpow_conj ... harg
```

本 module に新規 `Complex.arg` を残さない。
`Complex.cpow_conj` の branch side condition を回避するために別の branch
predicate を導入するのも避ける。

---

## 3. Gate R3 — 第一候補: positive natural base の explicit exponential route

CFZP-001 が既に用いている branch-free finite positive-base route を優先する。

概念的には `q := p ^ (k + 1)` として、`q > 0` から complex cast の nonzero を得て、
両辺の `cpow` を

```lean
Complex.cpow_def_of_ne_zero
```

で展開し、positive natural base の logarithm を既存の

```lean
Complex.natCast_log
```

へ落とす。

その後、right-edge coordinate

```text
s_R(-t) = conj(s_R(t))
```

と、real `log q` による exponential expression を使い、

```text
exp(-log(q) * conj(s_R(t)))
  = conj(exp(-log(q) * s_R(t)))
```

を `Complex.exp` の conjugation compatibility から閉じる。

proof の細部は Mathlib v4.33.0 API に合わせてよい。例えば `map_exp`、
`Complex.exp_conj` 相当の既存 simp theorem、`Complex.ext` 等を使ってよい。

重要:

- `Complex.arg` を使わない。
- global `Complex.log` branch の新規 convention を導入しない。
- base は positive natural number なので、その real logarithmだけを利用する。
- theorem statement の数学的意味を弱めない。

---

## 4. Gate R4 — 第二候補: CFZP-001 factorization route

R3 が Lean API 上で不自然なら、既存

```lean
natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle
cfzpPrimePowerCycleState
```

を使う route でもよい。

right-edge `t` と `-t` は real coordinate が同じなので left amplitude は同じ real
factor、cycle state は explicit `Complex.exp` 定義から conjugate pair になる。
common radial factor についても positive natural base / real exponent の real-valued
性だけを使う。

この route でも `Complex.arg` を導入しない。

不要な一般 theorem を大量追加せず、必要なら局所 helper または再利用可能な小 theorem
を最小限追加する。

---

## 5. Gate R5 — downstream theorem を変更しない

以下の CFZP-013 surface は同じ theorem statement のまま Green を維持する。

- `cfzp013RightSourceSummand_neg_eq_conj`
- `cfzp013FinitePrimePowerRayAmplitude_neg_eq_conj`
- `cfzp013WeightConjugationSkew_conj_eq_neg`
- `cfzp013WeightConjugationSkew_re_eq_zero`
- `cfzp013WeightConjugationSkew_eq_two_mul_I_mul_im`
- `cfzp013ReweightedReversedRightRay_sub_actualRightRayAtNeg_eq_skew_mul_bareSum`
- `cfzp013SameHeightMirrorRay_sub_one_eq_functional_add_conjRightResidual_add_skew`
- `cfzp013ConjRightRayResidual_normSq_eq`
- `Cfzp013FunctionalReflectionSkewInterferenceClosureGap`

self-recurrence decomposition の数学的内容を変更しない。

---

## 6. Gate R6 — roadmap classification

repair 後は roadmap の CFZP-013 Green-A classification を維持してよい。
必要なら短く、Gate B proof が branch-free positive-base exponential route に補強されたことを
追記する。

repair に失敗して `Complex.arg` を残す場合は Green-A と記録せず、Green-B reinforcement
pending とする。

---

## 7. Firewall

本補強では以下を禁止する。

- 新規 `Complex.arg`
- 新規 global `Complex.log` branch convention
- continuous phase / unwrap / zero-counting
- baseline collapse
- `amplitude Gap = ray-minus whole`
- infinite cutoff exchange
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

`Complex.cpow_def_of_ne_zero` と positive-natural-base logarithm identity は利用してよい。

---

## 8. Green suite

最低限:

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit.lean
lake build DkMath.RH
git diff --check
```

加えて対象 module を監査し、少なくとも新規明示使用として

```text
Complex.arg
sorry
admit
axiom
native_decide
```

が無いことを確認する。

可能なら通常の full suite も実行する。

---

## 9. 完了条件

次をすべて満たしたら CFZP-013 を Green-A に戻す。

1. `cfzp013PrimePowerMode_rightEdge_neg_eq_conj` の statement が維持される。
2. proof から `Complex.arg` が除去される。
3. downstream self-recurrence theorem 群がそのまま Green。
4. `DkMath.RH` が Green。
5. firewall 違反なし。
6. 新しい数学的仮説や provider を追加していない。

この補強完了後に初めて CFZP-014 の研究方向を選ぶ。候補は
Layer 2 finite weighted Gram/interference、CS37/CS38 aggregate transport、
または CFZP-009 common-baseline finite/cofinal reach の再評価である。
