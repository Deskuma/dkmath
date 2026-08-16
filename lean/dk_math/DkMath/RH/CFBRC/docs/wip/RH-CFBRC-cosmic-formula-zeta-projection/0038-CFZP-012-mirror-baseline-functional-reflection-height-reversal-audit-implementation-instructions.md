# CFZP-0038 / CFZP-012 — mirror-baseline functional-reflection height-reversal audit implementation instructions

## 0. 作業対象

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

Parent implementation commit: `bb4df35e64da725af442d1f299454be0473f6c31`

CFZP-011 で Layer 1 は Green-A / CLOSED となった。

新規 module の推奨名:

`DkMath.RH.CFBRC.CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit`

推奨 path:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit.lean`

実装後は `DkMath/RH.lean` に public import を追加し、`0000-CFZP-roadmap.md` に CFZP-012 の結果と frontier classification を追記する。

## 1. 背景

CFZP-011 は finite right ray を `Z_R`、same-height mirror ray を `Z_M` と見たとき、

```text
Z_R - 1 = (Z_R - Z_M) + (Z_M - 1)
```

および `normSq` の interference 展開を exact に固定した。

Layer 1 では各 prime-power mode に対して

```text
mirrorSourceSummand - rightSourceSummand
  = MellinWeight * sameHeightMirrorModeDifference
```

が証明済みである。

残る `Z_M - 1` を CFZP-009 の common baseline defect や CS25 common energy と名前だけで同一視してはならない。CS25 common energy は right-ray state `Z_R` に対する `normSq Z_R + 1` の積分・集約であり、`Z_M` 自体は別 observable である。

一方、right edge を

```text
s_R(t) = sigma + i t
```

と書けば、critical mirror の定義から有限代数として

```text
criticalMirror (s_R(t)) = 1 - s_R(-t)
```

が成立する。

したがって same-height mirror は functional reflection `s -> 1 - s` の height-reversed 版として監査できる。CFZP-012 の目的は、この exact relation を source summand / finite ray / baseline residual まで運び、`Z_M - 1` が既存 functional-reflection channel とどこまで一致し、どこから追加 correction が残るのかを確定することである。

## 2. 必須 Gate A — coordinate height-reversal identity

まず既存の `criticalMirror` と `pascalSymmetricRectangleRightEdge` を用いて、少なくとも次の exact coordinate identity を証明する。

```lean
criticalMirror (pascalSymmetricRectangleRightEdge W.rectangle.σ t) =
  1 - pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)
```

同値な補題名・statement shape でもよい。

新しい phase branch、`Complex.arg`、global `Complex.log` は導入しない。

## 3. 必須 Gate B — height-reversed functional-reflection mode decomposition

`q > 0` または prime-power mode に対して、CFZP-005 の既存

`cfzpFunctionalReflectionModeDifference`

を再利用し、same-height mode difference を height-reversed functional-reflection difference と vertical displacement に exact 分解する。

狙う algebraic shape は次である。

```text
sameHeightMirrorModeDifference(q, s_R(t))
  = functionalReflectionModeDifference(q, s_R(-t))
    + (q^(-s_R(-t)) - q^(-s_R(t)))
```

符号は既存定義に合わせて Lean で確認すること。単なる `ring` で閉じる場合も、既存 CFZP-005 observable 名を theorem surface に残す。

この Gate により、same-height mirror source と functional-reflection source の差が「height reversal / vertical cycle displacement」に局在することを明示する。

## 4. 必須 Gate C — Mellin-weighted summand transport

CFZP-011 の `cfzp011SameHeightMirrorSourceSummand` と既存 right source summandを用いる。

必要なら「weight は時刻 `t` のまま、mode だけ `s_R(-t)` に置いた」補助 summand を定義してよい。たとえば概念的には

```text
reweightedReverseRight(q,t)
  := weight(t) * q^(-s_R(-t))
```

である。

その上で、mirror source summand と reweighted reversed-right summand の差が

```text
weight(t) * functionalReflectionModeDifference(q, s_R(-t))
```

になる exact theorem を作る。

さらに same-height mirror/right differenceを

```text
weighted functional-reflection part
+ weighted vertical displacement part
```

へ分解する。

ここでは `weight(t) = weight(-t)` を仮定してはならない。

## 5. 必須 Gate D — finite ray transport

CFZP-011 と同じ finite exponent support 上で Gate C を有限和へ持ち上げる。

少なくとも、finite mirror ray `Z_M(t)` が

```text
height-reversed functional-reflection contribution
+ reweighted reversed-right ray
```

の形に exact 分解できる surface を用意する。

また baseline residual を

```text
Z_M(t) - 1
  = functional-reflection contribution
    + (reweighted reversed-right ray - 1)
```

の形へ exact に局在化する。

この段階で `Z_M - 1 = 0` や sign / positivity を主張しない。

## 6. Gate E — weight reversal / conjugation audit

ここは「証明できる strongest exact statement」を採用する。

まず repository 内に

- `pascalCenteredXiMellinSecondDifferenceWeight` の conjugation theorem
- `tau = 0` での `t -> -t` symmetry
- centered mode node の conjugation

に関する既存 lemma がないか確認し、あれば必ず再利用する。

既存 API または短い branch-free proof だけで

```text
weight(-t) = conj(weight(t))
```

のような theorem が得られるなら formalize してよい。

その場合、positive natural base の cpow conjugationと組み合わせて actual right ray の height reversal / conjugation relation、および必要なら

```text
normSq (Z_R(-t) - 1) = normSq (Z_R(t) - 1)
```

まで証明してよい。

ただし conjugation theorem が既存 API から安全に得られない場合は、ここを無理に開拓しない。新しい `Complex.log` branch や argument branchを作ってまで証明しないこと。その場合は weight-reversal correction を explicit frontier として残す。

## 7. Gate F — correction classification

可能なら、reweighted reversed-right ray と actual right ray at `-t` の差を explicit にする。

概念的には

```text
reweightedReverseRight(t) - rightRay(-t)
```

が weight mismatch にのみ由来することを finite sum level で表す。

共通 weight を有限和から factor できる場合、既存 geometric core / finite ray API を再利用する。新しい無限和は作らない。

この Gate の目的は `Z_M - 1` を次のどちらかに分類することである。

1. 既存 functional-reflection source + conjugate/right-ray residualへ exact に還元できる。
2. functional-reflection source + explicit weight-reversal correction + right-ray residualまでしか還元できない。

どちらでも Green-A になり得る。重要なのは residual の正体を exact に分類することであり、collapse を捏造しないことである。

## 8. Hard exit

CFZP-012 は次を達成した時点で CLOSED とする。

- `criticalMirror(s_R(t)) = 1 - s_R(-t)` が exact。
- same-height mirror mode が height-reversed functional-reflection mode + vertical displacement に exact 分解された。
- Mellin-weighted summand / finite rayへ輸送された。
- `Z_M - 1` が functional-reflection contribution と reversed-right residual/correction に exact 局在化された。
- weight reversal が証明可能なら exact conjugation surfaceを追加し、無理なら明示 marker を残した。

ここから 012A, 012B ... と phase を無限に掘らない。

012 が Green になった後、次の戦略判断は次の二択とする。

- residual が既存 CS37/38 / completed source geometry と十分強く接続したなら、その exact bridge を source-side closeoutへ戻す。
- そうでなければ Layer 3 は explanatory decomposition として閉じ、Layer 2 の finite weighted Gram/interference transportへ戻る。

## 9. 禁止事項 / firewall

- `Complex.arg` を導入しない。
- 新しい global `Complex.log` branch を導入しない。
- infinite Euler productを導入しない。
- cutoff `X -> infinity` を導入しない。
- finite sum / integral exchangeを新規に正当化しない。
- `normSq (sum modes) = sum normSq modes` を使わない。
- `Z_M - 1` を CFZP-009 common baseline defectと rename しない。
- common-energy reach providerを仮定しない。
- amplitude Gap と ray-minus whole を直接 equality としない。
- RH conclusionを導入しない。
- `sorry`, `admit`, `axiom`, `native_decide` を導入しない。

## 10. roadmap classification

実装後 `0000-CFZP-roadmap.md` に CFZP-012 を追記する。

Green-A の基準は「baseline collapse」ではなく、mirror baseline residual の functional-reflection / height-reversal classification が finite exact theorem として閉じたこと。

roadmap には少なくとも次を明記する。

```text
CFZP-011 Layer 1: CLOSED
CFZP-012 mirror baseline identity: CLASSIFIED
Layer 2 weighted Gram/interference: OPEN
common-baseline finite/cofinal reach: OPEN
```

weight reversal が未解決なら、その correction / conjugation gap を named marker として残す。

## 11. 検証

最低限次を実行する。

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaMirrorBaselineFunctionalReflectionHeightReversalAudit.lean
lake build DkMath.RH
git diff --check
```

可能なら通常の project full build/test suite も実行する。

新規 module と変更ファイルに `sorry`, `admit`, `axiom`, `native_decide` が無いことを確認する。

既存 repository の unrelated warning / existing `sorry` は本 stage の新規 defect と混同しない。
