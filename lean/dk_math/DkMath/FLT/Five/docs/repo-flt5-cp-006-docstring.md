# Report: FLT5 cp-006

## docstring

必須1は impl ファイル完了状態が解りやすいように impl 内にステータスと共に記載。
以下 Codex 報告

---

必須2の対応を完了しました。

[SignedGoldenZeroSectorDescent.lean](/lean/dk_math/DkMath/FLT/Five/SignedGoldenZeroSectorDescent.lean) の次の4定理に theorem-level docstring を追加しています。

- `goldenZeroSectorLift_norm`
- `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`
- `GoldenZeroSectorDescentPacket.strictDescent`
- `goldenZeroSectorDescentPacket_false`

明記した内容:

- well-founded measure は第二座標の絶対値 `|s|`
- fifth root の第二座標が次 packet の visible coordinate になる
- coprimality、fifth-power shape、norm condition が保存される
- strict inequality により `Nat.strong_induction_on` が適用できる
- 最終 FLT5 theorem を参照しない非循環な降下である

検証:

- `lake build DkMath.FLT.Five.SignedGoldenZeroSectorDescent` — 成功、8273 jobs
- `git diff --check` — 成功
- worktree clean

コミット:

```text
c4b6664b docs(flt5): explain the strict descent heart
```

ユーザー側の cp-006 完了報告コミットも保持されています。

```text
85657cac Upd: docs: report: FLT5 cp-006 — GN5 / FLT5 mathematician-facing docstring and explanatory API pass
```

現在、ブランチは origin より 2 commits ahead です。

---

## Linter warning cleanup

cp-006 の最終 polish として、FLT5 全体ビルドで報告されていた軽微な
Lean linter warning を修正した。

対象:

- `GoldenUnitClassification.lean`
- `SignedGoldenSectorArithmetic.lean`
- `SignedGoldenZeroSector.lean`
- `SignedGoldenZeroSectorInversion.lean`
- `SignedGoldenZeroSectorFactorization.lean`
- `SignedGoldenZeroSectorDescent.lean`

修正内容:

- 不要な sequential-goal focus と判定された `tac1 <;> tac2` を、
  `all_goals` を用いた明示的な goal 処理へ変更
- `unnecessarySimpa` が報告された一箇所を `simp` へ簡約
- `set_option linter.unnecessarySeqFocus false` などの警告抑制は追加していない
- theorem statement、公開 API、数学的証明内容に変更はない

検証:

- `lake build DkMath.FLT.Five` — 成功、8281 jobs、対象 linter warning なし
- `lake build DkMathTest.FLT.Five.CheckAxioms` — 成功
- `git diff --check` — 成功

結果:

cp-006 の docstring/API polish に加えて、同カテゴリー内で観測されていた
`unnecessarySeqFocus` および `unnecessarySimpa` warning も除去された。

---

## High-value explanatory API follow-up

cp-006 の付加価値作業として、数学者がエディタ上の API と公理監査だけで
証明経路と正確な射程を読めるよう、次の三点を追加した。

### Exact clean-channel valuation

`Valuation.lean` に次の公開 theorem を追加した。

```lean
theorem padicValNat_clean_body_eq_one
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1
```

これは新しい証明路線ではなく、`CleanGN5Channel.dvd_body` が与える
valuation lower bound と、`padicValNat_clean_body_upper_bound` が与える upper
bound を束ねた canonical API である。valuation による clean-channel
contradiction も、この theorem を再利用して `5 ≤ valuation` と
`valuation = 1` を直接対立させる形へ更新した。

### Final public theorem docstrings

`Main.lean` の `flt5Target` と `fermatFive_no_positive_solution` に、次を
theorem-level docstring として明記した。

- `x`, `y`, `z` は正の自然数
- `Fermat5Equation x y z` は `x^5 + y^5 = z^5` を表す
- ordinary-argument theorem は `flt5Target` の wrapper
- 一般指数版および任意の符号付き整数版ではない

### CheckAxioms inspection entry point

`CheckAxioms.lean` に module doc を追加し、ファイルが proof module ではなく
axiom-surface inspection entry point であることを明記した。さらに監査項目を
次の大見出しで整理した。

- GN5 foundation
- clean-channel obstruction
- five-adic routing
- golden order
- unit classification
- zero-sector descent
- public closure

`padicValNat_clean_body_eq_one` も `#print axioms` の監査対象へ追加した。

検証:

- `lake build DkMath.FLT.Five.Valuation` — 成功、8252 jobs
- `lake build DkMath.FLT.Five` — 成功
- `lake build DkMath.FLT.Five.Main` — 成功
- `lake build DkMathTest.FLT.Five.CheckAxioms` — 成功
- `git diff --check` — 成功
