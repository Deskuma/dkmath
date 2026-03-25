# No Square on S0 Work Notes

status: 完了 - phase-03: Phase 03-A: 定義 → 判定機 → 十分条件の順で実装する

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md) - `hS0_not_sq` を `NoSqOnS0` に置換可能な構造にした。
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md) -  x=c-b, u=b を代入して `Gx 3 x u = S0_nat c b` へ落とす橋補題を作った。

## 状況

ここからは次の3フェーズが自然です。

**Phase 03-A: 定義を固める（PetalCoreUnit）**

1. 新規 `lean/dk_math/DkMath/FLT/PetalCoreUnit.lean` を作成
2. 最小定義を追加

   - `PetalCoreUnit`
   - `HarmonicPoint`
   - `PeriodIndex`
   - `isExceptionalPhase`（除外対象）

3. `NPUnit` との橋を追加

   - `NP -> PetalCoreUnit` の写像
   - `succ` と周期述語の整合補題（弱い形でOK）

**Phase 03-B: 判定器を実質化**

1. `CounterexamplePattern.phaseGate` を `HasPhaseUnitInfrastructure` だけでなく
   `HarmonicPoint` / `isExceptionalPhase` を参照する形に更新
2. `classifyLift` に例外集合分岐を追加

   - `exceptional -> undecided`
   - `non-exceptional + primitive + noSquare -> impossible`

**Phase 03-C: NoSqOnS0 の十分条件を構築**

1. `NoSqOnS0` の十分条件補題を段階化して追加

   - `NoSqOnS0_of_nonExceptionalHarmonic`（仮名）

2. `PhaseLift`([src](../../PhaseLift.lean)) に接続して

   - `hS0_not_sq_of_NoSqOnS0` の上流を1段引き上げる

3. `Main`([src](../../Main.lean)) に派生定理を追加

   - `..._of_nonExceptionalHarmonic`（仮名）

---

実装順は **A1 → A2 → B1 → C1** が最短です。

## 2026-02-26 作業ログ（現時点まとめ）

## 2026-02-26 追記（phase-03: スケルトン作成）

### 実施内容

- 新規: `lean/dk_math/DkMath/FLT/PetalCoreUnit.lean`
  - 追加定義（Phase 03-A の最小骨格）:
    - `PetalCoreUnit`
    - `PeriodIndex`
    - `HarmonicPoint`
    - `isExceptionalPhase`
  - `NPUnit` との橋:
    - `ofNP : DkMath.NP → PetalCoreUnit`
    - `coreSucc`, `coreVal`
    - `coreSucc_val`
    - `harmonicPoint_ofNP`
    - `notExceptional_ofNP_zero`

- 更新: `lean/dk_math/DkMath/FLT/CounterexamplePattern.lean`
  - `import DkMath.FLT.PetalCoreUnit` を追加
  - `phaseGate` を
    `HasPhaseUnitInfrastructure ∧ ∃ u, HarmonicPoint u ∧ ¬ isExceptionalPhase u`
    に拡張
  - `phaseGate_default` で既定 witness を供給

### 検証

- `lake build DkMath.FLT.PetalCoreUnit` 成功
- `lake build DkMath.FLT.CounterexamplePattern` 成功
- `lake build DkMath.FLT.Main` 成功

### 補足

- これは phase-03 の**スケルトン**実装。
- 次は `classifyLift` へ例外相分岐（`exceptional -> undecided`）を本体反映する。

## 2026-02-26 追記（phase-03: 例外相分岐を classifyLift へ反映）

### 実施内容

- 更新: `lean/dk_math/DkMath/FLT/CounterexamplePattern.lean`
  - `exceptionalPhaseGate` を追加
  - `classifyLift` の先頭分岐を追加:
    - `exceptionalPhaseGate x = true` の場合は `LiftStatus.undecided`
  - 既存補題を分岐対応に更新:
    - `classifyLift_impossible_of_gates` に `¬ exceptionalPhaseGate x` を追加
    - `classifyLift_possible_of_primitive_and_sq` に `¬ exceptionalPhaseGate x` を追加
    - `classifyLift_undecided_of_not_primitive` に `¬ exceptionalPhaseGate x` を追加
    - `classifyLift_undecided_of_exceptional` を追加
    - `noSquareGate_of_classifyLift_impossible` を分岐対応に更新

### 検証

- `lake build DkMath.FLT.CounterexamplePattern` 成功
- `lake build DkMath.FLT.Main` 成功

### 補足

- これで phase-03-B の「`exceptional -> undecided`」を判定器本体に反映済み。
- 次は phase-03-C: `NoSqOnS0` の十分条件補題を段階化して追加する。

## 2026-02-26 追記（phase-03-C: 十分条件スケルトン接続）

### 実施内容

- 更新: `lean/dk_math/DkMath/FLT/PhaseLift.lean`
  - 追加定義:
    - `NonExceptionalHarmonicOnS0 (c b : ℕ)`
      - `(∃ u, HarmonicPoint u ∧ ¬ isExceptionalPhase u) ∧ NoSqOnS0 c b`
  - 追加補題:
    - `NoSqOnS0_of_nonExceptionalHarmonic`

- 更新: `lean/dk_math/DkMath/FLT/Main.lean`
  - 追加定理:
    - `FLT_d3_by_padicValNat_of_nonExceptionalHarmonic`
  - `NoSqOnS0_of_nonExceptionalHarmonic` を経由して
    既存 `FLT_d3_by_padicValNat_of_NoSqOnS0` に接続

### 検証

- `lake build DkMath.FLT.PhaseLift` 成功
- `lake build DkMath.FLT.Main` 成功

### 補足

- これは phase-03-C の**スケルトン接続**。
- 次は `NonExceptionalHarmonicOnS0 -> NoSqOnS0` の中身を
  仮定の分解から実質定理へ置換していく。
