# No Square on S0 Work Notes

status: 作業中 - phase-14: 完全証明への道（pending 除去）

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)
[NoSqOnS0: phase-08](NoSqOnS0-WorkNotes-phase-08.md)
[NoSqOnS0: phase-09](NoSqOnS0-WorkNotes-phase-09.md)
[NoSqOnS0: phase-10](NoSqOnS0-WorkNotes-phase-10.md)
[NoSqOnS0: phase-11](NoSqOnS0-WorkNotes-phase-11.md)
[NoSqOnS0: phase-12](NoSqOnS0-WorkNotes-phase-12.md)
[NoSqOnS0: phase-13](NoSqOnS0-WorkNotes-phase-13.md)

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [x] ただし、`GEisensteinBridge` の `descent` インターフェースは実装済み。

## 状況タスク

- 完了条件（DoD）:
  - [ ] 1. `TriominoFLT.lean` に `sorry` がない。
  - [ ] 2. `FLT_highExponent_core_pending` が実装済み（または不要化）。
  - [ ] 3. `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT` が成功。
  - [ ] 4. 暫定依存の残有無をコメントとログに明示。
- 受け入れ条件:
  - [ ] 1. Bridge から `Main` の triomino 接続口へ実際に到達すること。
  - [ ] 2. `Main` 側既存 API（line 772 / 788）を変更せず接続できること。

## 計画

## 作業ログ

### 2026-02-27 phase-14 継続（`TriominoCosmicPrimeGe5` 作業用モジュール追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`（新規）
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `FLTPrimeGe5Target := PrimeGe5FLTProvider`
  2. `triominoCosmic_globalProvider_of_FLTPrimeGe5`
  3. `triominoPrimeProvider_of_FLTPrimeGe5`
  4. `FLT_prime_ge5` 実装に向けた TODO 順序・最終ターゲットを module doc/comment で固定
- 意図:
  - `TriominoCosmic.lean` の staging 層を `sorry` なしのまま保ちつつ、
    `FLT_prime_ge5` 本体を育てる専用の作業場所を別ファイルへ確保。
  - 未完成定理本体はまだ置かず、ターゲットの型と補題分解順だけを
    Lean ファイルとして参照可能な形にした。
- 公開面ポリシー:
  - まだ `DkMath/FLT.lean` には載せない。
    実装が進むまでは内部作業用モジュールとして保持する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-1 の factorization 版を実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `exists_eq_pow_of_factorization_dvd`（private）
     - 素因数分解の指数がすべて `p` の倍数なら、`p` 乗根を明示構成
  2. `exists_primeFactor_factorization_not_dvd_of_not_isPow`
     - `u` が `p` 乗でないなら、
       ある素因子 `q` で `¬ p ∣ u.factorization q` を取り出す
- 意図:
  - `FLT_prime_ge5` 骨格の TODO-1 を、
    `padicValNat` へ行く前の最も独立した核（factorization 版）として確定。
  - 次段で `padicValNat q u = u.factorization q` 系の既存補題を使って、
    `¬ p ∣ padicValNat q u` へ接続しやすくした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。
