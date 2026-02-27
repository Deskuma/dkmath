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

### 2026-02-27 phase-14 継続（TODO-1 を `padicValNat` 版まで接続）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `padicValNat_eq_factorization`
  2. `not_dvd_padicValNat_of_not_dvd_factorization`
  3. `exists_primeFactor_val_not_dvd_of_not_isPow`
- 意図:
  - factorization 版で確定した TODO-1 の核を、
    `exponent_alignment_failure_of_val_not_dvd` にそのまま渡せる
    `padicValNat` 版まで薄く接続。
  - これで TODO-1 は「最終使用形」まで閉じた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-3 の最薄部を固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `coprime_sub_of_coprime`
     - `y ≤ z` かつ `Nat.Coprime y z` から `Nat.Coprime (z - y) y`
- 意図:
  - TODO-3 のうち、最も独立して進められる「差の gcd 不変」部分を先に確定。
  - これで、反例から `Nat.Coprime y z` さえ得られれば、
    `u := z - y` に対する `Nat.Coprime u y` は即座に回収できる。
- 実装メモ:
  - `Nat.coprime_sub_self_right` を利用し、gcd 手計算を避けて最短で固定。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-3 の残り 1 ピースを実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `coprime_right_of_add_pow_eq_pow`
     - `Nat.Coprime x y` と `x ^ p + y ^ p = z ^ p` から `Nat.Coprime y z`
- 意図:
  - TODO-3 の残りである「反例から `Nat.Coprime y z` を回収」を対偶で固定。
  - `g := Nat.gcd y z` に素因子 `q` があれば、
    `q ∣ y`, `q ∣ z`, したがって `q ∣ y^p`, `q ∣ z^p` から
    `q ∣ x^p`、さらに `q ∣ x` を導き、`Nat.Coprime x y` と矛盾。
- 到達点:
  - `coprime_right_of_add_pow_eq_pow` と
    既存の `coprime_sub_of_coprime` を組み合わせれば、
    反例から `u := z - y` に対する `Nat.Coprime u y` が回収できる。
  - これで TODO-3 は実質完了。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-2 の入力束を参照順込みで固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `PrimeCounterexamplePack`
  2. `PrimeCounterexamplePack.gap`
  3. `PrimeCounterexamplePack.gap_pos`
  4. `PrimeCounterexamplePack.gap_coprime_right`
  5. `GapNotIsPowTarget`
- 意図:
  - TODO-2 で使う primitive 反例の入力束を 1 箇所へ固定。
  - `TODO-3` で整備した `coprime_right_of_add_pow_eq_pow` と
    `coprime_sub_of_coprime` をそのまま再利用し、
    差 `u := z - y` の positivity / coprime 条件を束側メソッドとして回収できるようにした。
- 実装メモ:
  - 初回追加では参照順が逆でビルドが壊れたため、
    `PrimeCounterexamplePack` ブロックを TODO-3 補題群の後ろへ移動。
  - 数学内容は増やさず、定義順だけを整えて staging を復旧。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-2 を invariant 接続口へ 2 段化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoCosmicGapInvariant`
  2. `gap_not_isPow_of_counterexample`
- 意図:
  - `GapNotIsPowTarget` を直接埋めるのではなく、
    Triomino/Cosmic 側が最終的に供給すべき「gap は p 乗になれない」命題を
    先に名前で固定。
  - `TriominoCosmicPrimeGe5` 側は薄い変換だけを持ち、
    本丸の証明は別モジュールへ隔離しやすい構造にした。
- 到達点:
  - TODO-2 の未解決点は
    `TriominoCosmicGapInvariant` をどこでどう証明するか、
    という一点にさらに明確化された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5`
  - 結果: 成功。

### 2026-02-27 phase-14 継続（TODO-2 の本丸を隔離モジュールへ分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `TriominoCosmicGapInvariant` を `GapNotIsPowTarget` への alias に変更
     - 定義重複をなくし、意味だけを docstring に残す形へ整理
- 追加内容:
  1. 新規モジュール `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  2. `triominoCosmicGapInvariant : TriominoCosmicGapInvariant`
- 意図:
  - `TriominoCosmicPrimeGe5` は staging として清潔に保ち、
    `TODO-2` の本丸証明だけを別ファイルへ隔離。
  - 研究中の未解決点（`sorry`）を 1 ファイル 1 定理に閉じ込める。
- 実装メモ:
  - 新規ファイルはまだ公開面へは載せていない。
  - `triominoCosmicGapInvariant` 本体は未実装で、現時点では
    `hpack.gap_pos` / `hpack.gap_coprime_right` を取り出した位置で `sorry` 1 件。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5 DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。

### 2026-02-27 phase-14 継続（隔離室の `sorry` を既存補題接続の直前まで縮小）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 探索結果:
  - `TriominoFLT` / `FLT` 周辺を `gap`, `isPow`, `GN`, `NoSq`, `NonLift` で探索したが、
    現時点で「`PrimeCounterexamplePack -> ¬ ∃ t, (z - y) = t ^ p`」を
    そのまま返す既存コード補題は未発見。
  - 一方で `DkMath.FLT.Core.pow_eq_sub_mul_GN_of_add_pow_eq` は既に存在し、
    gap への変数変換と Cosmic Formula 側への接続にそのまま使えることを確認。
- 変更内容:
  1. `u := hpack.gap`
  2. `hu_pos : 0 < u`
  3. `hcop_uy : Nat.Coprime u y`
  4. `hxpow : x ^ p = u * GN p u y`
     - `pow_eq_sub_mul_GN_of_add_pow_eq` から `simpa` で取得
- 意図:
  - 隔離室の `sorry` を「Triomino/Cosmic 固有の不変量へ接続する最後の 1 点」だけに絞る。
  - 数論側の前処理（gap の positivity / coprime / Cosmic factorization）は既存補題で確定。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。
