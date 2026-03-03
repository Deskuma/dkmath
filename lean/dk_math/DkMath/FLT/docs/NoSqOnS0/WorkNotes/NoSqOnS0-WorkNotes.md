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

### 2026-02-27 phase-14 継続（`gap` から `GN` へ責務移動）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `exists_eq_pow_of_gap_eq_pow`
     - `x^p = u * GN p u y` と `u = t^p` から `∃ s, GN p u y = s^p`
  2. `TriominoCosmicBodyInvariant`
  3. `triominoCosmicBodyInvariant`
  4. `gapInvariant_of_bodyInvariant`
- 変更内容:
  1. `triominoCosmicGapInvariant` は
     `gapInvariant_of_bodyInvariant triominoCosmicBodyInvariant`
     へ委譲する形に変更
- 意図:
  - 「gap が p 乗でない」を直接示すのではなく、
    `u = t^p` なら `GN` も `p` 乗へ落ちる、という純算術縮約を先に確定。
  - これにより、隔離室の未解決点を
    「Body (`GN`) が p 乗になれない」
    という本丸 1 点へさらに圧縮。
- 到達点:
  - `sorry` は `triominoCosmicBodyInvariant` の 1 件だけに維持。
  - `triominoCosmicGapInvariant` 自体は、既に `sorry` なしの薄い合成定理になった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。

### 2026-02-27 phase-14 継続（`p ≥ 5` の安全柵を TODO-2 系へ追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `PrimeGe5CounterexamplePack`
  2. `PrimeGe5CounterexamplePack.gap`
  3. `PrimeGe5CounterexamplePack.gap_pos`
  4. `PrimeGe5CounterexamplePack.gap_coprime_right`
- 変更内容:
  1. `GapNotIsPowTarget` を `PrimeGe5CounterexamplePack` ベースへ変更
  2. `TriominoCosmicBodyInvariant` も `PrimeGe5CounterexamplePack` ベースへ変更
- 意図:
  - `p = 2, 3` を TODO-2 / BodyInvariant の入力領域から除外し、
    命題が真になりうる world へ制限。
  - `PrimeCounterexamplePack` はそのまま残し、prime-ge5 専用の追加柵だけを別構造体で載せた。
- 到達点:
  - `TODO-2` 系の未解決点は引き続き `triominoCosmicBodyInvariant` の 1 件だけ。
  - しかもその命題は、`p = 2, 3` の自明な反例世界を含まない形に安全化済み。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5 DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。

### 2026-02-27 phase-14 継続（`NoPowOnGN` 仕様へ分解）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `NoPowOnGN_fromCounterexample`
  2. `not_isPow_of_exists_prime_dvd_not_dvd_sq`
  3. `bodyInvariant_of_NoPowOnGN`
  4. `triominoCosmicNoPowOnGN`
- 変更内容:
  1. `triominoCosmicBodyInvariant` は
     `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN`
     へ委譲する形へ変更
- 意図:
  - `BodyInvariant` を直接証明するのではなく、
    まず「`GN` に平方止まりの素因子が入る」という最小入力仕様 `NoPowOnGN_fromCounterexample`
    に分解。
  - `p ≥ 5` のもとで `q ∣ GN` かつ `¬ q^2 ∣ GN` なら `GN` は `p` 乗になれない、
    という薄い一般補題を経由して `BodyInvariant` を得る構造にした。
- 到達点:
  - 隔離室の未解決点は、`triominoCosmicNoPowOnGN` の 1 件だけ。
  - `gap` 側でも `Body` 側でもなく、
    「反例から `GN` に平方止まりの素因子を供給できるか」という仕様供給 1 点へ収束。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。

### 2026-02-27 phase-14 継続（`triominoCosmicNoPowOnGN` を 2 分岐仕様へ展開）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `NoSqPrimeOnGN_when_p_dvd_u`
  2. `NoSqPrimeOnGN_when_p_not_dvd_u`
  3. `noPowOnGN_of_branches`
- 変更内容:
  1. `triominoCosmicNoPowOnGN` に
     「Branch A を binom 展開で閉じる / Branch B を Zsigmondy・NonLiftable で供給する」
     という TODO コメントを明記
- 意図:
  - 最後の未解決点を、`p ∣ (z-y)` と `¬ p ∣ (z-y)` の 2 分岐へさらに分解。
  - どちらの branch も `∃ q, Prime q ∧ q ∣ GN ∧ ¬ q^2 ∣ GN` を返す同型仕様に揃え、
    `noPowOnGN_of_branches` で合成できる形を先に固定。
- 到達点:
  - `sorry` は引き続き `triominoCosmicNoPowOnGN` の 1 件だけ。
  - ただし次の具体作業は
    Branch A（`p ∣ u`）か Branch B（`¬ p ∣ u`）のどちらか一方だけを個別に埋めればよい状態まで整理された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件）。

### 2026-02-27 phase-14 継続（Branch A 向け補助を先行固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `PrimeGe5CounterexamplePack.xpow_eq_gap_mul_GN`
  2. `PrimeGe5CounterexamplePack.prime_not_dvd_right_of_prime_dvd_gap`
- 意図:
  - Branch A（`p ∣ (z-y)`）で毎回必要になる
    `x^p = gap * GN p gap y`
    と
    `p ∣ gap -> p ∤ y`
    を pack 側メソッドとして先に固定。
  - `triominoCosmicNoPowOnGN` の Branch A 実装時に、
    反例 pack から必要な前処理をそのまま呼び出せるようにした。
- 実装メモ:
  - `GN` は `DkMath.CosmicFormulaBinom.GN` で完全修飾。
  - `p ∤ y` は `Nat.not_coprime_of_dvd_of_dvd` を使って
    `gap ⟂ y` から反証で回収。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5 DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `TriominoCosmicGapInvariant.lean` の `sorry` 1 件のみ）。

### 2026-02-27 phase-14 継続（Branch A を実装し、未解決を Branch B 専用へ縮小）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `noSqPrimeOnGN_when_p_dvd_u_impl`
- 変更内容:
  1. `triominoCosmicNoPowOnGN` は Branch A を `noSqPrimeOnGN_when_p_dvd_u_impl` へ委譲
  2. 残る `sorry` は Branch B (`NoSqPrimeOnGN_when_p_not_dvd_u`) のみ
- 実装メモ:
  - Branch A は `q := p` を採用。
  - `GN p (z-y) y` を head/tail に分解し、
    `A = p * y^(p-1)` と
    `B = Σ_{k≥1}` を分離。
  - `p ∣ (z-y)` から `p^2 ∣ B` を `k = 1` と `k ≥ 2` に場合分けして証明。
  - `p ∤ y` は `PrimeGe5CounterexamplePack.prime_not_dvd_right_of_prime_dvd_gap` を再利用。
  - `¬ p^2 ∣ A` と `p^2 ∣ B` から `¬ p^2 ∣ A + B` を出し、
    `q ∣ GN` かつ `¬ q^2 ∣ GN` を確定。
- 到達点:
  - `TriominoCosmicGapInvariant.lean` の未解決点は
    `triominoCosmicNoPowOnGN` 内の Branch B 用 `sorry` 1 件だけ。
  - 以後の探索対象は `¬ p ∣ (z-y)` 側の
    `GN` に平方止まりの素因子を入れる既存理論（Zsigmondy / NonLiftable / NoSq）へ限定された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件のみ）。

### 2026-02-27 phase-14 継続（PrimeGe5 pack に非零条件を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `PrimeGe5CounterexamplePack` に
     - `hx0 : x ≠ 0`
     - `hy0 : y ≠ 0`
     - `hz0 : z ≠ 0`
     を追加
  2. 補助メソッド
     - `PrimeGe5CounterexamplePack.x_pos`
     - `PrimeGe5CounterexamplePack.y_pos`
     - `PrimeGe5CounterexamplePack.z_pos`
     を追加
- 意図:
  - Branch B で Zsigmondy 系 API に接続する際に必要な `0 < y`（および必要なら `0 < x`, `0 < z`）を、
    pack から直接回収できるようにするため。
  - `y = 0` のような仕様外ケースを `PrimeGe5CounterexamplePack` の定義段階で排除し、
    `PrimitivePrime_fromCounterexample` の前提不足を構造的に解消する。
- 到達点:
  - `TriominoCosmicGapInvariant.lean` 側の唯一の `sorry` はそのまま 1 件。
  - ただし残る `hBspec` のうち、
    Zsigmondy 側の `PrimitivePrime_fromCounterexample` を既存定理へ接続する前提は揃った。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5 DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件のみ）。

### 2026-02-27 phase-14 継続（Branch B を 2 段仕様へ分解）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `PrimitivePrime_fromCounterexample`
  2. `NoSqOnGN_of_primitivePrime`
  3. `noSqPrimeOnGN_when_p_not_dvd_u_of_specs`
- 変更内容:
  1. `TriominoCosmicGapInvariant.lean` に `import DkMath.FLT.CosmicPetalBridge`
  2. `triominoCosmicNoPowOnGN` の Branch B は、
     `PrimitivePrime_fromCounterexample ∧ NoSqOnGN_of_primitivePrime`
     の 1 束仕様 `hBspec` に委譲する形へ変更
- 意図:
  - Branch B（`¬ p ∣ gap`）を
    「原始素因子の取得」と「原始素因子の深刺し禁止」の 2 段に明示分解。
  - `q ∣ GN` への橋は、既存の `prime_dvd_GN_of_dvd_sub_not_dvd_left` に固定。
  - 未解決点は 1 個のまま維持しつつ、残る `sorry` の意味を
    「Zsigmondy 出力 + NoSq/NonLiftable 入力の束をどう供給するか」
    まで狭めた。
- 到達点:
  - `triominoCosmicNoPowOnGN` の `sorry` は 1 件のまま。
  - ただし Branch B の具体実装は、
    `PrimitivePrime_fromCounterexample` と `NoSqOnGN_of_primitivePrime`
    をどこから供給するか、という完全に局所な問題へ分離された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（`TriominoCosmicGapInvariant.lean` に `sorry` warning 1 件のみ）。

### 2026-02-27 phase-14 継続（Branch B の未解決点を名前付き定理へ隔離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. Branch B 後半の匿名 `sorry` を `noSqOnGN_of_primitivePrime_impl` へ切り出し
  2. `triominoCosmicNoPowOnGN` は `primitivePrime_fromCounterexample_impl` と `noSqOnGN_of_primitivePrime_impl` の合成に整理
- 意図:
  - いま残っている未解決点を「一般 prime-ge5 で `q ∣ GN ∧ ¬ q ∣ u -> ¬ q^2 ∣ GN` を供給する定理」へ明示的に固定。
  - `GcdNextResearch` の `sorry` 付き研究補題へ依存せず、未証明箇所をこのファイル 1 定理に閉じ込める。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `noSqOnGN_of_primitivePrime_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（残る穴を `AllNonLiftableOnGN` family へ昇格）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `PrimitiveOnGN` / `NonLiftableGN` / `AllNonLiftableOnGN` を追加
  2. Branch B 合成 `noSqPrimeOnGN_when_p_not_dvd_u_of_specs` の第2入力を、点ごとの `NoSqOnGN_of_primitivePrime` ではなく、pack 由来の `AllNonLiftableOnGN` family に変更
  3. 未解決点を `allNonLiftableOnGN_fromCounterexample_impl` へ移動
- 意図:
  - 残りの `sorry` を、単発の `q^2 ∤ GN` ではなく、プロジェクト既存の `NonLiftable` 系語彙に沿った family 供給へ寄せる。
  - これにより、今後は `Triomino/Cosmic` 側の `NonLiftable / NoSq / classify impossible` 理論をそのまま接続しやすくした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `allNonLiftableOnGN_fromCounterexample_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（一般 `GN` nonlift bridge を型として固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `TriominoCosmicNonLiftableGNBridge` を追加
  2. `allNonLiftableOnGN_fromCounterexample_impl` の型を上記 bridge alias に統一
  3. `triominoCosmicNoPowOnGN_of_nonLiftableGNBridge` を追加し、`NoPowOnGN` 側の配線を no-`sorry` で分離
  4. `triominoCosmicNoPowOnGN` は bridge 実装を差し込む薄いラッパへ整理
- 技術的所見:
  - `CosmicPetalBridge` の既存 no-`sorry` 橋は `GN 3 (c-b) b = S0_nat c b` の d=3 専用。
  - 一般 `p ≥ 5` の `GN p (z-y) y` を S0/Phase 側に落とす既存 no-`sorry` 橋は、現行本体コードには見当たらない。
  - したがって残る未解決点は「general GN nonlift bridge をどう供給するか」の 1 点に正しく集約されている。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `allNonLiftableOnGN_fromCounterexample_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（general GN nonlift bridge を別ファイルへ分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoNoWieferichBridge`
  2. `triominoCosmicNonLiftableGNBridge_of_noWieferich`
  3. `triominoNoWieferichBridge_impl`（残る未解決点）
- 変更内容:
  1. `TriominoCosmicGapInvariant` は新規 bridge ファイルを import
  2. `allNonLiftableOnGN_fromCounterexample_impl` は `triominoCosmicNonLiftableGNBridge_of_noWieferich triominoNoWieferichBridge_impl` に委譲
- 意図:
  - 最後の `sorry` を `TriominoCosmicGapInvariant` から追い出し、`general GN nonlift bridge` 専用ファイルに隔離。
  - `GapInvariant` 側は再び配線専用になり、未解決点は「反例文脈で Wieferich 例外を排除する橋」1 定理に集約。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoNoWieferichBridge_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（最後の穴を `WieferichLift` 排除へさらに圧縮）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `WieferichLift`
  2. `TriominoWieferichLiftExclusion`
  3. `triominoNoWieferichBridge_of_wieferichLiftExclusion`
  4. `triominoWieferichLiftExclusion_impl`（残る未解決点）
- 変更内容:
  1. `triominoNoWieferichBridge_impl` は `triominoWieferichLiftExclusion_impl` から no-`sorry` で導出する形へ整理
- 意図:
  - 最後の `sorry` を、単なる divisibility 命題ではなく「反例文脈で Wieferich lift が起きない」という、より本質的な下降法コアへ押し込んだ。
  - 次に追加すべき新規理論は、`WieferichLift -> より小さい反例` を構成する下降補題の系統であることがコード上で明示された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoWieferichLiftExclusion_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（最後の穴を「最小反例選択 + 下降」カーネルへ圧縮）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `MinimalPrimeGe5CounterexamplePack`
  2. `WieferichDescent`
  3. `MinimalWieferichLiftSelection`
  4. `wieferichLiftExclusion_of_descent_on_minimal`
  5. `wieferichLiftExclusion_of_selection_and_descent`
  6. `TriominoWieferichLiftKernel`
  7. `triominoWieferichLiftKernel_impl`（残る未解決点）
- 変更内容:
  1. `triominoWieferichLiftExclusion_impl` は `triominoWieferichLiftKernel_impl` から no-`sorry` で導出する形へ整理
- 意図:
  - 最後の `sorry` を、単に `WieferichLift` を否定する命題ではなく、
    「最小反例を選べる」+「Wieferich lift からより小さい反例を作れる」
    という下降法の本体カーネルに押し込めた。
  - 以後の新規理論追加は、このカーネルを埋めることに集中できる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoWieferichLiftKernel_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（Branch B 専用 lift 供給を no-`sorry` 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `CounterexampleHasWieferichLiftB`
  2. `WieferichDescentB`
  3. `counterexampleHasWieferichLiftB_impl`
- 意図:
  - 「反例から lift を作る」部分を、実際に Branch B（`¬ p ∣ (z - y)`）でしか使わない領域へ切り出した。
  - 既存の `exists_primitive_prime_factor_prime` と `z^p - y^p = x^p` だけで、Branch B の lift 供給は no-`sorry` で閉じることを確認した。
- 技術メモ:
  - この時点では、既存の `MinimalWieferichLiftSelection` は「全反例上の最小化」になっているため、
    `CounterexampleHasWieferichLiftB` をそのままカーネルへ差し替えると、最小反例選択の対象集合と整合しない。
  - 次段では、`¬ p ∣ (z - y)` を保つ最小化（または Branch B 専用の `WieferichLiftExclusion`）へ整理した上で、
    残る `sorry` を `descent` 側だけに押し込む必要がある。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoWieferichLiftKernel_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（最小反例選択を no-`sorry` 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `CounterexampleHasWieferichLift`
  2. `minimalPrimeGe5CounterexampleSelection_impl`
  3. `minimalWieferichLiftSelection_of_liftExists`
  4. `wieferichLiftExclusion_of_liftExists_and_descent`
- 変更内容:
  1. `TriominoWieferichLiftKernel` を `CounterexampleHasWieferichLift ∧ WieferichDescent` に変更
  2. `triominoWieferichLiftExclusion_impl` は `liftExists + descent` から no-`sorry` で導出する形へ整理
- 意図:
  - 最小反例の「選択」は整列順序だけで no-`sorry` で閉じる部分として切り離し、
    残る未解決点を「反例から lift を作る」+「lift から下降する」の 2 段カーネルへ縮小した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoWieferichLiftKernel_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（Branch B 最小化へ切替、`descent` だけを残す）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `TriominoNoWieferichBridge` を Branch B（`¬ p ∣ (z - y)`）前提付きに弱化
  2. `TriominoWieferichLiftExclusion` を Branch B 前提付きに弱化
  3. `MinimalPrimeGe5CounterexamplePackB` を追加
  4. `minimalPrimeGe5CounterexampleSelectionB_impl` を no-`sorry` で実装
  5. `MinimalWieferichLiftSelection` を Branch B 最小化へ切替
  6. `WieferichDescentB` の結論を `¬ p ∣ (z' - y')` 保存付きに強化
  7. `TriominoWieferichLiftKernel` を `CounterexampleHasWieferichLiftB ∧ WieferichDescentB` に切替
  8. `triominoWieferichLiftKernel_impl` は no-`sorry` で
     `⟨counterexampleHasWieferichLiftB_impl, triominoWieferichDescent_impl⟩`
     へ整理
  9. `TriominoCosmicNonLiftableGNBridge` も Branch B 前提付きに弱化
- 意図:
  - lift 供給・最小反例選択・排除の対象集合をすべて Branch B に一致させた。
  - その結果、残る未解決点を本当に `WieferichDescentB`（=`triominoWieferichDescent_impl`）1 本へ押し込めた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGN.lean` の `triominoWieferichDescent_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（descent を別ファイルへ隔離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNCore.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `CosmicPetalBridgeGNCore.lean` を新設し、Branch B の配線・最小化・lift 供給を移設
  2. `CosmicPetalBridgeGNDescentB.lean` を新設し、`triominoWieferichDescent_impl` を隔離
  3. `CosmicPetalBridgeGN.lean` を wrapper 化し、最終 3 定理のみを配線
- 意図:
  - `CosmicPetalBridgeGN.lean` 自体を完全に配線専用へ戻し、
    最後の未解決点を `CosmicPetalBridgeGNDescentB.lean` の 1 定理へ閉じ込めた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichDescent_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（descent を二層化、純算術データ抽出を no-`sorry` 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `WieferichDescentDataB`
  2. `wieferichDescentDataB_of_pack`
  3. `TriominoWieferichDescentCoreB`
  4. `triominoWieferichDescent_impl_of_core`
  5. `triominoWieferichDescentCoreB_impl`
- 変更内容:
  1. `triominoWieferichDescent_impl` は `triominoWieferichDescentCoreB_impl` への wrapper に変更
- 意図:
  - `WieferichLift` から純算術で取れるデータ（特に `q^p ∣ GN p (z - y) y`）を no-`sorry` で固定し、
    最後の未解決点を「Triomino/Cosmic 固有の縮小器 core」1 定理へさらに圧縮した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichDescentCoreB_impl` の `sorry` 1件のみ）。

### 2026-02-27 phase-14 継続（step / core 分離、最後の `sorry` を step へ移動）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichDescentResultB`
  2. `TriominoWieferichDescentStepB`
  3. `triominoWieferichDescentCoreB_of_step`
  4. `triominoWieferichDescentStepB_impl`
- 変更内容:
  1. `triominoWieferichDescentCoreB_impl` は `step` から回収する配線へ変更
- 意図:
  - 縮小器の「成果物の形」と「step 実装」を明示し、
    最後の未解決点を `triominoWieferichDescentStepB_impl` 1 箇所に移した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichDescentStepB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`shrink` 核へ `sorry` を再隔離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkB`
- 変更内容:
  1. `TriominoWieferichDescentResultB` を data 用 `structure` へ修正
  2. `TriominoWieferichDescentStepB` を `Type` に修正
  3. `triominoWieferichDescentStepB_impl` は `hData` から `triominoWieferichShrinkB` へ渡すだけの glue に変更
  4. `triominoWieferichDescentCoreB_impl` / `triominoWieferichDescent_impl` は完全に配線化
- 意図:
  - `step / core / glue` の責務分離を完成させ、
    最後の未解決点を Triomino/Cosmic 固有の縮小器 `triominoWieferichShrinkB` 1 定理へ押し込めた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkB` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`candidate / repack / result` 分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkCandB`
  2. `TriominoWieferichShrinkCandB.toPack`
  3. `TriominoWieferichShrinkCandB.toResult`
  4. `triominoWieferichShrinkCandB_impl`
- 変更内容:
  1. `triominoWieferichShrinkB` は候補生成から `Result` へ落とす配線に変更
  2. `step / core / glue` は維持したまま、最後の未解決点を候補生成へ再移動
- 意図:
  - 縮小器を
    「候補生成（本丸）」
    「反例パック再構成」
    「最終 result 化」
    に分け、`sorry` を `triominoWieferichShrinkCandB_impl` 1 箇所へ押し込めた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkCandB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`Nums / witness / Cand` へ再分割）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkWitnessB`
  2. `TriominoWieferichShrinkNumsB`
  3. `triominoWieferichShrinkCandB_of_nums`
  4. `triominoWieferichShrinkNumsB_impl`
- 変更内容:
  1. `triominoWieferichShrinkCandB_impl` は `Nums -> Cand` の glue に変更
  2. `triominoWieferichShrinkB` は `Cand -> Result` の glue を維持
- 意図:
  - shrink を
    「Nums 生成（本丸）」
    「Nums から Cand へ」
    「Cand から Result へ」
    に再分割し、最後の未解決点を `triominoWieferichShrinkNumsB_impl` 1 箇所へさらに圧縮した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkNumsB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZ / Cert / glue` 分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkXYZB`
  2. `TriominoWieferichShrinkCertB`
  3. `TriominoWieferichShrinkXYZCertB`
  4. `triominoWieferichShrinkNumsB_of_XYZ_Cert`
  5. `triominoWieferichShrinkXYZCertB_impl`
- 変更内容:
  1. `triominoWieferichShrinkNumsB_impl` は `XYZ + Cert -> Nums` の glue に変更
  2. `triominoWieferichShrinkCandB_impl` は `Nums -> Cand` の glue を維持
  3. `triominoWieferichShrinkB` は `Cand -> Result` の glue を維持
- 意図:
  - shrink の内部を
    「XYZ 生成」
    「Cert 付与」
    「Nums 化」
    「Cand 化」
    「Result 化」
    の多層 glue に分け、最後の未解決点を `triominoWieferichShrinkXYZCertB_impl` 1 箇所へさらに圧縮した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZCertB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZ / hzlt / hpB' / witness` 投影レイヤ追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkXYZB_impl`
  2. `triominoWieferichShrink_hzlt`
  3. `triominoWieferichShrink_hpB'`
  4. `triominoWieferichShrink_witness`
- 変更内容:
  1. `triominoWieferichShrinkNumsB_impl` は上記 4 段の投影を束ねる glue に変更
- 意図:
  - `XYZCertB_impl` の単一コアを維持したまま、
    `XYZ` 生成・減少・Branch B 維持・witness 回収の名前付き切断面を用意し、
    今後の局所補題化を進めやすくした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZCertB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZCertB` のコア呼び出しを 1 回に固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkXYZB_of_core`
  2. `triominoWieferichShrink_hzlt_of_core`
  3. `triominoWieferichShrink_hpB'_of_core`
  4. `triominoWieferichShrink_witness_of_core`
- 変更内容:
  1. `triominoWieferichShrinkNumsB_impl` は `XYZCertB_impl` を 1 回だけ呼び、
     以後は `of_core` 投影から `t / hzlt / hpB' / hW` を回収する形に変更
- 意図:
  - 同じ core を重複して再評価する形を避け、
    以後の証明項肥大と書換えコストを抑える。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZCertB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZ + Trace` 導入、`XYZCertB_impl` を glue 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkTraceB`
  2. `triominoWieferichShrinkXYZCertB_of_trace`
  3. `triominoWieferichShrinkXYZTraceB_impl`
- 変更内容:
  1. `triominoWieferichShrinkXYZCertB_impl` は `XYZ + Trace -> XYZ + Cert` の再梱包 glue に変更
- 意図:
  - `XYZCertB_impl` 自体を配線化し、
    最後の未解決点を `triominoWieferichShrinkXYZTraceB_impl` 1 箇所へ移した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZTraceB_impl` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZTraceB_impl` を glue 化、`core` 導入）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkXYZTraceB_core`
  2. `triominoWieferichShrinkXYZB_impl_core`
  3. `triominoWieferichShrinkTraceB_impl_core`
- 変更内容:
  1. `triominoWieferichShrinkXYZTraceB_impl` は `XYZ` と `Trace` の回収を束ねる glue に変更
- 意図:
  - `XYZTraceB_impl` 自体を配線化し、
    最後の未解決点を `triominoWieferichShrinkXYZTraceB_core` 1 箇所へ再移動した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZTraceB_core` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZ_core / Trace_core / XYZTrace_core` へ再分割）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkXYZTraceB_kernel`
  2. `triominoWieferichShrinkXYZ_core`
  3. `triominoWieferichShrinkTrace_core`
- 変更内容:
  1. `triominoWieferichShrinkXYZTraceB_core` は `XYZ_core` と `Trace_core` を束ねる glue に変更
- 意図:
  - `XYZTraceB_core` 自体を配線化し、
    最後の未解決点を `triominoWieferichShrinkXYZTraceB_kernel` 1 箇所へ移した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZTraceB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`XYZ` に `ctor` を埋め込み、`Trace_core` を回収化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkCtorB`
  2. `triominoWieferichShrinkXYZ_kernel`
- 変更内容:
  1. `TriominoWieferichShrinkXYZB` に `ctor` を追加
  2. `triominoWieferichShrinkTrace_core` は `t.ctor` から `Trace` を回収する形へ変更
  3. `triominoWieferichShrinkXYZTraceB_kernel` を廃止し、
     `triominoWieferichShrinkXYZ_core` は `XYZ_kernel` の単純委譲へ変更
- 意図:
  - `Trace` 側の責務を「回収」に落とし、
    最後の未解決点を `XYZ` 生成 kernel（= 縮小変換の構成そのもの）へ寄せた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkXYZ_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`Witness` を `Eq / Inv` に分割し、`XYZ_kernel` を glue 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkWitnessEqB`
  2. `TriominoWieferichShrinkWitnessInvB`
  3. `TriominoWieferichShrinkWitnessB.toEq`
  4. `TriominoWieferichShrinkWitnessB.toInv`
  5. `TriominoWieferichShrinkWitnessB.ofEqInv`
  6. `TriominoWieferichShrinkCtorB.hW`
  7. `TriominoWieferichShrinkKernelDataB`
  8. `triominoWieferichShrinkKernelDataB_kernel`
- 変更内容:
  1. `TriominoWieferichShrinkCtorB` の witness 保持を `hW` 直持ちから `hEq / hInv` の 2 分割へ変更
  2. `triominoWieferichShrinkXYZ_kernel` は `KernelData -> XYZ + ctor` の再束ね直しだけを行う glue に変更
  3. `triominoWieferichShrinkTrace_core` は `t.ctor.hW` から完全 witness を回収するだけの形へ簡約
- 意図:
  - witness のうち「等式と順序」と「不変量」を型レベルで切り離し、
    最後の未解決点を将来的に `Eq` 側へ集中させやすい形に整える。
  - `XYZ_kernel` 自体を配線化し、縮小変換の本丸を
    `triominoWieferichShrinkKernelDataB_kernel` 1 箇所へさらに圧縮する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelDataB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`KernelDataB` に `Nums / Eq / Inv` の切断面を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkKernelNumsB`
  2. `TriominoWieferichShrinkKernelDataB.toNums`
  3. `triominoWieferichShrinkKernelSeedB_kernel`
  4. `triominoWieferichShrinkKernelNumsB_kernel`
  5. `triominoWieferichShrinkKernelEq_of_nums`
  6. `triominoWieferichShrinkKernelInv_of_nums`
- 変更内容:
  1. `triominoWieferichShrinkKernelDataB_kernel` は canonical `Nums / Eq / Inv` を束ね直す glue に変更
  2. 既存の未解決本体は `triominoWieferichShrinkKernelSeedB_kernel` へ移し、
     `KernelDataB_kernel` 本体からは `sorry` を除去
- 意図:
  - `KernelDataB` の中に `Nums` の独立した切断面を作り、
    以後 `Eq` と `Inv` を別々に強化できる地盤を先に整える。
  - `Eq_of_nums` / `Inv_of_nums` を canonical projection にしておくことで、
    次段でどちらに未解決点を寄せるかを選べる状態へ近づける。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelSeedB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`KernelSeedB` を `Nums + Eq + Inv` の束へ再整形）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkKernelSeedB`
  2. `TriominoWieferichShrinkKernelSeedB.toData`
- 変更内容:
  1. `triominoWieferichShrinkKernelSeedB_kernel` の返り値を `KernelDataB` 直返しから、
     `n : KernelNumsB` と `hEq / hInv` を持つ `KernelSeedB` へ変更
  2. `triominoWieferichShrinkKernelNumsB_kernel` は `KernelSeedB.n` の単純投影に変更
  3. `triominoWieferichShrinkKernelEq_of_nums` / `triominoWieferichShrinkKernelInv_of_nums` は
     `KernelSeedB` からの witness 回収へ整理
  4. `triominoWieferichShrinkKernelDataB_kernel` は `KernelSeedB.toData` の完全委譲へ変更
- 意図:
  - seed 自体の形を `Nums` と `Eq / Inv` に明示分解し、
    残る本丸が「どの数値を作り、その上にどの witness を載せるか」という一点だと
    型で読める状態にする。
  - `KernelDataB_kernel` を完全 glue 化し、今後の局所化対象を
    `KernelSeedB_kernel` だけに固定する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelSeedB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`hInv` を seed から切り離し、内部 core 束へ退避）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkKernelCoreB`
  2. `TriominoWieferichShrinkKernelCoreB.toSeed`
  3. `TriominoWieferichShrinkKernelCoreB.toData`
  4. `triominoWieferichShrinkKernelCoreB_kernel`
- 変更内容:
  1. `TriominoWieferichShrinkKernelSeedB` から `hInv` を削除し、seed は `n : KernelNumsB` と `hEq` だけを持つ形へ変更
  2. `TriominoWieferichShrinkKernelSeedB.toData` は `hInv` を外部引数で受け取る形へ変更
  3. `triominoWieferichShrinkKernelSeedB_kernel` は `KernelCoreB_kernel` から seed を回収する glue に変更
  4. `triominoWieferichShrinkKernelInv_of_nums` は `KernelCoreB_kernel` から `hInv` を回収する投影に変更
  5. `triominoWieferichShrinkKernelDataB_kernel` は `KernelCoreB.toData` の完全委譲へ変更
- 意図:
  - `hInv` を seed の責務から外し、
    seed 自体を「数値生成 + 等式保持」に寄せた切断面として読めるようにする。
  - 残る未解決点を `KernelCoreB_kernel` に集約しつつ、
    以後 `Inv` を seed と独立に補題化できる形に地盤を整える。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelCoreB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（seed レベルの `Eq / Inv` 回収面を明示化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelEq_of_seed`
  2. `triominoWieferichShrinkKernelInv_of_seed`
- 変更内容:
  1. `triominoWieferichShrinkKernelEq_of_nums` は `Eq_of_seed` の `Nums` 版 wrapper に変更
  2. `triominoWieferichShrinkKernelInv_of_nums` は `Inv_of_seed` の `Nums` 版 wrapper に変更
  3. `triominoWieferichShrinkKernelDataB_kernel` は
     `KernelCoreB.toData` 直呼びをやめ、
     `KernelSeedB_kernel` と `triominoWieferichShrinkKernelInv_of_seed` を束ねる glue に変更
- 意図:
  - `Eq` と `Inv` の回収インターフェースをどちらも seed レベルで揃え、
    将来 `Eq` 側・`Inv` 側を独立に差し替えやすい形へ整理する。
  - `KernelDataB_kernel` から core 直依存を外し、
    公開面では `Seed + Inv` の二段回収だけが見える状態にする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelCoreB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`KernelCoreB_kernel` を `EqSeedCore + Inv_of_seed_core` へ分割）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelEqSeedCoreB_kernel`
  2. `triominoWieferichShrinkKernelEqSeedB_kernel`
  3. `triominoWieferichShrinkKernelInv_of_seed_core`
- 変更内容:
  1. 旧 `triominoWieferichShrinkKernelCoreB_kernel` の本体を
     `triominoWieferichShrinkKernelEqSeedCoreB_kernel` へ移し、唯一の `sorry` を eq-side helper に再配置
  2. `triominoWieferichShrinkKernelCoreB_kernel` は
     `EqSeedB_kernel` と `Inv_of_seed_core` を束ねる glue に変更
  3. `triominoWieferichShrinkKernelSeedB_kernel` は
     `KernelCoreB` 経由ではなく `EqSeedB_kernel` の完全委譲に変更
  4. `triominoWieferichShrinkKernelInv_of_seed` は
     `Inv_of_seed_core` の wrapper に変更
- 意図:
  - `KernelCoreB_kernel` 自体から未解決点を外し、
    core の責務を完全に「束ね直し」に限定する。
  - 残る本丸を eq-side helper 名の下へ移し、
    次段で `Eq` 側へさらに寄せる導線を明示する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedCoreB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`Inv_of_seed_core` に seed 引数版を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelInv_of_seed_core'`
- 変更内容:
  1. `triominoWieferichShrinkKernelInv_of_seed_core'` を、
     `s : KernelSeedB` と
     `s = triominoWieferichShrinkKernelEqSeedB_kernel ...`
     という canonicality 証明を受ける形で追加
  2. `triominoWieferichShrinkKernelInv_of_seed_core` は
     上記 seed 引数版を呼ぶ wrapper に変更
  3. `triominoWieferichShrinkKernelCoreB_kernel` は
     ローカル `s` に対して `Inv_of_seed_core' ... s rfl` を使う形に変更
  4. `triominoWieferichShrinkKernelInv_of_seed` と
     `triominoWieferichShrinkKernelDataB_kernel` も、
     既に束ねた `s` を `Inv_of_seed_core'` へ渡す形に変更
- 意図:
  - `Inv` 回収のインターフェースを「先に得た seed を使う」形へ寄せ、
    外側の glue で同じ seed を再束縛しやすくする。
  - まだ一般の seed だけでは `Inv` を証明できないため、
    当面は canonicality 証明付きの seed 引数版として整理し、
    将来 `Inv` の独立補題へ差し替える足場を作る。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedCoreB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`InvTrace` を導入し、canonicality 等式を構造体へ退避）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkKernelInvTraceB`
- 変更内容:
  1. `triominoWieferichShrinkKernelInv_of_seed_core'` の最終引数を、
     `hs : s = canonical seed` から
     `tr : TriominoWieferichShrinkKernelInvTraceB ... s`
     へ変更
  2. `triominoWieferichShrinkKernelInv_of_seed_core` は
     `let c; let s; let tr := { core := c, hs := rfl }`
     を束ねて seed 引数版を呼ぶ wrapper に変更
  3. `triominoWieferichShrinkKernelCoreB_kernel`、
     `triominoWieferichShrinkKernelInv_of_seed`、
     `triominoWieferichShrinkKernelDataB_kernel` は
     いずれも `let c; let s; let tr` の 1 回評価パターンで
     `Inv_of_seed_core'` を呼ぶ形に変更
- 意図:
  - canonicality の等式を裸で持ち回らず、
    「この seed はこの core から来た」という最小 trace に閉じ込める。
  - 外側の glue をすべて `c / s / tr` の同型パターンへ揃え、
    二重評価と証明項の重複を抑える。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedCoreB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`EqSeedCoreB_kernel` を `KernelSeedB` 直返しに変更）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelEqSeedTraceB_kernel`
- 変更内容:
  1. `TriominoWieferichShrinkKernelInvTraceB` は
     `core + hs` を持つ形から、`hInv` だけを運ぶ最小 trace に変更
  2. 旧 `triominoWieferichShrinkKernelEqSeedCoreB_kernel` の本体を
     `triominoWieferichShrinkKernelEqSeedTraceB_kernel` へ移し、
     唯一の `sorry` を eq-side trace helper に再配置
  3. `triominoWieferichShrinkKernelEqSeedCoreB_kernel` は
     `KernelCoreB` 直返しをやめ、
     `EqSeedTraceB_kernel.toSeed` による `KernelSeedB` の glue に変更
  4. `triominoWieferichShrinkKernelEqSeedB_kernel` は
     `EqSeedCoreB_kernel` の完全委譲に変更
  5. `triominoWieferichShrinkKernelInv_of_seed_core'` は
     `exact tr.hInv` で閉じる形へ簡約
  6. `triominoWieferichShrinkKernelCoreB_kernel`、
     `triominoWieferichShrinkKernelInv_of_seed`、
     `triominoWieferichShrinkKernelDataB_kernel` は
     `c.hInv` を `InvTrace.hInv` へ詰め替えて使う glue に変更
- 意図:
  - `EqSeedCoreB_kernel` の返り値を `Nums + Eq` に固定し、
    返り値の型だけ見れば「等式側 seed を作る場所」だと読める形へ寄せる。
  - `InvTrace` を本来の役割である「`Inv` を運ぶ最小追加データ」に縮め、
    将来 `Inv` の独立補題化へ差し替えやすくする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTraceB_kernel` の `sorry` 1件のみ）。

### 2026-02-28 phase-14 継続（`EqSeedTraceB_kernel` を `Nums / Eq / Inv` の named kernel へ内部分割）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel`
  2. `triominoWieferichShrinkKernelNumsCoreB_kernel`
  3. `triominoWieferichShrinkKernelEq_of_nums_core`
  4. `triominoWieferichShrinkKernelInv_of_nums_core`
- 変更内容:
  1. 旧 `triominoWieferichShrinkKernelEqSeedTraceB_kernel` の本体を
     `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` へ移し、
     唯一の `sorry` を最深部の eq-side core に再配置
  2. `triominoWieferichShrinkKernelEqSeedTraceB_kernel` は
     `Nums / Eq / Inv` の named kernel を束ねる glue に変更
  3. `triominoWieferichShrinkKernelEqSeedCoreB_kernel` は
     引き続き `EqSeedTraceB_kernel.toSeed` を返す薄い glue を維持
- 意図:
  - eq-side helper の内部にも切断面を作り、
    残る穴を「最深部の等式側 core」に固定したまま
    `Nums`・`Eq`・`Inv` の責務を名前付きで分離する。
  - 次段で `Nums` や `Inv` を no-`sorry` 化し、
    最終的な穴を `Eq` 側の式変形だけに寄せるための足場を作る。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（最深部を hidden pack に落とし、`EqSeedTraceCoreB_kernel` を glue 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
- 変更内容:
  1. 旧 `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` の本体を
     `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` へ移し、
     唯一の `sorry` を hidden pack に再配置
  2. `triominoWieferichShrinkKernelNumsCoreB_kernel`、
     `triominoWieferichShrinkKernelEq_of_nums_core`、
     `triominoWieferichShrinkKernelInv_of_nums_core` は
     hidden pack からの投影へ切り替え
  3. 新しい `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` は
     上記 `Nums / Eq / Inv` の named kernel を束ねる visible glue に変更
  4. `triominoWieferichShrinkKernelEqSeedTraceB_kernel` は
     `EqSeedTraceCoreB_kernel` の完全委譲へ変更
- 意図:
  - visible な `EqSeedTraceCoreB_kernel` を配線専用にして、
    表側の責務分離をさらに明確にする。
  - `Nums / Eq / Inv` の公開切断面を維持したまま、
    残る未解決点を hidden pack 1 箇所へ押し下げる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`Nums / Eq / Inv` の投影版を `_of_pack` に退避）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkKernelNums_of_pack`
  2. `triominoWieferichShrinkKernelEq_of_nums_of_pack`
  3. `triominoWieferichShrinkKernelInv_of_nums_of_pack`
- 変更内容:
  1. hidden pack 依存の投影版 `Nums / Eq / Inv` core を `_of_pack` 名へ退避
  2. 公開側の
     `triominoWieferichShrinkKernelNumsCoreB_kernel`、
     `triominoWieferichShrinkKernelEq_of_nums_core`、
     `triominoWieferichShrinkKernelInv_of_nums_core`
     は、新設した `_of_pack` 版への wrapper に変更
  3. visible glue（`EqSeedTraceCoreB_kernel` 以降）は
     引き続き公開側の 3 つだけを見る形を維持
- 意図:
  - 依存反転のための名前を先に確保し、
    次段で `Nums` と `Inv` を独立実装へ差し替えるレールを敷く。
  - 現時点では挙動を変えず、
    「表側は新しい kernel 枠だけを見る」構図を固定する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`Nums + Inv` を同一ソースから供給する核を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvCoreB`
  2. `triominoWieferichShrinkNumsInvCoreB_kernel`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvCoreB_kernel` を新設し、
     現時点では `_of_pack` 投影版の `n` と `hInv` を 1 束にまとめる形で実装
  2. `triominoWieferichShrinkKernelNumsCoreB_kernel` は
     上記 core の `.n` を返す形に変更
  3. `triominoWieferichShrinkKernelInv_of_nums_core` は
     同じ `NumsInvCoreB` を `let core := ...` で 1 回だけ束縛し、
     `simpa [core] using core.hInv` で回収する形に変更
- 意図:
  - `Nums` と `Inv` が将来独立実装へ差し替わる時にも、
    かならず同じ `x' y' z'` を見るように足場を固定する。
  - 次段で `triominoWieferichShrinkNumsInvCoreB_kernel` の中身だけを
    本当の独立実装へ差し替えれば、
    公開 `Nums` / `Inv` の依存反転を崩さず進められるようにする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`NumsInvRecipe` を公開差し替え点として安定化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvRecipeB.toNums`
  2. `TriominoWieferichShrinkNumsInvRecipeB.toCore`
  3. `triominoWieferichShrinkNumsInvRecipe_of_pack`
- 変更内容:
  1. `TriominoWieferichShrinkNumsInvRecipeB` から
     `KernelNumsB` / `NumsInvCoreB` への梱包を専用メソッドへ分離
  2. 既存の pack 依存レシピ本体は
     `triominoWieferichShrinkNumsInvRecipe_of_pack` へ退避
  3. 公開の `triominoWieferichShrinkNumsInvRecipeB_kernel` は
     上記 `_of_pack` 版への委譲に変更し、
     `triominoWieferichShrinkNumsInvCoreB_kernel` は
     `Recipe.toCore` を呼ぶだけの安定した梱包層に整理
- 意図:
  - 将来 `triominoWieferichShrinkNumsInvRecipeB_kernel` の中身を
    本当の独立 shrink 実装へ差し替える時に、
    公開 API 側の配線を一切触らず済むようにする。
  - 生成部（recipe）と梱包部（`toNums` / `toCore`）を分離し、
    数値候補・不変量・公開 kernel の責務境界を明確にする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`NumsInvRecipeB_kernel` の公開骨組みを固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvRecipeB_kernel` を
     単純な `_of_pack` 委譲から `by` ブロックへ変更
  2. backend の `r0` を 1 回だけ束ねたうえで、
     `x' / y' / z'` の候補定義と
     `hzlt / hpB' / hInv` の各証明を別 `have` に分離
  3. 最後に `TriominoWieferichShrinkNumsInvRecipeB` を
     明示的に束ねる形へ変更
- 意図:
  - 将来 `triominoWieferichShrinkNumsInvRecipeB_kernel` の中身を
    本当の独立 shrink 実装へ差し替える時に、
    「候補の定義」と「証明の束ね」の責務を
    そのまま保ったまま中身だけ置換できるようにする。
  - 現時点では挙動を変えず、
    `Nums + Inv` 独立実装の受け皿となる公開骨組みだけを先に固定する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（数値候補 helper を分離し、`RecipeB_kernel` の backend 参照を剥離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvCandidateB`
  2. `triominoWieferichShrinkNumsInvCandidate_of_pack`
  3. `triominoWieferichShrinkNumsInvCandidateB_kernel`
  4. `triominoWieferichShrinkNumsInvCandidate_hzlt`
  5. `triominoWieferichShrinkNumsInvCandidate_hpB'`
  6. `triominoWieferichShrinkNumsInvCandidate_hInv`
- 変更内容:
  1. `NumsInvRecipe` とは別に、
     `x' / y' / z'` だけを表す `NumsInvCandidateB` を追加
  2. 現在の `_of_pack` backend からは
     まず `Candidate` を引き出す helper を通す形に変更
  3. `hzlt / hpB' / hInv` は
     `Candidate` に対する個別 helper として回収するように整理
  4. `triominoWieferichShrinkNumsInvRecipeB_kernel` 本体は
     `CandidateB_kernel` と上記 3 helper を呼ぶだけに変更し、
     直接 `r0` backend を束ねない形へ変更
- 意図:
  - 将来 `triominoWieferichShrinkNumsInvCandidateB_kernel` の中身を
    独立 shrink の候補生成へ差し替える時に、
    `RecipeB_kernel` 本体から backend 依存を切り離したまま進められるようにする。
  - 候補生成と `hzlt / hpB' / hInv` の責務を別 helper に分け、
    置換対象をさらに局所化する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`Candidate_exists` を追加し、独立候補の存在面を先行分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_exists`
- 変更内容:
  1. `TriominoWieferichShrinkNumsInvCandidateB` について、
     `hzlt / hpB' / hInv` を備えた候補の存在を返す
     `triominoWieferichShrinkNumsInvCandidate_exists` を追加
  2. 現時点では `_of_pack` backend を witness に使って
     上記存在定理を閉じる形に留め、
     将来の独立 shrink 実装を差し込む数学の受け皿を先に確保
  3. 一度 `CandidateB_kernel := Classical.choose ...` への切替も試したが、
     このファイルの定義鎖が広く computable なため
     noncomputable 連鎖が発生したので採用せず、
     `CandidateB_kernel` 自体は引き続き computable wrapper に戻した
- 意図:
  - `CandidateB_kernel` の実装戦略とは独立に、
    「独立 shrink 候補が存在する」という数学本体を
    別定理へ先に押し出しておく。
  - 将来、周辺定義を noncomputable 化するか、
    あるいは computable な選択手段へ置換するかの判断を
    後回しにしつつ、候補生成の証明面だけ先に育てられるようにする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`CandidateSpecB` を導入し、候補の証明責務を 1 定理へ集約）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvCandidateSpecB`
  2. `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel`
- 変更内容:
  1. `TriominoWieferichShrinkNumsInvCandidateB` に対して
     `hzlt / hpB' / hInv` を束ねる `Prop` 構造体
     `TriominoWieferichShrinkNumsInvCandidateSpecB` を追加
  2. `_of_pack` backend 由来の証明回収は
     `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel`
     1 本へ集約
  3. `triominoWieferichShrinkNumsInvCandidate_exists` は
     `CandidateB_kernel` と上記 `Spec` を束ねるだけの薄い包装に変更
  4. `triominoWieferichShrinkNumsInvCandidate_hzlt` /
     `triominoWieferichShrinkNumsInvCandidate_hpB'` /
     `triominoWieferichShrinkNumsInvCandidate_hInv`
     は、`Spec_of_kernel` の射影へ変更
- 意図:
  - 独立 shrink 実装へ差し替える時の置換点を
    `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel` 1 箇所へ固定し、
    helper・存在定理・`RecipeB_kernel` の配線を以後触らずに済むようにする。
  - `CandidateB_kernel` 自体は computable のまま保ちつつ、
    証明責務だけを `Spec` 側へ押し込める。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`RecipeB_kernel` も `Candidate + Spec` の包装へ統一）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec`
- 変更内容:
  1. `TriominoWieferichShrinkNumsInvCandidateB` と
     `TriominoWieferichShrinkNumsInvCandidateSpecB` から
     `TriominoWieferichShrinkNumsInvRecipeB` を復元する
     `ofCandidateSpec` を追加
  2. `triominoWieferichShrinkNumsInvRecipeB_kernel` は
     `CandidateB_kernel` と `CandidateSpec_of_kernel` を受け、
     `ofCandidateSpec` で梱包するだけの薄い層へ変更
- 意図:
  - `RecipeB_kernel` 側も
    `CandidateB_kernel + CandidateSpec_of_kernel`
    だけを見る構図に揃え、
    将来の独立 shrink 実装差し替えで
    `Recipe` 側の束ねロジックを一切触らずに済むようにする。
  - 公開の `Nums + Inv` パイプライン全体を
    「候補生成」と「仕様証明」の 2 本柱へ完全に揃える。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（独立 shrink の前処理として `q ∣ x` / `q ∤ y` を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrink_q_dvd_x`
  2. `triominoWieferichShrink_q_not_dvd_y`
- 変更内容:
  1. `PrimeGe5CounterexamplePack.xpow_eq_gap_mul_GN` と
     `hqpow_dvd_GN : q^p ∣ GN p (z - y) y` から、
     `q ∣ x` を回収する補題
     `triominoWieferichShrink_q_dvd_x` を追加
  2. 上記 `q ∣ x` と元の `hpack.hxy : Nat.Coprime x y` から、
     `q ∤ y` を回収する補題
     `triominoWieferichShrink_q_not_dvd_y` を追加
- 意図:
  - 次段で `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel`
    を独立 shrink の実証へ置き換える際に、
    `hInv`（とくに非零・互いに素）の前処理として必要になる
    `q` の整除情報を先に独立補題として固定する。
  - 候補式に依存しない純算術部分を先に切り出し、
    `Spec_of_kernel` 本体の差し替えを軽くする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`Spec_of_kernel` の `hInv` を部分的に backend 非依存化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrink_hz0_of_hpB'`
- 変更内容:
  1. `hpB' : ¬ p ∣ (z' - y')` から `z' ≠ 0` を直ちに回収する
     汎用補題 `triominoWieferichShrink_hz0_of_hpB'` を追加
  2. `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel` は
     `let c := CandidateB_kernel ...` を先に束ね、
     `hzlt` と `hpB'` を個別 `have` に分離
  3. 同定義内の `hInv` は構造体フィールドごとに組み立て直し、
     `hxy' / hx0' / hy0'` は当面 `_of_pack` 由来のまま回収しつつ、
     `hz0'` だけは新補題により `hpB'` から独立に導出する形へ変更
  4. あわせて `triominoWieferichShrink_hz0_of_hpB'` のシグネチャを最小化し、
     `unnecessarySimpa` / `unusedVariables` 系の linter warning を除去
- 意図:
  - `Spec_of_kernel` の `hInv` を段階的に独立化し、
    まずは `hz0'` を backend 非依存へ切り出すことで、
    次段で `hx0' / hy0' / hxy'` を順に独立化しやすくする。
  - 補題の責務を小さく分け、
    `Spec_of_kernel` を「前処理」「`hpB'`」「`hInv` 組み立て」に分割する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`hInv` の残り 3 フィールドを named helper へ分離）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hxy_core`
  2. `triominoWieferichShrinkNumsInvCandidate_hx0_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hy0_core`
  4. `triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel`
- 変更内容:
  1. `hInv` の残り backend 依存フィールド
     `hxy' / hx0' / hy0'` を、
     それぞれ独立した named helper として切り出し
  2. `hpB'` から `hz0'` を作る既存補題
     `triominoWieferichShrink_hz0_of_hpB'` と合わせて、
     `TriominoWieferichShrinkWitnessInvB` 全体を組む
     `triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel`
     を追加
  3. `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel` は
     `hInv` を直接組み立てる代わりに、
     上記 `InvCore_of_kernel` を呼ぶだけの形へ変更
- 意図:
  - 次段で `hy0'` → `hx0'` → `hxy'` を順に独立実装へ差し替える際に、
    `Spec_of_kernel` 本体を触らず、
    該当 helper だけを置換できるようにする。
  - `hInv` の依存剥離をフィールド単位へさらに押し進め、
    backend 参照の局所化を徹底する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`hy0_core` の独立化に向けた差し替え点を固定）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrink_hy0_of_eq_y`
  2. `triominoWieferichShrinkNumsInvCandidate_hy0_of_pack`
- 変更内容:
  1. `y' = y` が示せれば
     元の `hpack.hy0` から `y' ≠ 0` を回収できる
     汎用補題 `triominoWieferichShrink_hy0_of_eq_y` を追加
  2. 既存の pack 依存な `hy0'` 回収本体は
     `triominoWieferichShrinkNumsInvCandidate_hy0_of_pack` へ退避
  3. 公開の `triominoWieferichShrinkNumsInvCandidate_hy0_core` は
     上記 `_of_pack` 版への wrapper に変更し、
     次段でこの wrapper 本体だけ差し替えればよい形に整理
- 意図:
  - 次に `CandidateB_kernel` の独立候補で `y' := y`（あるいはそれに近い形）
    を入れた時に、
    `hy0_core` だけを `triominoWieferichShrink_hy0_of_eq_y`
    ベースへ置換できるようにする。
  - `hInv` の 3 フィールドのうち、
    もっとも軽い `hy0'` から差し替えを始めるためのレールを先に敷く。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`hy0_core` の独立ルートを先行追加し、`InvCore` を `let c` 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hy0_of_eq_core`
- 変更内容:
  1. 公開 `CandidateB_kernel` に対して
     `y' = y` が示せれば `hy0'` を直ちに回収できる
     `triominoWieferichShrinkNumsInvCandidate_hy0_of_eq_core` を追加
  2. `triominoWieferichShrinkNumsInvCandidate_hy0_core` は
     `let c := CandidateB_kernel ...` を先に束ね、
     `hy0_of_pack` から `simpa [c]` で回収する形へ整理
  3. `triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel` も
     `let c := CandidateB_kernel ...` と
     `have hpB'' : ¬ p ∣ (c.z' - c.y')` を先に置き、
     `hxy' / hx0' / hy0'` は `simpa [c]` で各 helper から回収、
     `hz0'` は `triominoWieferichShrink_hz0_of_hpB'` に渡す形へ整理
- 意図:
  - 将来 `CandidateB_kernel` を `y' := y` を持つ独立候補へ差し替えた時に、
    `hy0_core` 本体だけを
    `triominoWieferichShrinkNumsInvCandidate_hy0_of_eq_core`
    経由へ即座に切り替えられるようにする。
  - `InvCore_of_kernel` の巨大展開を抑え、
    以後の独立化で `simp` の爆発を避けやすくする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`hx0` / `hxy` も独立ルートを先行追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrink_hx0_of_eq_mul_right`
  2. `triominoWieferichShrink_hxy_of_eq_mul_eq_y`
  3. `triominoWieferichShrinkNumsInvCandidate_hx0_of_eq_mul_core`
  4. `triominoWieferichShrinkNumsInvCandidate_hxy_of_eq_mul_eq_core`
  5. `triominoWieferichShrinkNumsInvCandidate_hx0_of_pack`
  6. `triominoWieferichShrinkNumsInvCandidate_hxy_of_pack`
- 変更内容:
  1. `x = q * x'` から `x ≠ 0 -> x' ≠ 0` を回収する一般補題
     `triominoWieferichShrink_hx0_of_eq_mul_right` を追加
  2. `x = q * x'` と `y' = y` から
     元の `Nat.Coprime x y` を `Nat.Coprime x' y'` へ引き戻す一般補題
     `triominoWieferichShrink_hxy_of_eq_mul_eq_y` を追加
  3. 公開 `CandidateB_kernel` 向けに、
     上記一般補題をそのまま使う
     `hx0_of_eq_mul_core` / `hxy_of_eq_mul_eq_core` を追加
  4. 既存の pack 依存な `hx0' / hxy'` 回収本体は
     `_of_pack` へ退避
  5. 公開の `hx0_core` / `hxy_core` は
     `let c := CandidateB_kernel ...` を置いた wrapper に変更し、
     次段で wrapper 本体だけ差し替えればよい形へ整理
- 意図:
  - `hy0` と同じく、`hx0` と `hxy` も
    「pack 退避」「公開 wrapper」「独立ルート」の三層構造へ揃え、
    helper を順に独立実装へ置換できるようにする。
  - 将来 `CandidateB_kernel` が
    `x = q * x'` と `y' = y` を満たす独立候補に変わった時に、
    `hx0_core` / `hxy_core` を 1 補題呼び出しへ即座に切り替えられるようにする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`x' = x / q` ルートを先行追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hx0_of_div_core`
  2. `triominoWieferichShrinkNumsInvCandidate_hxy_of_div_eq_core`
- 変更内容:
  1. `q ∣ x` と `x' = x / q` から
     `x = q * x'` を `Nat.mul_div_cancel'` で回収し、
     既存の `hx0_of_eq_mul_core` に渡して `hx0'` を得る
     `triominoWieferichShrinkNumsInvCandidate_hx0_of_div_core` を追加
  2. 同じ `x = q * x'` と `y' = y` を使い、
     既存の `hxy_of_eq_mul_eq_core` に渡して `Nat.Coprime x' y'` を得る
     `triominoWieferichShrinkNumsInvCandidate_hxy_of_div_eq_core` を追加
  3. 途中の等式変形で `unnecessarySimpa` が出た箇所は
     `simpa` から `simp` へ落として linter warning を除去
- 意図:
  - 将来 `CandidateB_kernel` を
    `x' := x / q`, `y' := y`
    を持つ独立候補へ差し替えた時に、
    `hx0_core` / `hxy_core` を
    既存の “eq-mul ルート” へ即座に接続できるようにする。
  - `CandidateB_kernel` の候補式変更に先立って、
    `x / q` を使う独立実装ルートを証明側へ先に敷く。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-01 phase-14 継続（`hzlt / hpB'` も helper-localize）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hzlt_of_pack`
  2. `triominoWieferichShrinkNumsInvCandidate_hzlt_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hpB'_of_pack`
  4. `triominoWieferichShrinkNumsInvCandidate_hpB'_core`
- 変更内容:
  1. `hzlt` と `hpB'` についても、
     `hInv` 系 helper と同じく
     「pack 依存 backend」+「公開 wrapper」の二層を追加
  2. `triominoWieferichShrinkNumsInvCandidateSpec_of_kernel` から
     `r0 := triominoWieferichShrinkNumsInvRecipe_of_pack ...` の
     直参照を除去
  3. `Spec_of_kernel` は
     `triominoWieferichShrinkNumsInvCandidate_hzlt_core` と
     `triominoWieferichShrinkNumsInvCandidate_hpB'_core` を呼ぶだけの形へ変更
- 意図:
  - `Spec_of_kernel` から backend 直参照を消し、
    pack 依存を helper-localize する。
  - 次段で `CandidateB_kernel` の候補式を差し替える際に、
    `hzlt_core` / `hpB'_core` だけを独立実装へ置換すれば済む状態へ寄せる。
  - ただちに `CandidateB_kernel` を変えると
    `Eq_of_nums_core` の pack bridge まで同時に崩れるため、
    先に `Spec` 側の依存面を局所化して変更範囲を絞る。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-02 phase-14 継続（`Eq_of_nums_core` も helper-localize）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidateEq_of_pack`
  2. `triominoWieferichShrinkNumsInvCandidate_hEq_of_pack`
  3. `triominoWieferichShrinkNumsInvCandidate_hyz_of_pack`
  4. `triominoWieferichShrinkNumsInvCandidate_hyzLt_of_pack`
  5. `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel`
- 変更内容:
  1. `CandidateB_kernel` 向けの `Eq` backend を pack 依存 helper に退避
  2. `hEq' / hyz' / hyzLt` の field helper を追加し、
     将来 `CandidateB_kernel` 差し替え時の transport を helper 側へ局所化
  3. `triominoWieferichShrinkKernelEq_of_nums_core` は
     直接 `_of_pack` へ `simpa` する形をやめ、
     `NumsInvCandidateEqCore_of_kernel` 経由の wrapper へ変更
- 意図:
  - `InvCore_of_kernel` と同じ流儀で `Eq` 側も helper-localize し、
    `CandidateB_kernel` を将来差し替える際に
    `Eq_of_nums_core` の壊れ方を `EqCore_of_kernel` まわりへ閉じ込める。
  - `Spec_of_kernel` と同様に、公開側は薄皮を維持しつつ、
    transport の変更点を小さく保つ。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

## 2026-03-03 phase-14 継続（Spec 側も shadow-first に寄せる）

- 変更ファイル:
  - `DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
- 追加:
  - `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel`
- 更新:
  1. `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel`
  2. `triominoWieferichShrinkNumsInvCandidate_hzlt_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hpB'_core`
- 意図:
  - `_of_pack` backend と shadow 候補の fieldwise 一致を、
    trace 経由の `hxdiv / hy'` 供給付き helper に一本化した。
  - `EqCore_of_kernel` は、個別に `hxdiv / hy'` を組み立てず、
    `..._of_pack_shadow_fields_of_kernel` から shadow への一致を回収する形に簡素化した。
  - `hzlt_core / hpB'_core` も pack 直結の `simpa` 委譲をやめ、
    backend の性質を一度 shadow 側へ運んでから current kernel へ rewrite する
    shadow-first ルートへ切り替えた。
- 実装メモ:
  - `hzlt_core` は `Recipe_of_pack.hzlt` から backend の `< z` を作り、
    `z'` の一致だけで shadow/current へ運んだ。
  - `hpB'_core` は `Recipe_of_pack.hpB'` から backend の `¬ p ∣ (z' - y')` を作り、
    `y' / z'` の一致で shadow へ運んだ後、current kernel へ戻した。
  - `hpB'_core` の transport は `simpa` 一発では通らず、
    いったん `hp_div` を current `c` 側に正規化してから shadow 側へ移す形に直した。
- 効果:
  - `Spec` 側も `Eq` と同じく、shadow-first の一本化された transport ルートに揃った。
  - `CandidateB_kernel` 差し替え時に壊れる場所は、さらに `Spec` helper 群に閉じた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-02 phase-14 継続（`EqCore_of_kernel` を field-level wrapper まで分解）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hEq_core`
  2. `triominoWieferichShrinkNumsInvCandidate_hyz_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hyzLt_core`
- 変更内容:
  1. `triominoWieferichShrinkKernelEq_of_nums_core` は
     `EqCore_of_kernel` を丸ごと参照する形をやめ、
     `hEq_core / hyz_core / hyzLt_core` の field-level wrapper から
     `TriominoWieferichShrinkWitnessEqB` を再構成する形へ変更
- 意図:
  - `Eq` 側も `Inv` 側と同じく
    「field helper -> core helper -> wrapper」の三層へ揃え、
    将来 `CandidateB_kernel` を差し替えた時の破損点を
    `hEq_core / hyz_core / hyzLt_core` にさらに局所化する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-02 phase-14 継続（`CandidateB_kernel` 差し替え前の影候補を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow`
  2. `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x`
  3. `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y`
  4. `triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z`
- 意図:
  - 公開 `CandidateB_kernel` をまだ切り替えずに、
    次段で採用したい
    `x' := x / q`, `y' := y`
    の候補形を先に独立定義として固定する。
  - `z'` は当面 `_of_pack` backend の値を流用し、
    `Eq / hzlt / hpB'` 側 helper の追随先を先に観察できるようにする。
  - これにより、最終的な差し替えは
    `CandidateB_kernel := ..._div_eq_shadow`
    の一行変更に近づける。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-02 phase-14 継続（shadow 向け `Inv` helper を先行追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hy0_shadow_core`
  2. `triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hxy_shadow_core`
- 意図:
  - 公開 `CandidateB_kernel` はまだ据え置きのまま、
    影候補 `div_eq_shadow` に対して `hy0 / hx0 / hxy` が
    独立ルートで落ちることを先に確定する。
  - 次段で public kernel を shadow へ差し替える際、
    `InvCore_of_kernel` 側は参照の差し替えだけで追随できる状態に近づける。
- 実装メモ:
  - `hy0` は `y' = y` を `simp` で回収して `triominoWieferichShrink_hy0_of_eq_y` へ接続。
  - `hx0 / hxy` は `q ∣ x` から `x = q * (x / q)` を作り、
    `x' = x / q`, `y' = y` の shadow 定義へ接続する形。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-02 phase-14 継続（shadow 差し替え前の fieldwise gate を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq`
- 意図:
  - 無条件の `kernel = shadow` は、現状の backend が `sorry` を含むため
    そのまま証明対象にすると依存型の等値で不安定になりやすい。
  - 代わりに、
    `x' = x / q` と `y' = y`
    が示せた場合に、
    `_of_pack` backend と `div_eq_shadow` が
    `x' / y' / z'` の 3 フィールドで一致することを示す “gate” を追加した。
  - これにより、public kernel 差し替え前に
    「本当に同じ triple を見ているか」を helper レベルで判定できる。
- 実装メモ:
  - 構造体の等値そのものではなく、fieldwise 一致（3 本の equality）の conjunction に落とした。
  - `z'` は shadow が backend 流用なので `.symm` で即回収。
  - `kernel` ではなく `_of_pack` を対象にした。
    `CandidateB_kernel` への public wrapper も検討したが、
    定義順の都合で前方参照になり、現段階では実益が薄いため見送った。
    まずは `_of_pack` backend について
    `x' = x / q` と `y' = y`
    が実際に示せるかを判定する用途に限定する。
- 判断:
  - `triominoWieferichShrinkKernelNums_of_pack` は
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`（残る唯一の `sorry`）の投影なので、
    `_of_pack` backend の `x' / y'` は現時点では opaque。
  - したがって、public `CandidateB_kernel` を shadow へ差し替える前に、
    まず `_of_pack` backend 側で `hxdiv / hy'` が本当に証明できるかを確認する必要がある。
    ここが通らなければ、差し替えは単なる refactor ではなく数学内容の更新になる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`Eq` を `hEq' + hx0'` から再構成）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkWitnessEq_of_eq_and_hx0`
- 変更内容:
  1. `triominoWieferichShrinkKernelEq_of_nums_core`
- 意図:
  - shadow triple 用の独立 `Eq` 実装で、
    `hyz' / hyzLt` を transport せずに
    `hEq' : x'^p + y'^p = z'^p`
    と `hx0' : x' ≠ 0`
    だけから再構成できる形へ寄せた。
  - これにより、`Eq` 側の真の数学負担を `hEq'` 1本へさらに圧縮した。
- 実装メモ:
  - `x' ≠ 0` から `0 < x'`、さらに `0 < x'^p` を作り、
    `y'^p < x'^p + y'^p = z'^p` を得る。
  - `z' ≤ y'` を仮定すると `z'^p ≤ y'^p` となって矛盾するので、
    `y' < z'` を回収し、`y' ≤ z'` はそこから従わせた。
  - `triominoWieferichShrinkKernelEq_of_nums_core` は
    もはや `hyz_core / hyzLt_core` に依存せず、
    `hEq_core` と `hx0_core` だけから `WitnessEq` を組む。
- 効果:
  - `CandidateB_kernel` を将来差し替えたとき、
    `Eq` 側で本質的に作り直す必要があるのは `hEq'` だけになった。
  - `hyz_core / hyzLt_core` は依然 helper として残すが、
    公開 `Eq_of_nums_core` の依存からは外れた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（gate 付き shadow `Eq` を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack`
  2. `triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack`
- 意図:
  - 現段階では `_of_pack` backend の `x' / y'` は opaque で、
    `x' = x / q`, `y' = y` は自動では出ない。
  - そこで、将来 `hxdiv / hy'` が供給できた瞬間に、
    backend の `hEq'` を shadow triple へ運んで
    shadow `Eq` witness を即座に起動できる “gate 付き” ルートを先に敷いた。
- 実装メモ:
  - `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack` は、
    backend の `hEq'` を `triominoWieferichShrinkNumsInvCandidate_hEq_of_pack` から取り出し、
    `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq` の fieldwise gate
    (`x' / y' / z'` 一致) を使って shadow 側へ rewrite する。
  - `simp` での全体 rewrite は再帰が深くなりやすかったため、
    最終段は `rw [← hz, ← hy, ← hx]` の順で明示的に backend 側へ戻して `hEqb` を適用した。
  - `triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack` は、
    `hx0'` を `triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core` から回収し、
    `triominoWieferichShrinkWitnessEq_of_eq_and_hx0` で `Eq` witness を完成する。
- 効果:
  - まだ public `CandidateB_kernel` は据え置きのままでも、
    `hxdiv / hy'` さえ後から取り出せれば shadow `Eq` まで一気に配線できる状態になった。
  - つまり、shadow 差し替え前の判定フェーズと、差し替え後の `Eq` 追随の間に
    “橋” が一本追加された形。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（shadow `Eq` の gate を接続）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack`
  2. `triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack`
- 意図:
  - `Candidate_of_pack` backend の `x' / y'` は依然 opaque だが、
    将来 `hxdiv : x' = x / q` と `hy' : y' = y` が取り出せた瞬間に、
    backend の `hEq'` を shadow triple へ運び、
    shadow 側の `Eq` witness を即時に起動できるようにした。
  - つまり、shadow 差し替え前の “判定フェーズ” と
    shadow 差し替え後の “Eq 追随” の間に、gate 付きの接続橋を追加した。
- 実装メモ:
  - `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack` は、
    `triominoWieferichShrinkNumsInvCandidate_hEq_of_pack` から backend の `hEq'` を取得し、
    `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq`
    で得た `x' / y' / z'` の fieldwise 一致を用いて shadow 側へ移送する。
  - `simpa` での一括 rewrite は recursion depth に当たりやすかったため、
    最終段は `rw [← hz, ← hy, ← hx]` で backend 側へ戻して `hEqb` を刺す形に安定化した。
  - `triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack` は、
    `hx0'` を `triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core` から回収し、
    `triominoWieferichShrinkWitnessEq_of_eq_and_hx0` で `Eq` witness を完成する。
  - 追加位置は前方参照を避けるため、
    `triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core` など既存 helper の後ろへ置いた。
- 効果:
  - まだ public `CandidateB_kernel` は据え置きのままでも、
    `hxdiv / hy'` を kernel の仕様として外へ出せた瞬間に、
    shadow 側の `Eq` を独立 route で完成できる。
  - これにより、shadow 差し替えの前提条件が “helper で使える形” に固定された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（kernel interface に `hxMul / hyEq` を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkKernelCoreB` に
     - `hxMul : x = q * s.n.x'`
     - `hyEq : s.n.y' = y`
     を追加
  2. 上記 2 フィールドを
     - `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel`
     - `triominoWieferichShrinkKernelCoreB_kernel`
     で透過させるよう更新
  3. backend からの projection helper を追加
     - `triominoWieferichShrinkKernel_hxmul_of_pack`
     - `triominoWieferichShrinkKernel_hy_eq_of_pack`
  4. candidate レベルの helper を追加
     - `triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack`
     - `triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack`
     - `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack`
  5. gate を仮定なしで起動する wrapper を追加
     - `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_via_trace_of_pack`
     - `triominoWieferichShrinkNumsInvCandidateEq_shadow_via_trace_of_pack`
- 意図:
  - `_of_pack` backend の `x' / y'` は、唯一の `sorry` の投影なので opaque。
  - そのため、外側から定義展開で `x' = x / q` や `y' = y` を取り出す代わりに、
    それらのリンク命題を kernel interface 自体に昇格させた。
  - これで、既存の gate 付き shadow `Eq` ルートを
    “仮定付きの橋” から “trace を介して起動できる橋” へ格上げした。
- 実装メモ:
  - `hxMul` は `x' = x / q` よりも自然なリンクとして保持し、
    `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack` で必要時に `x / q` 形へ変換する。
  - `hyEq` はそのまま projection で外に出し、shadow `Eq` 側へ直接渡せる形にした。
  - 変更は interface の拡張だけで、唯一の `sorry`
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
    自体の数理は触っていない。
- 効果:
  - `hxMul / hyEq` が opaque backend の外側へ出たので、
    shadow `Eq` は trace wrapper 経由で起動可能になった。
  - 以後の作業は、public `CandidateB_kernel` 差し替え前でも
    “リンク命題が使えるかどうか” を helper 群で試せる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`CandidateB` の `LinkSpec` を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `TriominoWieferichShrinkNumsInvCandidateLinkSpecB`
  2. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack`
  3. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel`
- 意図:
  - `CandidateSpecB` はそのままにして、
    `hxMul / hyEq` の供給路だけを別仕様へ 1 本化した。
  - 以後、public `CandidateB_kernel` について
    `x = q * x'`, `y' = y`
    を参照したいときは `LinkSpec` だけを見ればよくなる。
- 実装メモ:
  - `LinkSpec_of_pack` は既存の
    `triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack`
    と
    `triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack`
    を単純に束ねる。
  - `LinkSpec_of_kernel` は `triominoWieferichShrinkNumsInvCandidateB_kernel` が
    現状 `_of_pack` への委譲であることを `simpa` で使う薄い wrapper。
  - 追加位置は定義順に合わせ、`LinkSpec_of_kernel` は public kernel 定義の後ろへ置いた。
- 効果:
  - `hxMul / hyEq` を参照する将来の helper は、個別 projection を直接見る必要がなくなった。
  - public `CandidateB` 側へのリンク露出が 1 箇所に集約され、shadow 差し替え前の staging が軽くなった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`Inv` core を `LinkSpec` 経由へ切替）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvCandidate_hxy_core`
  2. `triominoWieferichShrinkNumsInvCandidate_hx0_core`
  3. `triominoWieferichShrinkNumsInvCandidate_hy0_core`
- 意図:
  - `hInv` の opaque な `_of_pack` 投影に依存していた 3 本を、
    `TriominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel` と
    既存の独立核補題
    (`..._hxy_of_eq_mul_eq_core`, `..._hx0_of_eq_mul_core`, `..._hy0_of_eq_core`)
    だけで回る形へ置き換えた。
  - これで `Inv` 側は、public `CandidateB_kernel` の
    `hxMul / hyEq` が保たれる限り、backend の `hInv` 実体に依存しなくなった。
- 実装メモ:
  - 3 本とも、まず `hL := triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel ...`
    を置き、そこから
    - `hL.hxMul`
    - `hL.hyEq`
    を既存 core 補題へ流すだけの形にした。
  - 既存の `*_of_pack` helper は残しており、切替は public core helper の参照面だけに留めた。
- 効果:
  - public `CandidateB_kernel` を shadow へ差し替える前段として、
    `Inv` 側の依存はさらに軽くなった。
  - 今後 `CandidateB_kernel` の数値候補を動かしても、`Inv` 側で壊れる可能性があるのは
    `LinkSpec_of_kernel` の供給だけになった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`EqCore_of_kernel` を gate 正規ルートへ切替）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel`
- 意図:
  - `EqCore_of_kernel` が直接
    - `hEq_of_pack`
    - `hyz_of_pack`
    - `hyzLt_of_pack`
    に依存していた経路をやめ、
    shadow gate と `hx0'` 再構成を使う正規ルートへ寄せた。
  - これで `Eq` 側も、`Inv` と同様に opaque backend の生 witness から距離を取った。
- 実装メモ:
  - local で
    - `c := CandidateB_kernel`
    - `cs := div_eq_shadow`
    - `hL := LinkSpec_of_kernel`
    を置いた。
  - `hxdiv` と `hy'` は既存の
    - `triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack`
    - `triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack`
    から供給。
  - `of_pack_shadow_fields_of_eq` で backend と shadow の fieldwise 一致を作り、
    `shadow` 側の `hEq'` を current kernel 側へ rewrite して回収した。
  - `hyz' / hyzLt` は持ち回らず、`hx0'` と `hEq'` から
    `triominoWieferichShrinkWitnessEq_of_eq_and_hx0`
    で再構成する形に統一した。
  - 定義順の都合で後方参照ができないため、
    `hEq_shadow_via_trace_of_pack` や `hx0_core` は直接呼ばず、
    その中身を `EqCore_of_kernel` 内で局所展開した。
- 効果:
  - `EqCore_of_kernel` の依存は、
    - `LinkSpec_of_kernel`
    - fieldwise gate
    - `hEq_of_pack`
    の組み合わせに整理された。
  - 今後 public `CandidateB_kernel` を shadow に寄せる際、
    `Eq` 側の主な修正点は `hEq'` の供給路だけにさらに近づいた。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（public `CandidateB_kernel` を shadow 候補へ切替）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvCandidateB_kernel`
  2. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel`
  3. `triominoWieferichShrinkNumsInvCandidateEq_of_pack`
  4. `triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel`
  5. `triominoWieferichShrinkNumsInvCandidate_hzlt_of_pack`
  6. `triominoWieferichShrinkNumsInvCandidate_hzlt_core`
  7. `triominoWieferichShrinkNumsInvCandidate_hpB'_of_pack`
  8. `triominoWieferichShrinkNumsInvCandidate_hpB'_core`
  9. `triominoWieferichShrinkNumsInvCandidate_hxy_of_pack`
  10. `triominoWieferichShrinkNumsInvCandidate_hx0_of_pack`
  11. `triominoWieferichShrinkNumsInvCandidate_hy0_of_pack`
  12. `triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack`
  13. `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel`
- 意図:
  - public `CandidateB_kernel` を
    `x' := x / q`, `y' := y`, `z' := backend z'`
    の shadow 候補へ切り替えた。
  - それに伴い、`Inv / Eq / Spec` の各 helper を
    「backend の性質を shadow に運び、最後に current kernel へ戻す」
    形へ寄せ、差し替え後も外側配線が壊れないようにした。
- 実装メモ:
  - `LinkSpec_of_kernel` は、もう `_of_pack` への単純 `simpa` ではなく、
    `LinkSpec_of_pack` と
    `triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel`
    から `hxMul / hyEq` を current kernel へ transport する。
  - `Eq_of_pack` / `EqCore_of_kernel` は、`hEq'` を
    backend 側から fieldwise rewrite で current kernel に運び、
    `triominoWieferichShrinkWitnessEq_of_eq_and_hx0`
    で `hyz' / hyzLt` を再構成する流儀に統一した。
  - `hzlt_of_pack` / `hpB'_of_pack` は、backend の性質を一度 shadow 候補へ移し、
    `hzlt_core` / `hpB'_core` はそこから current kernel に戻す形へ変更した。
  - `Inv` の pack helper (`hxy_of_pack` / `hx0_of_pack` / `hy0_of_pack`) も、
    opaque backend の `hInv` 投影をやめ、`LinkSpec_of_kernel` の
    `hxMul / hyEq` から独立に再構成する形へ揃えた。
  - `hEq_shadow_of_pack` は、current kernel がすでに shadow 候補であるため、
    backend→shadow transport をやめ、現行 kernel の `hEq_of_pack` を
    直接使う薄い wrapper に簡約した。
  - `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` も、
    `c.hxMul / c.hyEq` ではなく current `CandidateB_kernel` の
    `LinkSpec_of_kernel` から `hxMul / hyEq` を回収する形に更新した。
- 効果:
  - public `CandidateB_kernel` の数値候補は、ついに shadow 形へ切り替わった。
  - `Inv` は `LinkSpec` 依存、`Eq` は gate + shadow-first、`Spec` も shadow-first の構図を維持したまま、公開候補を更新できた。
  - 残る不確定要素は引き続き `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件に閉じている。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（current-path から不要な pack-kernel 参照を除去）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel`
- 意図:
  - current-path の glue から、`triominoWieferichShrinkKernelEqSeedTracePackB_kernel` への未使用参照を 1 本除去し、
    main path の `sorry` 依存を少しでも薄くする。
- 実装メモ:
  - `triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel` 冒頭の
    `let c := triominoWieferichShrinkKernelEqSeedTracePackB_kernel ...`
    は、実際には以後使われていなかったため削除した。
  - 現在の `EqSeedTraceCoreB_kernel` は
    `NumsCore / EqCore / InvCore / LinkSpec_of_kernel`
    だけで構成される。
- 効果:
  - 残る `sorry` 自体は変わらないが、少なくとも current-path の glue は
    `pack-kernel` を直接参照しない構造へ一段寄った。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（current-path の `hxMul / hyEq` 投影を追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkKernel_hxmul_of_core_path`
  2. `triominoWieferichShrinkKernel_hy_eq_of_core_path`
- 意図:
  - 既存の early `_of_pack` 投影は定義順の都合で legacy なまま残しつつ、
    current-path (`KernelCoreB_kernel -> KernelNumsB_kernel`) から
    `hxMul / hyEq` を直接見る投影を追加しておく。
  - これにより、後続の整理や将来の置換で
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel`
    を経由しない参照面を増やせる。
- 実装メモ:
  - どちらも `c := triominoWieferichShrinkKernelCoreB_kernel ...` を置き、
    `c.hxMul / c.hyEq` を
    `KernelNumsB_kernel = c.s.n`
    へ `simpa` で投影するだけの薄い定理にした。
  - 既存の `_of_pack` 投影は前方参照制約があるため、そのまま維持した。
- 効果:
  - すぐに既存呼び出しを置き換えてはいないが、current-path から
    `hxMul / hyEq` を直接見られる正規投影ができた。
  - main path と legacy path の境界がさらに明確になった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`LinkSpec_of_kernel` を pure route に切替）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel`
- 意図:
  - shadow kernel になった現状では、`LinkSpec_of_kernel` はもはや `_of_pack` backend からの transport に依存しなくてよい。
  - `hxMul / hyEq` を、public `CandidateB_kernel` の算術と定義展開だけで供給する形へ切り替え、依存をさらに軽くする。
- 実装メモ:
  - `hxMul` は
    - `q^p ∣ GN` から `q ∣ x` を局所に再構成し、
    - `Nat.mul_div_cancel'`
    - shadow 定義 (`x' := x / q`)
    を使って `x = q * c.x'` を直接示した。
  - `hyEq` は shadow 定義 (`y' := y`) を `simp` で回収した。
  - これにより、`LinkSpec_of_kernel` は
    - `LinkSpec_of_pack`
    - `of_pack_shadow_fields_of_kernel`
    を参照しない pure route になった。
- 効果:
  - `Inv` 側の core helper 群が依存する `LinkSpec_of_kernel` は、opaque backend transport から切り離された。
  - public `CandidateB_kernel` の外側では、`hxMul / hyEq` は now current kernel だけを見れば足りる。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（最後の `sorry` を `Seed + links` へ薄化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `TriominoWieferichShrinkKernelSeedLinkB` を追加
  2. `triominoWieferichShrinkKernelInv_of_nums_from_links` を追加
  3. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の返り値を
     `KernelCoreB` から `KernelSeedLinkB` へ変更
  4. `_of_pack` 系投影 (`Nums / Eq / Inv / hxMul / hyEq`) を新しい薄い返り値へ追随
- 意図:
  - 最後の `sorry` が直接抱えていた `Inv` witness を外へ追い出し、
    数学 kernel の責務を `Seed (Nums + Eq) + links (hxMul / hyEq)` のみに縮小する。
  - `Inv` は外側の pack 条件と `hxMul / hyEq` から再構成できるので、
    本丸の未解決点をさらに細くする。
- 実装メモ:
  - `KernelInv_of_nums_of_pack` は、もう `pack-kernel.hInv` を参照しない。
  - 代わりに `triominoWieferichShrinkKernelInv_of_nums_from_links` で
    `KernelNums + hxMul + hyEq` から `hxy' / hx0' / hy0' / hz0'` を局所再構成する。
  - `KernelEqSeedTraceCoreB_kernel` など後段の core/glue は、そのまま full `KernelCoreB` を組み直す。
- 効果:
  - 最後の `sorry` は依然 1 件だが、抱える責務は以前より軽い。
  - current-path から見たとき、`Inv` は既に “派生物” になった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（当初は残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` の `sorry` 1件）。

### 2026-03-03 phase-14 継続（最後の `sorry` を `Nums + hEq' + links` へさらに薄化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `TriominoWieferichShrinkKernelNumsEqLinkB` を追加
  2. `TriominoWieferichShrinkKernelNumsEqLinkB.toSeedLink` を追加
  3. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_core` を追加
  4. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel` を
     `kernel_core -> toSeedLink` の glue に変更
- 意図:
  - 最後の未解決点から `Eq` witness 全体をさらに外へ押し出し、
    `Nums + hEq' + links (hxMul / hyEq)` だけを本丸に残す。
  - `hyz / hyzLt` は既存の
    `triominoWieferichShrinkWitnessEq_of_eq_and_hx0`
    で再構成する。
- 実装メモ:
  - `toSeedLink` では `hx0'` を `hpack.hx0` と `hxMul` から局所再構成し、
    そこから `Eq` witness を生成する。
  - これにより、最後の `sorry` は `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_core` に移動した。
- 効果:
  - `pack-kernel` 自体は glue 化され、最後の未解決点はさらに細い内部 core へ隔離された。
  - 残る数学コアは
    `Nums + hEq' + hxMul + hyEq`
    の構成だけになった。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`q ∣ x` 導出を早期 helper へ共通化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrink_q_dvd_x_core` を追加
  2. `TriominoWieferichShrinkKernelZEqB.toNumsEqLink` の `q ∣ x` 導出を `..._q_dvd_x_core` へ置換
  3. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel` の `hxMul` 導出を `..._q_dvd_x_core` へ置換
  4. 既存 `triominoWieferichShrink_q_dvd_x` は `..._q_dvd_x_core` への thin wrapper に変更
- 意図:
  - `q^p ∣ GN` から `q ∣ x` を出す純算術を 1 箇所へ集約し、
    `LinkSpec_of_kernel` と `toNumsEqLink` の重複を消す。
  - 最後の `sorry` の外側で使う arithmetic link を、さらに安定させる。
- 実装メモ:
  - `q ∣ q^p` は `pow_dvd_pow` ではなく `dvd_pow (dvd_refl q) hpack.hp.ne_zero` に切替。
  - `Inv_of_nums_from_links` には `z' = 0 -> p ∣ (z' - y)` の `Nat` 由来の流れを説明するコメントを追加。
- 効果:
  - `LinkSpec_of_kernel` は current shadow kernel の pure arithmetic により `hxMul / hyEq` を供給し続ける。
  - `toNumsEqLink` も同じ早期 helper を使うため、純算術の変更点が一本化された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
