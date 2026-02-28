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
