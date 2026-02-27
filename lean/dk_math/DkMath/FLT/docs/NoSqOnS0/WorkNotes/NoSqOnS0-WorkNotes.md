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
