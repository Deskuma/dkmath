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
[NoSqOnS0: phase-14](NoSqOnS0-WorkNotes-phase-14.md)

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

### 2026-03-03 phase-14 継続（`x = q * (x / q)` も core helper に共通化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrink_x_eq_q_mul_div_core` を追加
  2. `TriominoWieferichShrinkKernelZEqB.toNumsEqLink` の `hxMul` 導出を `..._x_eq_q_mul_div_core` へ置換
  3. `triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel` の `hxMul` 導出を `..._x_eq_q_mul_div_core` へ置換
- 意図:
  - `q ∣ x` の次に必ず使う `x = q * (x / q)` の算術 glue を一本化し、
    最後の `z_core` でも同じ導出を再利用できるようにする。
  - `z_core` の責務を、`z'` とその 3 条件 (`hzlt / hpB' / hEq'`) にさらに集中させる。
- 効果:
  - `LinkSpec_of_kernel` と `toNumsEqLink` の純算術は、
    `q ∣ x` に続く割り算正規化まで共有 helper で処理するようになった。
  - `z_core` 側で `hxMul` を使う必要が出ても、既存 helper を呼ぶだけで済む。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`z_core` を単一の存在ゴールへ圧縮）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` を
     直接 `sorry` を置く形から、
     `Subtype` で
     `z' < z ∧ ¬ p ∣ (z' - y) ∧ (x / q)^p + y^p = z'^p`
     をまとめて返す単一ゴールへ変更
  2. その `Subtype` から `z' / hzlt / hpB' / hEq'` を投影して
     `TriominoWieferichShrinkKernelZEqB` を構成する glue に整理
- 実装メモ:
  - いったん `Exists` + `Classical.choose` へ寄せる案を試したが、
    `noncomputable` 連鎖が下流定義全体へ波及して不適切だった。
  - そのため、`sorry` を `Type` の値として保持できる `Subtype` に戻した。
- 意図:
  - `z_core` の残る数学を
    「`z'` とその 3 条件を同時構成する」
    という 1 つの存在問題へ明確化する。
  - 外側の record glue は完全に固定し、今後の詰めをこの存在ゴールだけに集中させる。
- 効果:
  - 残る `sorry` は 1 件のまま維持。
  - `z_core` の内部責務が、候補 `z'` と
    `hzlt / hpB' / hEq'`
    の同時構成にさらに明示的に圧縮された。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`z_core` の `Subtype` 分解を平坦化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の末尾で、
     `hzCore.1 / hzCore.2` による取り出しをやめた
  2. 代わりに
     - `rcases hzCore with ⟨z', hzSpec⟩`
     - `rcases hzSpec with ⟨hzlt, hpB', hEq'⟩`
     と分解してから record を組む形に整理した
- 意図:
  - 残る本丸 `hzCore` の中身を今後詰める際に、
    「どの成分が未解決か」が見えやすい形へ整える
  - `Subtype` の投影を直接並べるより、局所補題化・差し替えがしやすい形に寄せる
- 効果:
  - 数学内容は不変
  - 残る `sorry` は引き続き `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の 1 件のみ
  - `z_core` の外形は、次に `z' / hzlt / hpB' / hEq'` を個別に詰めるための準備形になった
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（候補Aを棄却し、`z_core` を候補Bへ切替）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `triominoWieferichShrink_q_not_dvd_z` を追加
     - primitive 条件 `q ∤ (z - y)` のもとでは `q ∤ z` を示す
     - したがって候補A `z' := z / q` は数学的に自然候補として使えないことを明文化
  2. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の内部候補を
     - 候補A `z' := z / q`
     から
     - 候補B `z' := z - y`
     へ切り替えた
  3. `z_core` 内のコメントも、
     - 候補Aは `q ∤ z` で先に棄却
     - 候補Bを次の本命として詰める
     という方針に更新した
- 意図:
  - 候補Aの失敗をコード上の補題として残し、同じ検討を繰り返さないようにする
  - 残る `sorry` を、次の実験候補（gap ベースの候補B）に対する数学本体へ素直に向ける
- 効果:
  - 残る `sorry` は 1 件のまま維持
  - ただし、その中身は「候補Aを試す」段を終え、候補Bを直接詰める状態になった
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（候補Bで `hzlt` を先行実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. 候補B `z' := z - y` のもとで、
     `Nat.sub_lt` と `hpack.hz0 / hpack.hy0` から
     `hzlt : z' < z`
     を `z_core` 内で先に実装した
  2. その結果、`z_core` に残る未解決は
     - `hpB' : ¬ p ∣ (z' - y)`
     - `hEq' : (x / q)^p + y^p = z'^p`
     を与える後半の conjunction にさらに縮んだ
- 意図:
  - 候補Bで確実に先に落とせる純算術部分を先行して片付け、
    残る `sorry` を本当に必要な数学（Branch B 条件と等式）へ絞る
- 効果:
  - 残る `sorry` は 1 件のまま維持
  - ただし、その責務は候補Bに対する `hpB' + hEq'` へさらに圧縮された
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（`z_core` 前処理の算術を core helper 化）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `z_core` で後から使う算術前処理を helper に切り出した
     - `triominoWieferichShrink_xdiv_ne_zero_core`
     - `triominoWieferichShrink_xdiv_pow_pos_core`
     - `triominoWieferichShrink_zpow_eq_ypow_add_qpow_mul_xdivpow_core`
  2. `x = q * (x / q)` から
     `x / q ≠ 0` と `(x / q)^p > 0` を回収する前処理を固定した
  3. 元の反例等式を
     `z^p = y^p + q^p * (x / q)^p`
     の shadow 固定形へ正規化する helper を追加した
- 意図:
  - `z_core` の候補比較（特に `hzlt` を `z'^p < z^p` で落とすルート）で
    毎回必要になる算術 glue を本体から追い出す
  - 候補Bが詰まった場合でも、次候補で再利用できる前処理を先に共通化しておく
- 効果:
  - 残る `sorry` は 1 件のまま維持
  - `z_core` の外側で使う算術は `x = q * (x / q)` の周辺まで共有化され、
    本体はより直接に `z' / hpB' / hEq'` の比較へ集中できる形になった
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（候補B固定をやめ、generic `candidateZData` へ一段圧縮）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. 候補B固定の残差をやめ、
     `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data`
     を追加した
  2. 返り値は
     - `x' / y' / z'`
     - `hzlt`
     - `hxdiv`
     - `hyEq`
     - `hpB'`
     - `hEq'`
     を持つ最小データ構造
     `TriominoWieferichShrinkKernelCandidateZDataB`
     に固定した
  3. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ` は
     `candidateZ_data.toSubtype` の glue に変更した
  4. `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core` は、
     `candidateZ` をそのまま受け取って record へ梱包する glue に保った
- 意図:
  - false な候補Bに `sorry` を固定し続けず、
    「適切な triple と trace を供給する」最小 kernel に戻す
  - 今後、非循環の shrink candidate や新しい explicit 候補を採る場合も、
    差し替える位置を `candidateZ_data` 1 箇所に固定する
- 効果:
  - 残る `sorry` は 1 件のまま維持
  - ただし warning の位置は
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data`
    に固定された
  - `candidateZ` と `z_core` は no-`sorry` の glue になった
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（残る warning は `CosmicPetalBridgeGNDescentB.lean` の `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data` の `sorry` 1件のみ）。
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB`
  - 結果: 成功（残る warning は同じく `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data` の `sorry` 1件のみ）。

### 2026-03-03 phase-14 継続（gcd spine: `gap ⟂ GN` を非循環で確立）

- 対象:
  - `lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
- 追加:
  - `triominoWieferichShrink_gap_coprime_GN_core`
- 内容:
  1. 既に追加済みの
     `triominoWieferichShrink_gap_gcd_GN_dvd_p_int`
     を直接使い、
     `gcd (z-y, GN p (z-y) y) ∣ p` と `hpB : ¬ p ∣ (z-y)` から
     `Nat.Coprime (z-y) (GN p (z-y) y)` を導く補題を追加した
  2. 実装は、`Nat.gcd` の非自明性から共通素因子 `r` を取り、
     `r ∣ gap`, `r ∣ GN` を `Int.gcd` 側へ持ち上げ、
     `r ∣ p`、したがって `r = p` に帰着して `hpB` に矛盾させる形にした
- 意図:
  - `candidateZ_data` を explicit な `z'` 構成で殴る前に、
    Branch B の非循環な gcd spine を core helper として固める
  - ここから先、`gap * GN = x^p` と組み合わせた別ルート（coprime 分解 / 矛盾ルート）を試す足場にする
- 結果:
  - `candidateZ_data` の `sorry` はそのまま 1件
  - ただし、`gap ⟂ GN` をこのファイル内で循環なしに使えるようになった
- ビルド確認:
  - 実行: `cd lean/dk_math && lake env lean DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 結果: 成功（warning は `unnecessarySimpa` 1件と
    `triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data` の `sorry` 1件）
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
  - 結果: 成功
