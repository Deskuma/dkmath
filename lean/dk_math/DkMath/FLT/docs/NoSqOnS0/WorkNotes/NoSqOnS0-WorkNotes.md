# No Square on S0 Work Notes

status: 作業中 - phase-12: 完全証明への道（トロミノ構造の補題を実装して下降法を完成させる）

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

## 課題

- [ ] 仮定の証明
  - [ ] `NonLiftableS0` の証明（下降法）
  - [x] ただし、`GEisensteinBridge` の `descent` インターフェースは実装済み。

### トロミノ構造

想定していた「具体補題」は `TriominoFLT.lean` 側の次の鎖です。

1. `color3_L_tromino_standard`（各色1セル）
2. `color_balance_of_box_3k`（Box の色平衡）
3. `FLT_from_tromino_tiling` 本体完成
4. `FLT_case_3_via_tromino` / `FLT_general_via_tromino`

その上で、今の API には  
`hasNoSqFamily` か `hasNonLiftableFamily` を出すブリッジ補題を1本置いて接続する計画でした。

現状は `TriominoFLT.lean` に `sorry` が残っているので、まず 1→2→3 の順で埋めるのが必要です。

## 状況タスク

**現状評価**

- [ ] 3. 未充足の本丸は `NonLiftableS0` の自動生成です。  
  今は `hNonLift` を入力で受けるか、`NoSq` から逆算しています。

**phase-10 攻略法（本命）**

- [ ] 3. 上の供給を下降法（または同等の反例縮小）で埋める。  
  `GEisensteinBridge` はまだ導入段階（`lean/dk_math/DkMath/FLT/GEisensteinBridge.lean`）なので、ここが最大工数です。
- [ ] 4. 最終入口を `NoSqBaseInput` 一発に統合。  
  `lean/dk_math/DkMath/FLT/Main.lean:334` を最終公開入口にし、他はラッパーに寄せる。

**保険ルート**

- [ ] 1. 「まず完全定理を公開したい」なら、既存 `Basic` 系（`FLT_case_3`, `FLT`）への橋定理を先に立てる。  
- [ ] 2. その後に phase-11 本命（下降法）を段階置換する。

この方針なら、短期で前進しつつ、最終的に“仮定なし NonLiftable”へ到達できます。  

## 状況

### D.1. ルート1. 下降法で `NonLiftableS0` を実証する

ファイル内の用語で言えば、欲しいのはこれ：

\[
\text{PrimitiveOnS0}(c,b,q)\ \Rightarrow\ \neg(q^2 \mid S0_nat(c,b))
\]

これを “最小反例” 仮定のもとで示し、もし \(q^2\mid S0\) なら **より小さい反例** を構成して矛盾、が王道じゃ。

Lean 的には、だいたいこういう形の核が要る：

```lean
-- 最小の反例 (a,b,c) を仮定し、
-- q^2 | S0 から、より小さい (a',b',c') を構成して矛盾
theorem nonLiftableS0_of_minCounterexample
  {a b c q : ℕ} :
  -- (1) a^3 + b^3 = c^3, gcd 条件, 最小性
  -- (2) PrimitiveOnS0 c b q
  -- (3) q^2 ∣ S0_nat c b
  False := by
  ...
```

この “下降ステップの構成” には、結局 **アイゼンシュタイン整数 \(\mathbb{Z}[\omega]\)**（あるいは同等の因数分解構造）が効く。
ぬしの `GEisensteinBridge` 構想は、まさにここに刺さる。

---

## 資料

[議事録](../../discussion-infinite-descent.md)

## 作業ログ

### 2026-02-26 phase-12 方針固め

現状は `TriominoFLT.lean` に `sorry` が残っているので、まず 1→2→3 の順で埋めるのが必要です。

### 2026-02-26 phase-12 開始（Triomino 接続入口を Main に追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/FLT/Main.lean`
- 追加内容:
  1. `FLT_d3_by_padicValNat_of_triominoHasNoSqFamily_coprimeSupport_direct`
  2. `FLT_d3_by_padicValNat_of_triominoHasNonLiftableFamily_coprimeSupport_direct`
- 意図:
  - `TriominoFLT` 側で `hasNoSq` / `hasNonLiftable` family 補題が完成したら、
    既存数論APIへ即時接続できる専用入口を先に固定。
  - phase-12 の実体補題（トロミノ側 `sorry` 解消）作業を Main 側の変更なしで進められるようにした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.FLT.Main DkMath.FLT.GEisensteinBridge`
  - 結果: 成功（`GEisensteinBridge` に `intro` 形の提案 warning 1件のみ）。

### 2026-02-26 phase-12 継続（Triomino 最初の `sorry` 着手と分解方針確定）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
- 実施内容:
  1. `color3_L_tromino_standard` の直接証明を試行し、
     「相異性証明」「mod 3 シフト計算」「3要素 Finset の色カウント」の3ブロック分解が必要であることを確認。
  2. いったんビルド安定性を優先し、本補題は `sorry` のまま維持（コメントを phase-12 方針に更新）。
- 次の実装方針:
  1. 相異性補題（`v`, `v+e0`, `v+e1` が pairwise distinct）を独立補題化
  2. `color3` の `+e0/+e1` での剰余シフト補題を独立補題化
  3. 上記2系統を合流して `color3_L_tromino_standard` を再度実装
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT DkMath.FLT.Main`
  - 結果: 成功（`TriominoFLT` の既存 `sorry` warning は継続）。

### 2026-02-26 phase-12 継続（`color3_L_tromino_standard` 前段 helper 実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
- 追加内容:
  1. `axis0` / `axis1`
  2. `basis0` / `basis1`
  3. `axis0_ne_axis1`
  4. `cell_ne_add_basis0`, `cell_ne_add_basis1`, `add_basis0_ne_add_basis1`
  5. `diff_add_basis0`, `diff_add_basis1`
  6. `color3_val_add_basis0`, `color3_val_add_basis1`
- 意図:
  - `color3_L_tromino_standard` を直接一気に証明せず、
    相異性と mod-3 シフトを独立補題として先に固定。
  - 次段で 3点 Finset の色カウント本体へ合流する。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（`TriominoFLT` の既存 `sorry` warning は継続）。

### 2026-02-26 phase-12 継続（`color3` シフト補題を Fin 3 等式へ昇格）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `color3_add_basis0`（`color3 (v + basis0 hd) = color3 v + 1`）
  2. `color3_add_basis1`（`color3 (v + basis1 hd) = color3 v + 2`）
- 試行内容:
  1. `color3_L_tromino_standard` を `basis0/basis1` ベースで実装し、
     `filter` の card 証明まで接続を試行。
  2. ただし `filter` membership の同値を `simp` だけで閉じる段階で未解決が残るため、
     本体は一旦 `sorry` に戻してビルド健全性を維持。
- 次段の実装ポイント:
  1. `t = {v, v+basis0, v+basis1}` 上の membership 同値
     `((c ∈ t) ∧ color3 c = k) ↔ ...` を色ごとに補題化
  2. その補題を `color3_L_tromino_standard` へ適用して `sorry` 解消
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（`color3_L_tromino_standard` ほか既存 `sorry` warning は継続）。

### 2026-02-26 phase-12 継続（`color3_L_tromino_standard` の `sorry` 解消）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `mem_three_color0_iff`
  2. `mem_three_color1_iff`
  3. `mem_three_color2_iff`
- 実装内容:
  1. `color3_L_tromino_standard` を `basis0/basis1` で定式化し、
     `color3_add_basis0/1` による 3 色の巡回をケース分解で確定。
  2. `filter` の membership 同値を上記 3 補題へ切り出し、
     `filter = singleton` を `ext` で示して各 card=1 を証明。
- 結果:
  - `color3_L_tromino_standard` の `sorry` を除去。
  - 残る `sorry` は `color_balance_of_box_3k` と FLT 骨格定理群。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（既存 linter warning は継続）。

### 2026-02-26 phase-12 継続（`Box` 色平衡向け 1次元 mod3 カウント補題）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `count_mod3_eq_div_of_dvd`
  2. `card_filter_range_mod3_eq_div_of_dvd`
  3. `card_filter_range_mod3_eq_of_dvd`
- 意図:
  - `color_balance_of_box_3k` の本体で必要になる
    「`3 ∣ m` なら `range m` の各剰余類（mod 3）個数が一致」を先に固定。
  - `Nat.count_modEq_card` を使って `m / 3` へ正規化する形に統一。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る `sorry` は `color_balance_of_box_3k` と FLT 骨格定理群）。

### 2026-02-26 phase-12 継続（`color_balance_of_box_3k` の目標を `pi` 側へ正規化）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `card_filter_Box_eq_card_filter_pi`
- 変更内容:
  1. `color_balance_of_box_3k` を
     `Box` 上の色カウントから `s = Finset.pi ...` 上の色カウントへ帰着する形に更新。
  2. `hs`（`s` 上の本体カウント等式）1点へ `sorry` を集約。
- 意図:
  - `Cell` 側の map/embedding 展開を毎回追わず、
    次段の証明を純粋に `pi` 上の座標カウント問題として進めるため。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（`color_balance_of_box_3k` の中核 `hs` が未解決）。

### 2026-02-26 phase-12 継続（`card_filter_color3_eq_piCoord` の型向き修正）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `card_filter_color3_eq_piCoord` の `hPred` で、
     `simpa` 依存だった双方向変換を `calc` で明示化。
  2. `color3_val_of_pi` を向き付きで使い、
     `color3 = k` と `toNat = k.val` の橋を安定化。
  3. `color3_add_basis1` 内の `ring` を `ring_nf` へ置換（linter 提案反映）。
- 結果:
  - `line 524/527` で発生していた型不一致エラーを解消。
  - `color_balance_of_box_3k` の未解決は `hs_mod` 本体のみに集約。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 実装準備：`Pi.cons` 座標補題）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `piCoordOn`
  2. `piCoordOn_cons_same`
  3. `piCoordOn_cons_ne`
  4. `axis1_mem_univ_erase_axis0`
  5. `axis0_mem_univ_erase_axis1`
- 変更内容:
  1. `piCoord` を `piCoordOn` の特殊化として再定義（意味は同一）。
- 意図:
  - `Finset.pi` 分解 (`pi_insert`) 後に `Pi.cons` で構成した関数の軸座標を
    直接展開できる形を用意し、`hs_mod` の case 実装を進めやすくした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 実装準備：fiber disjoint 補題）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `disjoint_image_piCons_of_ne`
  2. `pairwiseDisjoint_image_piCons`
- 意図:
  - `Finset.pi` を軸座標ごとの fibers に分解したとき、
    `card_biUnion` を適用するための pairwise disjoint 条件を先に固定。
  - `hs_mod` 本体で `range (n axis)` 上の `biUnion` カウントへ進む基礎を準備。
- 補足:
  - `pi_insert` の `univ` 直接版は dependent index の型同型（`insert ... = univ`）で
    証明項が重くなるため、今回は導入を見送り、先に disjoint 側を確定した。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 実装準備：`Pi.cons` 後の差分 mod3 展開）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `diffMod3_toNat_piCons_axis0`
  2. `diffMod3_toNat_piCons_axis1`
- 意図:
  - `pi_insert` 分解後の fiber 内で、
    `((x0 - x1) % 3).toNat` を `b` と残り座標の式へ直接落とせるようにした。
  - `hs_mod` で必要な「固定 tail に対する 1次元 range カウント」へ接続しやすくした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 実装準備：fiber filter card 正規化）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `card_filter_image_piCons_axis0`
  2. `card_filter_image_piCons_axis1`
- 変更内容:
  1. `Pi.cons_injective` が必要とする非包含条件を補題仮定として明示
     (`axis0 ∉ s` / `axis1 ∉ s`)。
  2. `filter_map` + `card_map` で image 側 filter card を tail 側 filter card へ正規化。
  3. 末尾の述語同値は `piCoordOn_cons_ne` で座標値を書き換える形に整理。
- 意図:
  - `hs_mod` 本体で `Finset.pi` を軸固定 fibers に分解した後、
    各 fiber のカウントを 1次元 mod3 カウントへ直接落とせるようにする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 実装準備：`univ.erase axis` 専用ラッパ）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `card_filter_image_piCons_axis0_univErase`
  2. `card_filter_image_piCons_axis1_univErase`
- 意図:
  - `hs_mod` の本体で毎回必要になる
    `ha : axis ∉ s` / `haxis : otherAxis ∈ s` の証明を内部化し、
    `s = univ.erase axis` 固定の用途で直接使えるようにした。
  - 本体の `simpa` 量を減らして、`axis0/axis1` 分岐実装を短くする。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` のみ）。

### 2026-02-26 phase-12 継続（`pi` 型運搬の橋補題）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `piFunEquiv`
  2. `map_pi_eq_pi_of_eq`
  3. `card_filter_pi_univ_eq_insertErase_axis0`
  4. `card_filter_pi_univ_eq_insertErase_axis1`
- 意図:
  - `hs_mod` 実装で必要な
    `pi(univ)` と `pi(insert axis (erase axis))` 間の依存関数型ギャップを埋める。
  - まず card/filter レベルで `univ` 側を `insert/erase` 側へ運搬可能にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` と軽微 linter 提案のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 内部を `insert/erase` へ運搬）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `hs_mod` の `sorry` 直前で、`hIns0/hIns1` を導入。
  2. residue `0/1/2` それぞれについて、
     `s = pi(univ)` 側の filter card を
     `pi(insert axis (erase axis))` 側へ運搬する等式群
     (`hAxis*_toInsert0`, `hAxis*_toInsert1`) を実装。
  3. TODO コメントを更新し、次段で使う補題を明示:
     `card_filter_image_piCons_axis*_univErase`,
     `card_filter_range_mod3_eq_of_dvd`。
- 意図:
  - `hs_mod` 本体の未解決部分を「実際のカウント処理」だけに縮約。
  - 依存型の型差（`univ` vs `insert/erase`）は前処理で解消済み。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` と linter 提案のみ）。

### 2026-02-26 phase-12 継続（mod3 条件変換補題の追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `sub_toNat_eq_iff_mod`
  2. `card_filter_range_sub_mod3_toNat_eq_of_dvd`
- 意図:
  - `hs_mod` で扱っている
    `((((b:ℤ) - (c:ℤ)) % 3).toNat) = k` を
    `Nat` 側の mod 条件へ直接落とせるようにした。
  - `3 ∣ m` のとき、上記条件で絞った `range m` の card が
    `k ∈ {0,1,2}` で不変であることを、既存の
    `card_filter_range_mod3_eq_of_dvd` へ接続可能にした。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` と linter 提案のみ）。

### 2026-02-26 phase-12 継続（`hs_mod` 向け補助補題を先行追加）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 追加内容:
  1. `card_biUnion_filter_eq_sum_card_filter_indexed`
  2. `sum_card_filter_swap`
  3. `sum_card_filter_sub_mod3_toNat_eq_of_dvd`
  4. `sub_rev_toNat_eq_iff_mod`
  5. `card_filter_range_sub_rev_mod3_toNat_eq_of_dvd`
  6. `sum_card_filter_sub_rev_mod3_toNat_eq_of_dvd`
- 意図:
  - `hs_mod` の本体で必要になる
    「biUnion の card 分解」「二重和の交換」「(b-c)/(c-b) mod3 の residue 非依存」
    を独立補題として先に確定。
- 実装メモ:
  - `hs_mod` への一括統合（`by_cases h3` 本体化）は、
    依存型の `DecidableEq`/`simp` 展開と heartbeat 超過で不安定だったため、
    本体は一旦 `sorry` のままに戻し、補助補題のみ保持。
  - 次回は `axis0` 分岐だけを小さく切って段階的に再接続する方針。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` と linter 提案）。

### 2026-02-26 phase-12 継続（`hs_mod` の axis0 分岐を復元）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `pi_insert_axis0_univErase` / `pi_insert_axis1_univErase` を `Finset.pi_insert` 経由で安定化
  2. `h3` 分岐のうち `3 ∣ n (axis0)` 側を実装し、`hs_mod` の 2本の等式を導出
  3. `3 ∣ n (axis1)` 側は `sorry` のまま残置（次段で実装）
- 意図:
  - 先行追加した補助補題（`card_filter_pi_insert_axis0_eq_sum`、`card_filter_image_piCons_axis0_univErase`、
    `sum_card_filter_sub_mod3_toNat_eq_of_dvd`）が実際に `hs_mod` 本体で使えることを確認。
  - 一括実装ではなく、`axis0` / `axis1` を段階分割する方針で進める。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は `sorry` と linter 提案）。

### 2026-02-26 phase-12 継続（`hs_mod` の axis1 分岐も実装）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `h3` の `3 ∣ n (axis1)` 側を `u1/predIns1` で実装
  2. `card_filter_pi_insert_axis1_eq_sum`
     `card_filter_image_piCons_axis1_univErase`
     `sum_card_filter_sub_rev_mod3_toNat_eq_of_dvd`
     を接続して `hs_mod` の 2本の等式を閉じた
- 結果:
  - `color_balance_of_box_3k` 内の `hs_mod` は `sorry` なしで成立
  - `TriominoFLT.lean` の残 `sorry` は最終 FLT スケルトン部のみ
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は linter 提案 + FLT スケルトンの `sorry` のみ）。

### 2026-02-26 phase-12 継続（`FLT_case_3_via_tromino` を Mathlib で閉じる）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `Mathlib.NumberTheory.FLT.Three` を import
  2. `FLT_case_3_via_tromino` を `fermatLastTheoremThree` で実装（`sorry` 2件削除）
- 結果:
  - `TriominoFLT.lean` の残 `sorry` は 2件（`FLT_from_tromino_tiling` と `FLT_general_via_tromino`）
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る warning は linter 提案 + `sorry` 2件）。

### 2026-02-26 phase-12 継続（`n=3` 分岐を先行確定）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 変更内容:
  1. `FLT_from_tromino_tiling` に `n = 3 ∨ 4 ≤ n` の分岐を追加
  2. `n = 3` 側は `fermatLastTheoremThree` で即閉じ
  3. 未実装 `sorry` を `n ≥ 4` 側に限定
  4. `FLT_general_via_tromino` も同様に `n=3` 側は `FLT_case_3_via_tromino` で閉じる形に整理
- 意図:
  - フェーズ12の未実装領域を「高指数 (`n ≥ 4`) 専用」に切り分け、次段実装の境界を明確化。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功（残る `sorry` は高指数側 2件のみ）。

### 2026-02-26 phase-12 方針明記（`fermatLastTheoremThree` 依存は暫定）

- 変更ファイル:
  - `lean/dk_math/DkMath/CosmicFormula/TriominoFLT.lean`
  - `lean/dk_math/DkMath/FLT/docs/NoSqOnS0/WorkNotes/NoSqOnS0-WorkNotes.md`
- 方針（明文化）:
  1. `Mathlib.NumberTheory.FLT.Three` の利用は、phase-12 の `sorry` 削減を優先するための暫定ブリッジ。
  2. 研究目標は Triomino/Cosmic 側の独立証明であり、将来これが完成した時点で当該依存を除去する。
  3. 置換対象は `FLT_from_tromino_tiling` の `n=3` 分岐と `FLT_case_3_via_tromino`。
- 追記内容:
  - 上記方針を `TriominoFLT.lean` 内に `NOTE [Temporary Mathlib FLT3 bridge]` として明記。
- ビルド確認:
  - 実行: `cd lean/dk_math && lake build DkMath.CosmicFormula.TriominoFLT`
  - 結果: 成功。
