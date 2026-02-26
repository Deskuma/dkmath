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
