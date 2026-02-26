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
