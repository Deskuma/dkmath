# No Square on S0 Work Notes

status: 作業中 - phase-06: リファクタリング branch: `dev/flt-refactoring-phase6-260224-v0`

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)

## 課題

- [x] なし

## 状況タスク

phase-06（リファクタリング）として、以下の順で進めるのが最短です。

1. [ ] 目標定義の固定

   - `NoSqOnS0-WorkNotes.md` に phase-06 のゴールを明記
   - ゴール: 「`Main` は合成のみ、導出は `PhaseLift/CounterexamplePattern` へ集約」

2. [ ] 仮定インターフェースの圧縮

   - `PhaseLift` に入力構造体（仮称 `Phase6Input`）を追加
   - 現在バラけている仮定群（`hHarm`, `hNoExcAll`, `coprime`, mod3 分離など）を束ねる

3. [ ] 中間補題の移設

   - `Main` に残る局所補題を洗い出し
   - 移設先を `PhaseLift` / `CounterexamplePattern` に振り分けて移動

4. [ ] `Main` の再配線

   - `Main` は「入口定理 + 合成」だけに整理
   - 重複証明を削除し、共通補題参照に統一

5. [ ] 検証と記録

   - `lake build DkMath.FLT.Main`
   - `NoSqOnS0-WorkNotes.md` に phase-06 作業ログ追記
   - 補題チェーン（Mermaid）が必要なら更新

## 作業ログ 2026/02/24  4:52 より
