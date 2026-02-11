# Working MEMO

## 差の冪に関する補題群の整理と「完全冪否定」への道筋

ワークスペース情報を収集していますわっち、全文を読んだぞい（[`DkMath/FLT/DandWiseWolf-FLT-conversation log.md`](lean/dk_math/DkMath/FLT/DandWiseWolf-FLT-conversation log.md) と実装中の `DkMath.Samples.SketchBook.diffPowSum` / `DkMath.Samples.SketchBook.BodyPow_factor` を確認したぞよ🍎。次にやるべき作業を短く計画して示す。どうじゃ？

1. [ ] 目的と優先度（短く）

- [ ] 最優先：差の冪周りを整理して「否定筋（完全冪にならない）」へ繋ぐ土台を作る（まずはコンパイル + 小さな補題）。
  - [x] ~~中期：\(\gcd\) 制御補題 → 部分的な「完全 \(d\) 乗否定」補題を積む。~~
  - [ ] 長期：Zsigmondy 等を形式化して一般定理へ（重工事、段階的に）。

1. [ ] 具体タスク（順序付き）
   1. [ ] モジュール分割：差の冪関連を専用ファイルへ移す（再利用性向上）
      - [x] 新規ファイル: `DkMath/Algebra/DiffPow.lean` に `diffPowSum`・`pow_sub_pow_factor`・`BodyPow`・`BodyPow_factor` を置く（現状の FLT.lean から抽出）。
   2. [ ] 基本補題：交差項が消えない不等式を入れる
      - [x] `BodyPow_pos` / `BodyPow_gt`：$x,u > 0, d\ge2$ なら $(x+u)^d-u^d > x^d$ を形式化して証明する（探索空間削減の剃刀）。
   3. [ ] \(\gcd\) 補題を作る（中核）
      - [x] `gcd (a-b) (diffPowSum a b d)` $\mid d$ ` 型の補題を `DkMath/NumberTheory/GcdDiffPow.lean` に実装。
   4. [ ] 「完全冪否定」ファイルを段階的に作る
      - [ ] `DkMath/NumberTheory/NoPerfectPowerDiffPow.lean`：まずは $d$ が素数かつ $\gcd(a,b)=1$ の場合等、扱いやすいケースから。
      - [ ] Zsigmondy を使う部分は分離して段階的に導入（重い作業）。
   5. [ ] ドキュメント・テスト・ビルド
      - [ ] それぞれの新ファイルに docstring を付け、`README` に追記。
      - [x] `lake build` で逐次確認、テスト（小さな `example` / `#eval`）を追加。

2. [ ] 小さな実装方針メモ（証明戦略）
   - [ ] `diffPowSum` は `∑ i in Finset.range d` の形に寄せる（`sum_range_succ` 系が刺さりやすい）。
   - [ ] `BodyPow_pos` は二項展開で交差項が正であることを直接示すのが素直。
   - [ ] `gcd` 補題は binomial-coef の素因子性や合同式で制御し、最終的には「共通因子は $d$ に由来する」系に落とす。
   - [ ] `NoPerfectPowerDiffPow` はまず簡単なケースを潰して段階的に一般化する（Zsigmondy の正式化は別PRで）。

3. [ ] 変更候補ファイル（新規・修正）
   - 修正元: FLT.lean （差分抽出）
   - [ ] 追加案: lean/dk_math/DkMath/Algebra/DiffPow.lean
   - [ ] 追加案: lean/dk_math/DkMath/NumberTheory/GcdDiffPow.lean
   - [ ] 追加案: lean/dk_math/DkMath/NumberTheory/NoPerfectPowerDiffPow.lean

4. [ ] 開発フロー（短く）
   - [ ] 小さく切って PR を出す（DiffPow → gcd → NoPerfectPower の順）。
   - [ ] 各PRで `lake build` を必ず通す（CI を意識）。
   - [ ] ドキュメント（各ファイル先頭）と README を更新する。

参考（既存実装）

- 差分実装：`DkMath.Samples.SketchBook.diffPowSum` / `DkMath.Samples.SketchBook.BodyPow_factor`
- 討論ノート：[`DkMath/FLT/DandWiseWolf-FLT-conversation log.md`](lean/dk_math/DkMath/FLT/DandWiseWolf-FLT-conversation log.md)

必要なら、わっちが新規ファイルの雛形と最初の補題（`BodyPow_pos` と `gcd` 命題の骨格）を書いて PR 用のパッチを作るぞい。ぬしはどのタスクから始めたいかの？
