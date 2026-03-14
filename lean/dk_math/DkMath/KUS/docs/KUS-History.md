# KUS: Implementation History

## History Log

### 2026-03-14 / Work Unit 1. 内容把握

- KUS の主題は、通常の数体系で単一の `0` に潰れて失われる構造を、`(K, U, S_U)` という依存型構造として保持することだと確認。
- 特に零状態を `(0, U, S_U)` として扱い、観測的零 `toNat = 0` と構造保持零 `extract = (U, S_U)` を分離する設計方針を確認。
- README 上の初期実装対象は、`K : ℕ`、unit 依存 blueprint family、Nat 埋め込み、forget、extract、固定 fiber 上の可換モノイド、round-trip 定理に限定されていることを確認。
- 実装上の重要論点として、`Div` を早期導入せず `extract` を先に設計すること、全空間演算より固定 unit fiber の演算を優先すること、依存型として `S_U ∈ Blueprint(U)` を正面から扱うことを整理。
- repo 全体の流儀として、`Core` を中心に薄い補助モジュールを分け、入口ファイルで import 集約する構成が多いことを確認。KUS の README 案はその方針と整合する。
- 次段候補としては、`Unit.lean` と `Blueprint.lean` で依存型の土台を置き、`Core.lean` で最小 KUS 構造を定義し、続いて `NatEmbed.lean` と `Extract.lean` を設計する流れが自然と判断。

### 2026-03-14 / Work Unit 2. phase-01 最小核の実装

- `DkMath/KUS/Unit.lean` に `(U, S_U)` を束ねる `US` を追加し、KUS の構造保持側を Lean 上で独立させた。
- `DkMath/KUS/Core.lean` に `KUS`、`mkWith`、`zeroState` を追加し、`(0, U, S_U)` を「係数のみ零化した構造保持零」として定義した。
- `DkMath/KUS/NatEmbed.lean` に `ofNat`, `toNat` を追加し、README の `Nat -> KUS -> Nat` の最小往復を実装した。
- `DkMath/KUS/Extract.lean` に `extract` を追加し、通常除法とは別の特異操作として `(U, S_U)` を回収する経路を固定した。
- `DkMath/KUS/RoundTrip.lean` に `extract (ofNat support n) = support` と `ofNat (extract x) (toNat x) = x` を追加し、観測側と構造保持側の round-trip を最小形で整備した。
- 入口 `DkMath/KUS.lean` と root import `DkMath.lean` を追加更新し、KUS をライブラリの公開入口に接続した。
- docs として `KUS-WorkNotes.md` と `KUS-MinimalKernel.md` を追加し、実装済み範囲と次作業候補を Markdown 側でも追跡できるようにした。
- 次作業予定は `KUS-WorkNotes.md` に明記し、固定 fiber 上のモノイド構造と unit transport 仕様を次段候補として残した。

### 2026-03-14 / Work Unit 3. build 接続確認

- `lake build DkMath.KUS` を通し、KUS の入口モジュールとして独立ビルドできることを確認した。
- root 側では `DkMath.lean` に `import DkMath.KUS` を追加し、`lake build DkMath` で全体接続を確認した。
- 既存 repo に由来する `sorry` warning は継続しているが、今回の KUS 追加による新規エラーは解消済みである。
- 次作業は、固定 support 上の演算を `Monoid.lean` として切り出し、README の planned modules を Lean 実装へさらに寄せること。

### 2026-03-14 / Work Unit 4. phase-02 固定 fiber 加法モノイド

- `DkMath/KUS/Monoid.lean` を追加し、phase-02 の最小実装として `Fiber support := Nat` を導入した。
- `Fiber.toKUS` と `Fiber.toNat` を追加し、固定 support fiber と KUS 本体の接続 API を固定した。
- `Fiber` 上に `AddCommMonoid` を与え、phase-01 の「固定 fiber 上の可換モノイド的土台」を最小更新で実装した。
- `DkMath/KUS.lean` を更新し、`import DkMath.KUS.Monoid` で公開入口に接続した。
- 次作業予定は `KUS-WorkNotes.md` へ反映し、`Scale` 仕様と `Examples` の最小化を次段タスクとして残した。

### 2026-03-14 / Work Unit 5. phase-02 build 確認

- 指定されたビルドスクリプト `lean-build.sh` を利用し、`./lean-build.sh DkMath.KUS` を実行して成功を確認した。
- 続けて `./lean-build.sh DkMath` を実行し、root 入口でも成功することを確認した。
- ビルドログ上の warning は既存 repo 由来の `sorry` によるもので、KUS phase-02 追加分に起因する新規エラーはない。
- これにより、phase-02 の成果は「実装・文書・入口接続・ビルド確認」が揃った状態で保存された。

### 2026-03-14 / Work Unit 6. phase-03 Scale transport

- `DkMath/KUS/Scale.lean` を追加し、`ScaleSpec`（`mapUnit` と依存型 `mapBlueprint`）を導入した。
- `scaleUS` / `scaleKUS` を追加し、`toNat` 保存・`extract` 整合・零状態の整合を最小補題として固定した。
- `idScale` / `comp` と、それぞれの `US` / `KUS` への作用補題を追加して、transport の最小代数を整えた。
- 入口 `DkMath/KUS.lean` に `import DkMath.KUS.Scale` を追加し、公開 API へ接続した。
- docs として `KUS-ScaleSpec.md` を追加し、phase-03 の仕様・保証・次作業候補を文書化した。

### 2026-03-14 / Work Unit 7. phase-03 build と軽微警告整理

- `lean-build.sh` を用いて `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- `Scale.lean` の軽微な lint 警告（`simpa` 推奨、未使用変数、whitespace）を修正した。
- これにより phase-03 は「実装・仕様文書・入口接続・ビルド確認」が揃った状態で確定した。

### 2026-03-14 / Work Unit 8. phase-04 Examples 導入

- `DkMath/KUS/Examples.lean` を追加し、toy unit / blueprint を使った最小使用例を実装した。
- `toySupport`, `toyX`, `toyFiberSum`, `toyScale` を導入し、`KUS` / `Fiber` / `Scale` の基本利用を補題で固定した。
- 入口 `DkMath/KUS.lean` を更新し、`import DkMath.KUS.Examples` を追加して公開 API に接続した。
- docs 側では `KUS-WorkNotes.md` と `KUS-MinimalKernel.md` を phase-04 状態へ更新した。
- 次作業予定は `Scale` と `Monoid` の整合補題追加（phase-05）とした。

### 2026-03-14 / Work Unit 9. phase-04 build と警告整理

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- `Examples.lean` の軽微な whitespace 警告を解消した。
- これにより phase-04 は「実装・入口接続・記録・ビルド確認」が揃った状態で確定した。

### 2026-03-14 / Work Unit 10. phase-05 Scale×Monoid 整合

- `DkMath/KUS/Scale.lean` に、`Scale` と fixed fiber (`Fiber.toKUS`) の整合補題を追加した。
- 追加補題は `scaleKUS_toKUS`, `extract_scaleKUS_toKUS`, `toNat_scaleKUS_toKUS_add` の 3 本。
- これにより、scale 後 support への移送と、観測係数レベルでの加法整合が最小形で固定された。
- `KUS-ScaleSpec.md` と `KUS-WorkNotes.md` を phase-05 状態へ更新した。

### 2026-03-14 / Work Unit 11. phase-05 build 確認

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- `Scale.lean` の補題追加後も KUS 側に新規 warning はなく、全体 warning は既存 repo 由来のみ。
- これにより phase-05 は「補題追加・仕様更新・記録・ビルド確認」が揃った状態で確定した。

### 2026-03-14 / Work Unit 12. phase-06 fiber 設計方針の固定

- `KUS-FiberDesign.md` を追加し、`Fiber := Nat` と subtype fiber の比較を文書化した。
- phase-06 の採用方針として、当面は `Fiber := Nat` を継続することを明示した。
- subtype 版へ移行する条件（移行トリガー）を定義し、判断基準を固定した。
- `KUS-WorkNotes.md` に phase-06 の実施内容と次作業予定（phase-07）を追記した。

### 2026-03-14 / Work Unit 13. phase-06 docs 更新後の確認ビルド

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` を実行し、build succeeded を確認した。
- phase-06 は docs 中心の変更であり、実装挙動を変えずに設計判断だけを固定できたことを確認した。

### 2026-03-14 / Work Unit 14. phase-07 補題利用例の固定

- `DkMath/KUS/Examples.lean` に、phase-05 整合補題の具体利用例を 3 本追加した。
- 追加した利用例は `toyScale_toKUS_comm`, `toyScale_extract_toKUS_comm`, `toyScale_toNat_add_comm`。
- `KUS-ScaleSpec.md` と `KUS-WorkNotes.md` を phase-07 状態へ更新した。

### 2026-03-14 / Work Unit 15. phase-07 build 確認と小修正

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- `Examples.lean` の利用例証明で `simpa using` が構文エラーとなる環境差分を確認し、`exact` 形式へ修正して安定化した。
- これにより phase-07 は「利用例追加・docs 更新・ビルド確認」が揃った状態で確定した。

### 2026-03-14 / Work Unit 16. phase-08 API 命名の薄い整理

- `DkMath/KUS/Scale.lean` に、`ScaleSpec.*` の整合補題短縮 alias を追加した。
- 追加内容は `scale_toKUS`, `extract_scale_toKUS`, `toNat_scale_toKUS_add` の 3 本。
- 既存名・既存利用は維持し、移行を強制しない方針で可読性だけを改善した。
- `KUS-ScaleSpec.md` と `KUS-WorkNotes.md` を phase-08 状態へ更新した。

### 2026-03-14 / Work Unit 17. phase-08 build と安定化

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- phase-08 途中で関数 alias の暗黙推論エラーが出たため、補題 alias のみに絞ることで安定化した。
- これにより phase-08 は「命名整理・docs 更新・ビルド確認」が揃った状態で確定した。

### 2026-03-14 / Work Unit 18. phase-09 alias 適用判断

- `DkMath/KUS/Examples.lean` の補題呼び出し 3 箇所を alias 名へ置換した。
- 置換先は `scale_toKUS`, `extract_scale_toKUS`, `toNat_scale_toKUS_add`。
- コア理論側の命名は維持し、利用例層のみ alias を採用する方針を確定した。
- `KUS-ScaleSpec.md` と `KUS-WorkNotes.md` を phase-09 状態へ更新した。

### 2026-03-14 / Work Unit 19. phase-09 build 確認

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` と `./lean-build.sh DkMath` の成功を確認した。
- phase-09 の変更は可読性改善のみで、理論挙動に変更がないことを確認した。

### 2026-03-14 / Work Unit 20. phase-10 alias ポリシー固定

- `KUS-AliasPolicy.md` を追加し、alias の標準適用範囲を `Examples` 層までと固定した。
- `KUS-ScaleSpec.md` に phase-10 方針を追記し、コア理論の正準名維持を明文化した。
- `KUS-WorkNotes.md` を phase-10 状態へ更新し、次作業を phase-11（命名規則ガイド）に設定した。

### 2026-03-14 / Work Unit 21. phase-10 docs 更新後の確認ビルド

- `lean-build.sh` で `./lean-build.sh DkMath.KUS` を実行し、build succeeded を確認した。
- phase-10 は docs 中心の変更であり、実装挙動を変えずに運用ポリシーのみ固定できたことを確認した。
