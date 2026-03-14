# KUS Work Notes

status: 作業中 - phase-14: 係数型の一般化（GKUS / Nat→Int→Rat）

## 課題

- [x] KUS の最小依存型 `US`, `KUS` を Lean で定義する
- [x] `Nat -> KUS` 埋め込みと `KUS -> Nat` forget を導入する
- [x] `extract : KUS -> US` を通常除法と分離して導入する
- [x] 最小 round-trip 定理を追加する
- [x] 固定 fiber 上の可換モノイド的構造を設計する
- [x] `Scale` と unit transport の仕様を定める
- [x] toy blueprint による最小使用例を追加する
- [x] `Scale` と `Monoid` の整合補題を最小追加する
- [x] fiber 型設計（Nat alias / subtype）比較を文書化する
- [x] phase-05 補題の利用例を `Examples.lean` に追加する
- [x] `Scale` API の非破壊命名整理を行う
- [x] alias 補題の `Examples` 反映範囲を判断する
- [x] alias 標準適用範囲を文書として固定する
- [x] alias 命名規則ガイドを `KUS-AliasPolicy.md` に追加する
- [x] 同一 support 上の KUS 加算（`kusAdd`）を定義する
- [x] 零追跡性補題を実装する（係数が零になっても support を保持）
- [x] 同一 support 上の KUS 乗法（`kusMul`）を定義する
- [x] 乗法の零追跡性補題を実装する（係数が零になっても support を保持）
- [x] `lake test` 環境を `DkMathTest` として整備する
- [x] KUS 回帰テスト（`DkMathTest/KUS.lean`）を追加する
- [ ] 係数型を一般化した `GKUS C U Blueprint` を設計・実装する
- [ ] `Nat` 係数をデフォルトとして既存 `KUS` との互換性を保つ
- [ ] `Int` 係数上での加算・乗法を最小実装する

## 状況タスク

- 完了条件（phase-13）
  - [x] `DkMath/KUS/Unit.lean` が `US` を提供する
  - [x] `DkMath/KUS/Core.lean` が `KUS`, `mkWith`, `zeroState` を提供する
  - [x] `DkMath/KUS/NatEmbed.lean` が `ofNat`, `toNat` を提供する
  - [x] `DkMath/KUS/Extract.lean` が `extract` を提供する
  - [x] `DkMath/KUS/RoundTrip.lean` が最小往復定理を提供する
  - [x] 固定 fiber の演算 API が確定する
  - [x] `DkMath/KUS/Scale.lean` が `ScaleSpec` と最小 transport API を提供する
  - [x] `DkMath/KUS/Examples.lean` が toy 使用例を提供する
  - [x] `Scale` と fixed fiber の整合補題が `Scale.lean` にある
  - [x] `DkMath/KUS/docs/KUS-FiberDesign.md` に採用方針と移行トリガーがある
  - [x] `DkMath/KUS/Examples.lean` に phase-05 補題の利用例がある
  - [x] `DkMath/KUS/Scale.lean` に alias API が追加されている
  - [x] `DkMath/KUS/Examples.lean` が alias 補題を利用している
  - [x] `DkMath/KUS/docs/KUS-AliasPolicy.md` に運用方針がある
  - [x] `DkMath/KUS/docs/KUS-AliasPolicy.md` に命名規則ガイドがある
  - [x] `DkMath/KUS/Add.lean` が `SameSupport` と `kusAdd` を提供する
  - [x] 零追跡性（`zero_tracking`）が補題として固定されている
  - [x] 単位元・交換則・結合則（toNat レベル）が補題として固定されている
  - [x] `DkMath/KUS/Mul.lean` が `kusMul` と `oneState` を提供する
  - [x] 乗法の零追跡性（`kusMul.zero_tracking`）が補題として固定されている
  - [x] `lakefile.toml` に `testDriver = "DkMathTest"` を追加した
  - [x] `DkMathTest/KUS.lean` に kusAdd / kusMul の回帰テストがある
  - [ ] `DkMath/KUS/docs/KUS-CoeffDesign.md` に係数拡張の設計がある
  - [ ] `DkMath/KUS/Coeff.lean` が `GKUS` を提供する
  - [ ] `Int` 係数の最小テストが `DkMathTest/KUS.lean` にある

## 計画

- 直近の主戦場:
  - phase-14: 係数型一般化（`GKUS C U Blueprint`）
- 直近の設計候補:
  - `GKUS` は `C : Type*` でパラメータ化し、`CommSemiring C` を要求する
  - 既存 `KUS` は `GKUS Nat` の型エイリアスとして互換性を保つ
  - 減法は `C = Int` 以上のときのみ意味を持つ（`Ab` 群制約で導入）
  - 乗法は CommSemiring の範囲で自然に使える
  - alias 適用は `Examples` を境界とし、コア理論は従来名を維持する
  - subtype 版の試作は本流へ入れず docs 先行で設計比較する
  - 例示モジュールを肥大化させず、証明用の最小例に限定する
- 非目標（phase-01 ではやらない）:
  - `Div` の導入
  - `K : ℚ`, `ℝ`, 一般 carrier への拡張
  - `Scale` の実装

## 実装メモ

- `US` を先に独立させたことで、README の `(U, S_U)` を `extract` の戻り値として明示できる形になった。
- `KUS` は `coeff : Nat` と support の従属対であり、零状態は「係数が 0 になった support 保持状態」として `zeroState` に切り出した。
- `ofNat (extract x) (toNat x) = x` を最小の再構成定理として置き、観測側と構造保持側の分離を Lean 上で固定した。
- phase-02 では `Fiber support := {x : KUS // extract x = support}` を導入し、固定 support 上で `Nat` 係数と同型な `AddCommMonoid` を与えた。
- phase-03 では `ScaleSpec` により、`US` / `KUS` へ unit transport を与える最小 API を追加し、係数保存と extract 整合を補題で固定した。
- phase-04 では `Examples.lean` を追加し、toy blueprint 上で `KUS` / `Fiber` / `ScaleSpec` の最小利用例を固定した。
- phase-05 では `Scale.lean` に fixed fiber 整合補題を追加し、`Scale` と `Monoid` の接続を観測係数レベルで固定した。
- phase-06 では `KUS-FiberDesign.md` を追加し、`Fiber := Nat` 継続採用と subtype 版への移行トリガーを明文化した。
- phase-07 では `Examples.lean` に phase-05 補題の利用例を追加し、定義済み整合補題の実用性を確認した。
- phase-08 では `Scale.lean` に非破壊 alias API を追加し、長い修飾名なしでも同じ理論を参照できるようにした。
- phase-09 では alias API を `Examples.lean` へ適用し、可読性改善が実利用で有効かを確認した。
- phase-10 では alias 運用範囲を docs へ固定し、適用境界を `Examples` 層までと明文化した。
- phase-11 では alias 命名規則ガイドを `KUS-AliasPolicy.md` に追記し、将来追加時の揺れを防ぐ基準を確立した。
- phase-12 では `Add.lean` を追加し、同一 support 上の KUS 加算（`kusAdd`）を実装した。零追跡性・単位元・交換則・結合則を最小形で固定した。
- phase-13 では `Mul.lean` を追加し、同一 support 上の KUS 乗法（`kusMul`）を実装した。零追跡性・単位元・交換則・結合則を最小形で固定した。

### 2026-03-14 phase-13 KUS 乗法の実装

- 対象:
  - `lean/dk_math/DkMath/KUS/Mul.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `kusMul` を定義し、可視係数の Nat 乗法と support 保持を一体化した
  2. `oneState` を導入し、左右単位元（`one_mul`, `mul_one`）を固定した
  3. 零追跡性（`kusMul.zero_tracking`）を固定した
  4. 交換則・結合則を `toNat` レベルで固定した
  5. 零閉補題（`zeroState_kusMul_zeroState`）を追加した
- 次の予定:
  - phase-14 で係数拡張（Nat→Int/Rat）の設計を docs 先行で固める

### 2026-03-14 phase-13 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. `omega` 依存を除去し、`Nat.mul_comm`/`Nat.mul_assoc` による安定証明へ整理した
- 次の予定:
  - phase-14 で係数拡張の前提を整理する

## 作業ログ

### 2026-03-14 phase-01 最小核の実装

- 対象:
  - `lean/dk_math/DkMath/KUS.lean`
  - `lean/dk_math/DkMath/KUS/Unit.lean`
  - `lean/dk_math/DkMath/KUS/Blueprint.lean`
  - `lean/dk_math/DkMath/KUS/Core.lean`
  - `lean/dk_math/DkMath/KUS/NatEmbed.lean`
  - `lean/dk_math/DkMath/KUS/Extract.lean`
  - `lean/dk_math/DkMath/KUS/RoundTrip.lean`
- 内容:
  1. README の世界観のうち、`Nat` 係数・support 保持・extract 分離に絞って最小 Lean 核を追加した
  2. `US` を構造保持側、`KUS` を観測係数付き状態として分け、`zeroState`, `ofNat`, `toNat`, `extract` を整えた
  3. round-trip は `Nat -> KUS -> Nat` と `KUS -> extract -> ofNat` の両側で最小形を追加した
- 次の予定:
  - 固定 fiber 上の演算型を `Monoid.lean` として切り出す
  - `README` の planned modules と実装済みモジュールの差分を別ドキュメントで埋める

### 2026-03-14 phase-01 ビルド確認

- 対象:
  - `cd lean/dk_math && lake build DkMath.KUS`
  - `cd lean/dk_math && lake build DkMath`
- 内容:
  1. `DkMath.KUS` はビルド通過を確認した
  2. root の `DkMath` に import を追加した状態でも全体ビルドで破綻しないことを確認した
  3. 既存 repo 由来の `sorry` warning は残るが、今回追加した KUS 群はエラーなしで接続できた
- 次の予定:
  - fixed support 上の加法構造を `Monoid.lean` として導入する
  - linter の軽微な style warning を、次回の小修正タイミングでまとめて掃除する

### 2026-03-14 phase-02 固定 fiber 加法モノイド

- 対象:
  - `lean/dk_math/DkMath/KUS/Monoid.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `Fiber support := Nat` として fixed support の係数層を最小実装した
  2. `Fiber.toKUS` / `Fiber.toNat` を導入し、固定 fiber と KUS 本体の接続 API を整えた
  3. `Fiber` 上に `Zero`, `Add`, `AddCommMonoid` instance を追加し、加法構造を固定 support 上で確立した
  4. 入口 `DkMath/KUS.lean` で `Monoid.lean` を import して公開 API へ接続した
- 次の予定:
  - `Scale.lean` の仕様を docs で先に固定する
  - `Examples.lean` で固定 fiber 演算の toy 例を最小追加する

### 2026-03-14 phase-02 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認した
  2. root の `DkMath` でも build succeeded を確認し、KUS phase-02 の接続が全体で有効であることを確認した
  3. 全体ビルドで出る warning は既存 repo 由来の `sorry` 群が中心で、今回追加分に新規エラーはない
- 次の予定:
  - `Scale` 仕様の文書化を先行し、phase-03 の実装境界を固定する

### 2026-03-14 phase-03 Scale transport 仕様と実装

- 対象:
  - `lean/dk_math/DkMath/KUS/Scale.lean`
  - `lean/dk_math/DkMath/KUS.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `ScaleSpec` を導入し、`mapUnit` と依存型 `mapBlueprint` を同時に持つ最小仕様を追加した
  2. `scaleUS` / `scaleKUS` を追加し、`toNat` 保存と `extract` 整合を補題で固定した
  3. `idScale` と `comp` を追加し、transport の単位元・合成の最小法則を追加した
  4. 入口 `DkMath/KUS.lean` で `Scale.lean` を import して公開 API へ接続した
- 次の予定:
  - `Examples.lean` で toy blueprint を導入し、`Scale` と `Monoid` の最小使用例を追加する

### 2026-03-14 phase-03 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. `Scale.lean` の軽微な lint 警告（`simpa`/未使用変数/whitespace）は修正済み
- 次の予定:
  - phase-04 として `Examples.lean` を追加し、toy blueprint 上の `Monoid` / `Scale` 使用例を固定する

### 2026-03-14 phase-04 Examples 追加

- 対象:
  - `lean/dk_math/DkMath/KUS/Examples.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `ToyUnit := Nat`, `ToyBlueprint u := Fin (u+1)` を定義し、依存型 blueprint の最小具体例を導入した
  2. 固定 support `toySupport`、KUS 値 `toyX`、fiber 加法 `toyFiberSum` を追加した
  3. `toyScale` を追加し、`toNat` 保存と `extract` 整合を具体例で確認した
  4. 入口 `DkMath/KUS.lean` へ `Examples.lean` import を追加した
- 次の予定:
  - `Scale` と `Monoid` の整合補題を最小追加する（phase-05）

### 2026-03-14 phase-04 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. `Examples.lean` の軽微な whitespace 警告を修正し、KUS 側の追加分は warning なしで通過
- 次の予定:
  - phase-05 で `Scale` と `Monoid` の整合補題を最小追加する

### 2026-03-14 phase-05 Scale×Monoid 整合補題

- 対象:
  - `lean/dk_math/DkMath/KUS/Scale.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `scaleKUS_toKUS` を追加し、scale と fixed fiber 埋め込みの整合を固定した
  2. `extract_scaleKUS_toKUS` を追加し、transport 後 support の抽出整合を固定した
  3. `toNat_scaleKUS_toKUS_add` を追加し、観測係数レベルで加法整合を固定した
- 次の予定:
  - phase-06 として、transport 後 fiber 型（Nat 別名 vs subtype）の設計比較を文書化する

### 2026-03-14 phase-05 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. KUS 追加分の warning は解消し、全体 warning は既存 repo 由来の `sorry` 群のみ
- 次の予定:
  - phase-06 で fiber 型設計比較（Nat alias / subtype）を docs へ明示する

### 2026-03-14 phase-06 fiber 型設計比較（docs）

- 対象:
  - `lean/dk_math/DkMath/KUS/docs/KUS-FiberDesign.md`
  - `lean/dk_math/DkMath/KUS/docs/KUS-WorkNotes.md`
- 内容:
  1. `Fiber := Nat` と subtype fiber を比較し、長所・短所を整理した
  2. phase-06 の結論として `Fiber := Nat` 継続採用を明文化した
  3. subtype 版へ移行すべき条件（移行トリガー）を定義した
- 次の予定:
  - phase-07 で phase-05 補題の使用例を `Examples.lean` に追加する

### 2026-03-14 phase-06 確認ビルド（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
- 内容:
  1. docs-only 更新後も `DkMath.KUS` の build succeeded を確認
  2. 実装ファイルの挙動を変えていないことを再確認
- 次の予定:
  - phase-07 の `Examples.lean` 強化へ進む

### 2026-03-14 phase-07 補題利用例の追加

- 対象:
  - `lean/dk_math/DkMath/KUS/Examples.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `toyScale_toKUS_comm` を追加し、`scaleKUS_toKUS` の具体利用を固定
  2. `toyScale_extract_toKUS_comm` を追加し、`extract_scaleKUS_toKUS` の具体利用を固定
  3. `toyScale_toNat_add_comm` を追加し、`toNat_scaleKUS_toKUS_add` の具体利用を固定
  4. `KUS-ScaleSpec.md` に phase-07 の利用例を追記
- 次の予定:
  - phase-08 で補題命名と API の最小整理を検討する

### 2026-03-14 phase-07 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. 途中で `simpa using` が構文エラーになったため、`Examples.lean` は `exact` 形式へ修正して安定化した
- 次の予定:
  - phase-08 で補題命名と API の最小整理を実施する

### 2026-03-14 phase-08 非破壊命名整理

- 対象:
  - `lean/dk_math/DkMath/KUS/Scale.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `ScaleSpec.*` を壊さず、整合補題の短縮別名を追加した（`scale_toKUS` など）
  2. 環境差分で暗黙推論が厳しいため、関数 alias は見送り、補題 alias のみに絞った
  3. 既存利用を壊さない方針で、API の見通しのみ改善した
- 次の予定:
  - phase-09 で alias 適用範囲（Examples まで寄せるか）を判断する

### 2026-03-14 phase-08 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
  - `cd lean/dk_math && ./lean-build.sh DkMath`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. root `DkMath` でも build succeeded を確認
  3. phase-08 途中で alias 実装の推論問題が出たため、補題 alias のみに絞って安定化した
- 次の予定:
  - phase-09 で alias 適用範囲を判断し、必要なら Examples 側の呼び出しを整理する

### 2026-03-14 phase-09 alias 適用判断

- 対象:
  - `lean/dk_math/DkMath/KUS/Examples.lean`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
- 内容:
  1. `Examples.lean` の phase-05 補題呼び出しを alias 名へ置換した
  2. 置換対象は 3 箇所に限定し、理論本体の命名は維持した
  3. alias 適用は「利用例層でのみ採用」が妥当という結論にした
- 次の予定:
  - phase-10 で alias 適用の拡張有無を判断する

### 2026-03-14 phase-10 alias ポリシー固定（docs）

- 対象:
  - `lean/dk_math/DkMath/KUS/docs/KUS-AliasPolicy.md`
  - `lean/dk_math/DkMath/KUS/docs/KUS-ScaleSpec.md`
  - `lean/dk_math/DkMath/KUS/docs/KUS-WorkNotes.md`
- 内容:
  1. alias の標準適用範囲を `Examples` 層までに固定した
  2. コア理論では `ScaleSpec.*` 名を正準参照として維持する方針を明文化した
  3. alias 追加時の運用ルール（追加は許可、置換強制なし）を定義した
- 次の予定:
  - phase-11 で alias 命名規則の簡易ガイドを追加する

### 2026-03-14 phase-10 確認ビルド（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
- 内容:
  1. docs 更新後も `DkMath.KUS` は build succeeded を確認
  2. 理論実装を変更せず、運用方針のみ固定できたことを確認
- 次の予定:
  - phase-11 で alias 命名規則の簡易ガイドを追加する

### 2026-03-14 phase-11 alias 命名規則ガイドの追加

- 対象:
  - `lean/dk_math/DkMath/KUS/docs/KUS-AliasPolicy.md`
- 内容:
  1. 命名規則 5 条（prefix 除去・語順・サフィックス・短縮範囲・1 対 1 対応）を追記
  2. 正準名 vs alias の対応表を記載
  3. ユーザーによる `#print "file: ..."` 追加を確認し、ビルドへの影響なしを確認

### 2026-03-14 phase-11 確認ビルド（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認
  2. docs のみ変更で理論挙動は無変更であることを確認
- 次の予定:
  - phase-12 で次の実装拡張候補を評価・選択する

### 2026-03-14 phase-12 KUS 加算の実装

- 対象:
  - `lean/dk_math/DkMath/KUS/Add.lean`
  - `lean/dk_math/DkMath/KUS.lean`
- 内容:
  1. `SameSupport` 述語を導入し、同一 support の判定を型で明示した
  2. `kusAdd` を定義し、可視係数加算と support 保持を一体化した
  3. 零追跡性（`zero_tracking`）：係数が 0 になっても `extract` が US を返すことを補題で固定した
  4. 零状態を左右単位元として確認した（`zero_add`, `add_zero`）
  5. `toNat` レベルの交換則・結合則を `omega` で固定した
  6. 零閉補題（`zeroState_kusAdd_zeroState`）を追加した
- 次の予定:
  - phase-13 で減法または乗法の導入を検討する

### 2026-03-14 phase-12 ビルド確認（lean-build.sh）

- 対象:
  - `cd lean/dk_math && ./lean-build.sh DkMath.KUS`
- 内容:
  1. `DkMath.KUS` は build succeeded を確認（warning なし）
  2. `symm`/`trans` の自己再帰は `unfold SameSupport at *` で解消した
  3. `zero_tracking` の `hz` は `_` に変更し、support 保持が無条件であることを明確にした
- 次の予定:
  - phase-13 で減法または乗法の最小実装へ進む

### 2026-03-14 phase-14 GKUS テスト修復（`lake test` 復旧）

- 対象:
  - `lean/dk_math/DkMathTest/KUS.lean`
- 内容:
  1. `DkMathTest.GKUS` 節を全面整理し、重複と構文崩れを除去した
  2. `GSameSupport` 証明を `hN` / `hI` として共通化し、`gOp` / `gAdd` / `gMul` / `gSub` テストで再利用した
  3. `extract_g` と係数一致の回帰テストを最小構成で復元した
  4. `lake build DkMathTest.KUS` でエラー解消を確認した（warning のみ）
  5. `./lean-test.sh` で `build succeeded` を確認した
- 次の予定:
  - phase-15: `GKUS` のコンテキスト拡張（`CommSemiring` 補題・`gDiv`（除算型）設計）
  - `Rat` 係数でのゼロ追跡テスト（分子が 0 のとき support 保持）を検討する

### 2026-03-14 phase-15 gDiv の実装と Rat 除算テスト

- 対象:
  - `lean/dk_math/DkMath/KUS/Coeff.lean`
  - `lean/dk_math/DkMathTest/KUS.lean`
- 内容:
  1. `abbrev gDiv [Div C] ...` を `gSub` 直後に追加し、`gOp (· / ·)` の略記として定義した
  2. `gDiv` namespace に `toCoeff_div`、`extract_div_left`、`zero_tracking` を追加した
  3. `DkMathTest/KUS.lean` に `Rat` 除算テスト 3 本を追加した
     - `(1/2) / (1/3)` の係数計算テスト
     - `extract_g` の support 保持テスト
     - `x / 0 = 0`（Rat のゼロ除算）でも support 保持することのテスト
  4. `tl` で `build succeeded` を確認した
- 次の予定:
  - phase-16: `CommSemiring` 補題の整備（`gAdd`/`gMul` の代数法則を `GKUS` レベルで固定）

### 2026-03-14 phase-14 Rat 係数テスト追加

- 対象:
  - `lean/dk_math/DkMathTest/KUS.lean`
- 内容:
  1. `Rat` 係数の `grA` (`1/2`) / `grB` (`1/3`) と共通補題 `hR` を追加した
  2. `gAdd`/`gMul`/`gSub` の係数計算テストと `extract_g` support 保持テストを追加した
  3. `Rat` 乗法の優先順位問題（`*` と `/` 混在）を明示括弧で修正して安定化した
  4. `tl` で `build succeeded` を確認した（error/warning ともなし）
- 次の予定:
  - phase-15 で `gDiv`（除算）設計と `Rat` ゼロ追跡の整理を行う
