# KUS Alias Policy (phase-10)

この文書は、`Scale` 周辺で導入した alias の運用範囲を固定する。

## 結論

- phase-10 時点では **alias は利用例層（`Examples.lean`）でのみ推奨** とする。
- コア理論層（`Scale.lean` 内の主要定理）は既存名を正準とし、互換性を優先する。

## 理由

1. 既存名はすでに docs と履歴で安定参照されている。
2. alias をコア層へ強制適用すると、将来の検索性・差分追跡で混乱が増える。
3. phase-08 で確認した通り、関数 alias は環境差分の推論問題を起こしやすい。

## 運用ルール

- 既存名（例: `ScaleSpec.scaleKUS_toKUS`）は残す。
- alias（例: `scale_toKUS`）は追加・利用してよいが、置換を強制しない。
- 新規補題を増やすときは、まず正準名で追加し、必要な場合のみ alias を足す。

## 現在の alias 対象

- `scale_toKUS`
- `extract_scale_toKUS`
- `toNat_scale_toKUS_add`

## 次作業候補

1. alias 命名規則（接頭辞/語順）の簡易ガイドを 1 段落で追加
2. subtype fiber 試作を別枝 docs で比較（本流への反映は保留）
