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

1. [x] 目標定義の固定

   - `NoSqOnS0-WorkNotes.md` に phase-06 のゴールを明記
   - ゴール: 「`Main` は合成のみ、導出は `PhaseLift/CounterexamplePattern` へ集約」

2. [x] 仮定インターフェースの圧縮

   - `PhaseLift` に入力構造体（仮称 `Phase6Input`）を追加
   - 現在バラけている仮定群（`hHarm`, `hNoExcAll`, `coprime`, mod3 分離など）を束ねる

3. [x] 中間補題の移設

   - `Main` に残る局所補題を洗い出し
   - 移設先を `PhaseLift` / `CounterexamplePattern` に振り分けて移動

4. [x] `Main` の再配線

   - `Main` は「入口定理 + 合成」だけに整理
   - 重複証明を削除し、共通補題参照に統一

5. [x] 検証と記録

   - `lake build DkMath.FLT.Main`
   - `NoSqOnS0-WorkNotes.md` に phase-06 作業ログ追記
   - 補題チェーン（Mermaid）が必要なら更新

## 作業ログ 2026/02/24  4:52 より

- phase-06 実装ステップ（仮定インターフェース圧縮: v0）
  - `PhaseLift.lean` に追加:
    - `Phase6NoSqInput (c b : ℕ)`
      - `hbc`, `hcb_coprime`, `hHarm`, `hNoSq`, `hc_nz`, `hb_nz`, `hsep` を束ねる構造体。
    - `phase6_s0PrimeSupportExceptThree`
      - `Phase6NoSqInput` から `S0PrimeSupportExceptThree c b` を復元する補助。
  - 位置づけ:
    - `Main` の入口仮定を段階的に圧縮する phase-06 の初手。

- phase-06 実装ステップ（`Main` 入口定理の追加）
  - `Main.lean` に追加:
    - `FLT_d3_by_padicValNat_of_phase6NoSqInput`
      - `Phase6NoSqInput c b` + `hNoExcAll` を入力に、
        既存 `...of_harmonicEnvelope_NoSq_coprimeSupport` へ接続する薄い合成定理。
  - 位置づけ:
    - `Main` の引数列を減らし、今後のリファクタリング先を固定。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK

- phase-06 実装ステップ（中間補題の移設）
  - `Main.lean` から `PhaseLift.lean` へ移設:
    - `S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb`
    - `padicValNat_lower_bound_of_dvd_d3`
    - `padicValNat_upper_bound_d3`
  - `PhaseLift` 側に追加 import:
    - `DkMath.NumberTheory.GcdNext`
    - `DkMath.ABC.PadicValNat`
  - `Main` 側から上記補題定義ブロックを削除し、
    共通補題参照へ統一。
  - 位置づけ:
    - phase-06 タスク 3（中間補題の移設）を実装として完了。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK

- phase-06 実装ステップ（Main 再配線の追加整理）
  - `Main.lean` から未使用の層Aラッパー補題を削除:
    - `exists_primitive_prime_factor_d3`
  - 同補題は `PhaseLift.lean` 側へ移して共通層に統一。
  - 効果:
    - `Main` には合成・導出本体のみを残し、分岐ラッパーを共通層へ寄せた。

- build（再確認）
  - `lake build DkMath.FLT.Main` : OK
