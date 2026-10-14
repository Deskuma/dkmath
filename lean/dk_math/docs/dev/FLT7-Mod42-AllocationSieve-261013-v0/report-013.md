# report-013 — 実装結果

2026-10-14。instruction-013 の Outcome A。

## 実装

`DkMath/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean` に次の3公開定理を追加した。

```lean
centeredSevenSextic_not_dvd_thirteen {D q : ℕ} (hD : ¬ 13 ∣ D) :
  ¬ 13 ∣ centeredSevenSextic D q
centeredSevenSextic_no_image_of_thirteen_support {r s : ℕ}
  (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ s) :
  ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49
nestedAllocation_excluded_of_thirteen_support {M r : ℕ}
  (hr13 : ¬ 13 ∣ r) (hs13 : 13 ∣ M / r) :
  ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r)
```

既存 polynomial モジュールのみを import し、receiver の定義を変更せず既存同値の必要方向を利用した。有限体全称証明を任意自然数へ cast するため、169個の個別 example や自然数入力の上限は使わない。

`DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean` に一般 API の適用、M=3*13^12 / r=3 の named regression、商と sixth-power equality、法5 square premise の不成立、D=2 の法13値域、4定理の公理監査を保存した。具体例の巨大な自然数式の elaboration に `exponentiation.threshold 400` を用いた。

## 検証

nested Lake directory `lean/dk_math` で再開後に実行した。

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredThirteenSupport`: exit 0、9088 jobs、対象モジュールは replay 成功。
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredThirteenSupport.lean`: exit 0。一般 API と具体例を検証し、3公開定理・1回帰定理の `#print axioms` を実行。
- 公理はすべて `[propext, Classical.choice, Quot.sound]`。sorryAx なし。
- 新規2 Lean ファイルの `sorry/admit/axiom/unsafe/native_decide` 検索は一致なし。
- `git diff --check` は exit 0。新規ファイルの whitespace は別途確認した。

証拠とソースハッシュは [evidence/013-verification-summary.md](evidence/013-verification-summary.md) に記録した。Python の表と Lean の形式証明を区別し、Python 数学検証を実行したとは記載していない。

## 成立範囲

r=3 は cheap 条件と別の sixth-power 必要条件を通過し、法5の値域とも整合するが、法13 support 障害で exact receiver が不成立となる。これは同じ選択 divisor に関する結果である。全 divisor 分類や full-sieve 不存在への拡張は行わず、gate 013 で終了する。
