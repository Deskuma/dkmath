# 対応状況

PR: <https://github.com/Deskuma/dkmath/pull/53>

## 対応済み

### discussion_r3085207779

[discussion](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085207779)

はい。今回の指摘 `discussion_r3085207779` については、ローカルで確認して修正まで入れました。

修正内容は、[`ClassGroupBridge.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean) で `IsRegularPrime` が実際に `p` を使う placeholder になるよう細くし、`classGroupPTorsionFree_of_regularPrime` が regular-prime 仮定だけから現在の強い `CyclotomicClassGroupPTorsionFreeTarget` を導かない形に直したことです。あわせて [`RegularPrimeRoute.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/RegularPrimeRoute.lean) と [`Samples.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Samples.lean) も更新して、regular-prime route 側が明示的な class-group 仮定 `hCl` を受け取るように揃えました。

検証は `lake build DkMath.FLT.Kummer.ClassGroupBridge`、`lake build DkMath.FLT.Kummer.RegularPrimeRoute`、`lake build DkMath.FLT.Samples` で通しています。`DkMathTest.FLT.Kummer.RegularPrimeRouteNoSorry` も回しましたが、このターンでは完了ログを取り切れていません。

---

ご指摘どおりでした。`IsRegularPrime` が実際には `p` を使っておらず、しかも `CyclotomicClassGroupPTorsionFreeTarget` 相当の強い内容を regular-prime 仮定だけから流し込んでいたため、placeholder としても API が強すぎる状態になっていました。

この点を修正し、

- `IsRegularPrime (p : ℕ)` を少なくとも `a ^ p = 1 → a = 1` の形で `p` を使う placeholder に変更
- `classGroupPTorsionFree_of_regularPrime` は regular-prime 仮定だけから強い `CyclotomicClassGroupPTorsionFreeTarget` を導かない形に変更
- その結果として、`RegularPrimeRoute` 側は明示的な class-group 仮定 `hCl` を受け取るように整理

しました。

確認として、少なくとも以下はローカルでビルド通過しています。

- `lake build DkMath.FLT.Kummer.ClassGroupBridge`
- `lake build DkMath.FLT.Kummer.RegularPrimeRoute`
- `lake build DkMath.FLT.Samples`

ありがとうございました。
