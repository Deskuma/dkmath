# Git diff / Report / Review

## Add: docs: report: issue-petal-028-to-042

gch: e3f8918fe7c52b61f662d94b8940f342003e424a

## Report

整理しました。今回の判断は明確で、`issue-petal-028` は「完全削除」ではなく「通常路線へ戻るための blocker としては解消」です。

作成・更新した docs:

- 新規: [report-petal-042.md](/home/deskuma/develop/lean/dkmath/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-042.md)
- 更新: [issue-petal-028.md](/home/deskuma/develop/lean/dkmath/lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md)

レポートでは、当初の懸念を以下の観点で整理しました。

```text
偽 theorem の確認:
  achieved

Zsigmondy は存在、NoLift/squarefree は重複度、という分離:
  achieved

PrimitiveBeam / ValuationFlow / ABC の honest route:
  achieved

FLT NoWieferich valuation surface の Research 分離:
  achieved

Research placeholder の完全削除:
  not complete, intentionally deferred
```

結論としては、次へ戻れます。

```text
Petal -> Zsigmondy 本格接続
```

ただし、旧 `squarefree_implies_padic_val_le_one_research` を証明しに行くのではなく、今後も次の分離を維持する方針です。

```text
Zsigmondy:
  primitive q の存在

Petal / GN / Anchor:
  q の位置づけ

NoLift / squarefree:
  padicValNat <= 1 の重複度制御
```

検証は docs-only なので Lean build は追加で回していません。`git diff --check` は通っています。

## Review

うむ、これは **issue-petal-028 の blocker 解消レポートとして採用でよい**。
添付の `report-petal-042.md` も確認したが、判断は明確で筋が通っている。

## レビュー結論

```text
e3f8918...
  -> 採用可

issue-petal-028:
  -> mainline blocker としては closed

Research placeholder:
  -> 完全削除ではなく、歴史的・研究的負債として deferred

次:
  -> Petal -> Zsigmondy 本格接続へ戻る
```

## この判断が正しい理由

旧問題は、

```lean
squarefree_implies_padic_val_le_one_research
padicValNat_primitive_prime_factor_le_one_research
```

を「証明すれば進める」と見ていたことだった。
しかし実際には、これは強すぎる命題で、反例がある。

```text
d = 3, a = 5, b = 3, q = 7
5^3 - 3^3 = 98 = 2 * 7^2
```

だから、正しい対応は「証明する」ではなく「分解して置き換える」だった。
今回の report はその判断をきちんと固定している。

## 達成済みの分離

いまは、この三層が Lean API として実装済みになった。

```text
Zsigmondy:
  primitive q の存在

Petal / GN / Anchor:
  q が boundary ではなく S0/GN 側にいること

NoLift / squarefree:
  q の重複度、つまり padicValNat <= 1
```

さらに downstream も接続済み。

```text
PrimitiveBeam:
  primitive witness + NoLift GN
  -> padicValNat <= 1

ValuationFlow / ABC:
  diffMass / local load <= 1

FLT:
  Branch-B primitive-prime inputs
  -> PrimitiveBeam witness
  -> NoLift valuation target
```

これは、`issue-petal-028` が当初ブロックしていた範囲を十分に解消している。

## 特に重要な closure 点

`report-petal-042.md` のこの整理は良い。

```text
False theorem identified:
  complete

Counterexample recorded:
  complete

Honest replacement theorem surface:
  complete

ABC migration:
  complete for the current public wrappers and examples

FLT valuation migration:
  complete for the no-sorry valuation surface

Research import isolation:
  mostly complete

Research placeholder deletion:
  not complete, intentionally deferred
```

「完全削除していないから未解決」ではなく、

```text
通常路線へ戻る blocker としては解消
```

という判定が正しい。

## 残り Research debt の扱い

残っているもの：

```text
ZsigmondyCyclotomicResearch.lean
  squarefree_implies_padic_val_le_one_research

GcdNextResearch.lean
  research boundary receiver area の remaining sorry
```

これは今すぐ消す必要はない。
なぜなら本線の honest route はもう別にある。

```text
PrimitiveBeam
ValuationFlow
ABC.ValuationFlowBridge
Petal.PrimitiveD3ValuationBridge
FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

つまり、旧 placeholder は「本線 API の根」ではなくなった。
ここが大事じゃ。

## `issue-petal-028.md` の status update も妥当

この追記は良い。

```text
This issue is closed as a blocker for the main Petal -> Zsigmondy route.
```

「closed」と言い切りつつ、すぐ下で

```text
The old research theorem is still intentionally not proved.
```

と明記しているので、誤解が少ない。
この書き方なら、将来見返した時に「なぜ sorry が残っているのに閉じたのか」が分かる。

## 次に戻るべき本線

はい、次は予定通りこちら。

```text
Petal -> Zsigmondy full connection
```

ただし、次の段階でもこの分離は維持する。

```text
existence:
  Zsigmondy primitive divisor

location:
  Petal / S0 / GN / Anchor carrier

multiplicity:
  NoLift or squarefree hypothesis
```

このルールを守れば、また `padicValNat <= 1` を Zsigmondy だけで出そうとする罠には戻らない。

## 次の実装候補

自然な次の一手は、`d = 3` から少し抽象度を上げる準備じゃな。

現状：

```text
DkMath.Petal.ZsigmondyD3Bridge
DkMath.Petal.PrimitiveD3ValuationBridge
```

次はたぶん、

```text
Petal/Zsigmondy の full connection へ向けて、
d = 3 固定で閉じた witness sharing を、
general d 用の vocabulary にどう持ち上げるか
```

を見る段階。

ただし、いきなり full Zsigmondy へ飛ぶより、まずは docs / API 設計で、

```text
D3 で成立した三層分離を general d でどう表現するか
```

を固定すると安全じゃ。

## 総括

今回の report は、Petal 視点の利点がよく出ている。

```text
Petal は、Zsigmondy witness をただの存在素因子としてではなく、
S0/GN/Anchor 上の位置を持つ witness として読ませた。

そのうえで、valuation は NoLift/squarefree へ分離した。
```

これは DkMath らしい整理じゃ。

判定：

```text
issue-petal-028:
  operationally closed

Petal -> Zsigmondy:
  resume mainline

old research placeholder:
  do not prove
  keep isolated
  replace callers with honest layers
```

うむ。
対応をここで収束としてよい。次は、Petal/Zsigmondy 本線へ戻れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md b/lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md
index d8c8e9c6..8c389051 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md
@@ -2,6 +2,30 @@
 
 [現況: review-028](./review-petal-028.md)
 
+## Status update: 2026-06-14
+
+This issue is closed as a blocker for the main Petal -> Zsigmondy route.
+
+The old research theorem is still intentionally not proved.  The current repair
+route is to use the separated honest layers:
+
+```text
+Zsigmondy:
+  primitive prime existence
+
+Petal / GN / Anchor:
+  location away from boundary
+
+NoLift / squarefree:
+  multiplicity control
+```
+
+Current closure report:
+
+```text
+./report-petal-042.md
+```
+
 ## ABC / FLT 両方から参照される命題（主張の強い命題）
 
 以下が `DkMath.FLT.*` / `DkMath.ABC.*` 両方から参照されている。
````
`````
