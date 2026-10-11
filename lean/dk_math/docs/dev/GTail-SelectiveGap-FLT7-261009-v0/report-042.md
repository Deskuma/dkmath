# Step042 report — proof direction and branch-specific decision audit

2026-10-11。Outcome B（research/source audit）、STOP042。
Base HEAD `2ef7a30dd97df285b31a089317ae550cd1b960a6`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
[source inventory](source-inventory-042.md) / [research decision](research-decision-042.md)。

## 結果

documentation-only の指定に従い、terminal / lifted / ramified / CRT の actual source contracts を
比較した。**新たに実装する Step043 proof target は選ばず、停止を推奨する。**
提示された候補 I は既証明、II/III は独立な数論的構成・評価の具体式が欠落している。
これは候補を架空の theorem にせず、根拠がなければ停止する acceptance 分岐に対応する。

新 production/test owner、Lean example、public theorem、public axiom を追加していない。
新 Lean invocation / build / suite / axiom audit も行っていない。
既存結果を source/proof-route として調査したので、今回の kernel 再検証と呼ばない。
GitHub への照会は行わず、記載 HEAD のローカル実 source を用いた。

## 指示書と現行 source の相違・訂正

instruction-042 §3.4 / Candidate I、review-041 の「Row-Z signed extraction open」は
TERM-009 時点の状態であり、現行 TERM-010 では閉じている。

[SevenBaseTerminalRowZSignedResidualCore.lean](../../../DkMath/FLT/Seven/SevenBaseTerminalRowZSignedResidualCore.lean):

- 115行: `nonempty_rowZSignedResidualCore`。
- 162行: residual core と conjugate の gcd が unit。
- 192行: `exists_residualCore_eq_seventh_power`。
- 211行: `AwaySevenBaseTerminalRowZProfile.nonempty_signedRamifiedArithmeticObligation`。
- 223行: actual canonical inhabitant。
- 233行: actual `signedRamified` normal form。
- 256行: terminal の `ramifiedChartResolution`。

その proof は alternating positive split、signed coordinate coprimality、sevenAxis peel、
terminal residual、exact norm=b^7、Euclidean/GCD coprime extraction、units ±1 absorption を使う。
「抽出が source hEq から従う」という名前だけの仮定ではない。
[SevenBaseTerminalRamifiedSummit.lean](../../../DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean):108/162/232
は Y/Z の共通 summit まで実際に構成している。
既存 `DkMath/FLT/Seven/docs/ROADMAP.md`:596–622 にも TERM-010 完了が記載されている。

従って accepted branch ledger は **terminal seed impossible / lifted seed open /
Row-Z extraction completed / downstream global closure open** と訂正した。
「Row-Z signed packet 自体が impossible」とは推論しない。
旧 review / instruction / report の文章は変更せず、今回文書に訂正理由を記録した。

## Proof-direction audit

Step040 certificate は all-support + strict size → Δ=0 → Fermat7Equation。
結論は False ではない。既に CounterexamplePack.hEq がある場合 Δ=0 とその congruences は
直接得られるので、certificate に戻すだけでは original tuple を排除しない。
Step041 の actual countermodels は basic positive primitive focus から二つの仮定が
別々に出ないことを示した。hypothetical Fermat source の全追加構造に対する
新 global invariant の存在まで否定したわけではない。

terminal exponent1 の seed/provider は
[SevenBaseTerminalDescentSeedExclusion.lean](../../../DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean):40/49
で negated Nonempty が証明済み。seed→2≤exponent の converse はない。
これを universal reconstruction の未実装扱いにしない。
Row-Sum は actual False、Row-Y は swapped natural ramified、Row-Z は signed ramified。
いずれも surviving ramified route の終端排除までを意味しない。

FUSION visible signed roots の seventh-power difference は exact depth5。
`no_direct_signedFermatSevenChart` が visible next-chart shortcut を否定する。
original hypothetical chart を否定する theorem ではない。
internal depth5→4 は actual primitive reconstruction obligation と別。
「obligation の inhabitant がない」は **未構成** を表し、その Prop の否定証明を表さない。
追加の depth-four finite/nested/centered owner も調べ、同値 receiver と conditional family
exclusion を未構成の new global proof と混同しなかった。

CRT の original residual と independently centered weighted residual を別々に記録した。
original residual 四つが小さければ original=model*s^weights になるが、
既存 receiver の centered weighted=model*s^weights と同じ結論ではない。
original=weighted の bridge、または original equality に対する別の row mismatch が必要。
九つの fixed first residuals の再証明も、新 independent inequality にはならない。

## 三候補の評価と実装再開条件

詳細な(a)–(i)評価は research-decision-042.md に記載した。

| Candidate | Current decision | Needed before a later implementation |
|---|---|---|
| I Row-Z signed extraction | 既証明、選択対象から除外 | 抽出後の新 invariant / additive reconstruction と global source connection |
| II lifted-away seed | unresolved two候補では優先1位、実装未選択 | explicit next triple map、primitive additive identity、exact source-match、全分岐の indexed descent |
| III original CRT bound | 優先2位、実装未選択 | original residual の独立 bound の具体式、original/centered bridge または直接 row contradiction |

新 theorem-sized target の選択数0。選択したように見せる skeleton、conditional field の追加、
finite/local equivalence の再包装は行わない。imports の追加0、source DAG への変更0。
将来の technique が未決定なので import cost や proof 難易度の測定値を作らない。
後続で具体式が提示される場合の最初の falsifiable lemma と focused verification targets を
decision 文書に示したが、今回は実行していない。

## 既存 Lean 結果からの気づき・評価した命題

1. 宣言元の obligation owner だけを読むと、後続 owner の inhabitant を見落とす。
   今回は facade の imports と TERM-010 source を辿ることで Row-Z の既証明を確認できた。
   今後も definition→constructors→consumers の順で final frontier を確認する。
2. terminal seed 不存在と terminal CounterexamplePack 不存在は別命題。
   seed を排除した結果だけで FLT7 を結論しない。lifted の必要条件を十分条件にしない。
3. 異なる discriminant の carrier を区別した。旧 TraceOneInt(-2) は Euclidean と unit吸収が
   実装されている。E(-1)↔degree-six R の no-hom はこの旧 recipient の障害ではない。
4. Row-Z の first-lemma 候補として primitive signed coordinates、norm source、gcd-conjugate、
   seventh-root extraction を評価したが、全て既存である。重複実装を棄却した。
5. lifted の「旧 |root.snd| が新 carrier」だけでは positivity/primitive/hEq はない。
   new additive triple map を具体化することが、本当に source-indexed descent に進む最初の課題。
6. CRT winding multiple の小ささは independently centered factors の小ささではない。
   weighted scale は3/7乗なので、個々の centered bound から product bound への飛躍を避ける。
7. internal carrier depth4 を新 away carrier にした場合、new away root は depth3であり、
   old inner root depth4をそのまま使うことも既存 theorem で否定されている。
8. 新 Lean propositions / examples は試していない。上記は existing proof routes と提案命題の
   静的比較であり、新たな kernel-checked mathematical result の報告ではない。

## 作業・検証記録

read-only inspection は cat / sed / rg / rg --files / wc -l で actual owners、
review/report/frontier-041、old STATUS/ROADMAP、facade を調べた。
namespace / implicit-explicit arguments / fields / proof body を確認し、inventory に
source の verbatim signatures と行番号を転記した。新 #check / #print は不要と判断した。

初回探索で guessed filenames TraceOneArithmetic、TraceOnePowerExtraction、AwaySevenPivotDepth、
SevenPrimary* / SevenPrimaryPivotDepth は存在せず cat/sed/rg の read が失敗した。
rg により actual QuadraticCoprimeFactor / QuadraticEuclidean / SevenPivotDepthPacket /
SevenPivotDescentAudit を発見して訂正した。これは数学的失敗や compiler failure ではない。
初回 workspace audit は git ls-files の cwd-relative path を root-relative と比較して assertion が失敗。
比較を cwd-relative に合わせ、source-link / signature / whitespace / unchanged-owner checks を再実行して成功した。
`rg --files -g AGENTS.md` の該当0も source failure と数えない。

最終検査コマンド:

```sh
git diff --check
git diff --name-only
git status --short
```

exit0。最終 docs の source-link existence、転記 signature の source一致、newline、tab、
trailing whitespace を Python で検査した。tracked diff は指定 ROADMAP 一つのみ、
既存 HEAD bytes を保持して追記。新ファイルは inventory/decision/report の3件のみ。
production/test/facade/old source/review/correction の変更0。

Outcome B research audit として停止。新 FLT7 theorem、terminal contradiction、
primitive descent、recursive closure は追加していない。
