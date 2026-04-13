# History

prev cid: 69ca1b34-0bcc-83a2-bcfd-529624b85356
cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [001](History-001.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (template)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

## 2026/04/13 17:49:50 JST

1. 背景:
   - 直前の整理で
     `padicValNat_d3_upper_bound`
     は legacy wrapper と位置づけ直されたが、
     新規 caller が使うべき replacement としては
     boundary 側の exact theorem 群しか前に出ておらず、
     primitive 側の着地点が theorem 名としてまだ薄かった
   - `review-059`
     の migration 方針に沿うなら、
     `d = 3`
     の primitive route
     `q ∣ a^3 - b^3 ∧ ¬ q ∣ a - b`
     に対する honest upper bound を
     直接呼べる形で立てておくのが筋だった
2. 実施:
   - `GcdNextResearch.lean`
     に
     `padicValNat_d3_primitive_upper_bound`
     を追加し、
     `q ∣ a^3 - b^3`
     かつ
     `¬ q ∣ a - b`
     の primitive branch で
     `padicValNat q (a^3 - b^3) ≤ 1`
     を no-`so#rry` で直接返す補題を固定した
   - 証明は
     `padicValNat_le_one_of_prime_divisor_case_three_strong`
     と
     `padicValNat_a2_ab_b2_upper_bound_stage1`
     を束ねるだけの薄い wrapper に留め、
     `b = 0`
     の退避枝も
     `q ∣ 1`
     から `q = 1`
     を導いて `Nat.Prime q` と矛盾させる形で閉じた
   - そのうえで
     `padicValNat_d3_upper_bound`
     の docstring を更新し、
     新規 caller 向けの recommended replacement 一覧に
     `padicValNat_d3_primitive_upper_bound`
     を追加した
3. 結論:
   - `d = 3`
     の caller migration 先は、
     これで
     primitive route には
     `padicValNat_d3_primitive_upper_bound`
     、
     boundary route には
     `padicValNat_d3_canonical_case_split`
     /
     `padicValNat_d3_layer_b_case_split`
     /
     exact valuation theorem 群、
     という形で見通しよく揃った
   - これにより
     `padicValNat_d3_upper_bound`
     を温存する理由は
     さらに
     compatibility だけ
     に縮み、
     今後は実 caller をこの分配先へ順次寄せるだけの状態に近づいた
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - （未報告）

## 2026/04/13 22:19:47 JST

1. 背景:
   - `padicValNat_d3_upper_bound`
     の外部 caller はすでに消えており、
     repo 内検索では実コード上の呼び出し先が残っていなかった
   - そこで
     `review-059`
     の「最初の caller を 1 本だけ移植」
     は、
     まず
     `GcdNextResearch.lean`
     内の legacy helper が抱えていた primitive branch の重複証明を
     新 API に差し替える形で着手することにした
2. 実施:
   - `padicValNat_d3_primitive_upper_bound`
     の定義位置を
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     より前へ移し、
     内部 caller から参照できるようにした
   - その上で
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     の
     `q ∤ a - b`
     枝にあった
     `padicValNat_le_one_of_prime_divisor_case_three_strong`
     と
     `padicValNat_a2_ab_b2_upper_bound_stage1`
     の直書きを削り、
     `padicValNat_d3_primitive_upper_bound`
     を呼ぶ形へ差し替えた
   - これにより、
     旧 `padicValNat_d3_upper_bound`
     family の内部でも
     primitive route の仕事は
     新 API 側へ一本化された
3. 結論:
   - 外部 caller はまだ無いが、
     最初の migration 例として
     **legacy helper 内の primitive branch を新 API 呼び出しへ置換**
     できた
   - 以後、
     `padicValNat_d3_upper_bound`
     周辺の残務は
     boundary receiver 注入だけにさらに縮退し、
     primitive 側のロジックは
     `padicValNat_d3_primitive_upper_bound`
     へ集約された
   - 次に外部 caller が現れる場合も、
     primitive branch については
     すでに migration 先が実使用付きで固定された状態になった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - （未報告）

## 2026/04/13 22:22:43 JST

1. 背景:
   - `padicValNat_d3_upper_bound`
     はすでに
     docstring 上では legacy wrapper と明示され、
     primitive route / canonical split / layer-B split への移行先も揃っていた
   - ただし theorem 自体には
     Lean の deprecation 属性が付いておらず、
     将来の caller が警告なしに旧 API を掴める状態だった
2. 実施:
   - `GcdNextResearch.lean`
     の
     `padicValNat_d3_upper_bound`
     に
     `@[deprecated padicValNat_d3_canonical_case_split (since := "2026-04-13")]`
     を追加した
   - 置換先名は
     `d = 3`
     valuation story の正規入口として固定済みの
     `padicValNat_d3_canonical_case_split`
     を採用し、
     詳細な分配先
     `padicValNat_d3_primitive_upper_bound`
     /
     `padicValNat_d3_layer_b_case_split`
     は引き続き docstring に残した
3. 結論:
   - これで
     `padicValNat_d3_upper_bound`
     は
     **説明上だけでなく Lean 上も deprecated 相当**
     の扱いになった
   - 新規 caller は warning によって
     canonical split への移行を促され、
     旧 theorem は compatibility のためだけに残る状態がより明確になった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - （未報告）

## 2026/04/13 22:32:03 JST

1. 背景:
   - 次の一手として、
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     を
     legacy / research 専用の場所へ落とし、
     `GcdNextResearch`
     の残る debt を
     `d = 3`
     compatibility wrapper ではなく
     `d > 3`
     戦線へ押し出す方針を採った
   - 直前の状態では、
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     という名前がまだ mainline helper 風に見える一方、
     実態としては
     historical boundary receiver target を引数に受ける
     research helper だった
2. 実施:
   - `GcdNextResearch.lean`
     の既存 helper を
     `padicValNat_d3_upper_bound_of_boundaryReceiver_research`
     へ改名し、
     docstring でも
     research-only helper
     であることを明示した
   - 旧名
     `padicValNat_d3_upper_bound_of_boundaryReceiver`
     は
     `@[deprecated ...]`
     付きの compatibility alias として残し、
     `padicValNat_d3_upper_bound_of_boundaryReceiver_research`
     への移行警告を出す形にした
   - さらに
     private lemma
     `padicValNatD3BoundaryReceiverTarget_from_legacy_squarefree_research`
     を追加し、
     `squarefree_implies_padic_val_le_one`
     に由来する
     `d = 3`
     legacy boundary receiver 注入を
     research 専用の局所名の下へ隔離した
   - その上で
     `padicValNat_d3_upper_bound`
     は
     deprecated の旧 helper ではなく
     `padicValNat_d3_upper_bound_of_boundaryReceiver_research`
     と
     上の private lemma
     だけを使う形へ差し替えた
3. 結論:
   - これで
     `GcdNextResearch`
     における
     `d = 3`
     legacy debt は
     theorem 名の上でも
     **research-only helper + private compatibility injection**
     に整理された
   - build warning 上の direct `sorry` は引き続き
     `padicValNat_upper_bound_layer_b_stub`
     の
     `d > 3`
     戦線だけに残り、
     `GcdNextResearch`
     の主な honest migration 作業は
     いったん整理完了と見てよい状態になった
   - 次の主戦場は、
     このまま
     `ZsigmondyCyclotomicResearch`
     側の honest migration と
     statement repair を進めることになる
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - （未報告）

## 2026/04/13 22:40:42 JST

1. 背景:
   - `GcdNextResearch`
     側の `d = 3` legacy 整理が済んだので、
     主戦場を
     `ZsigmondyCyclotomicResearch`
     の honest migration へ戻した
   - 現状の問題は、
     true statement を表す
     `..._honest`
     が既にある一方で、
     旧 public 名
     `squarefree_implies_padic_val_le_one`
     /
     `padicValNat_primitive_prime_factor_le_one`
     がそのまま research placeholder を背負っており、
     downstream caller からは
     honest 依存と research 依存が定理名の上で区別しにくかったことにある
2. 実施:
   - `ZsigmondyCyclotomicResearch.lean`
     で
     `squarefree_implies_padic_val_le_one_research`
     と
     `padicValNat_primitive_prime_factor_le_one_research`
     を追加し、
     unrepaired statement に依存する route を
     theorem 名の上で research 専用に分離した
   - 旧 public 名
     `squarefree_implies_padic_val_le_one`
     /
     `padicValNat_primitive_prime_factor_le_one`
     は
     `@[deprecated ...]`
     付きの compatibility alias とし、
     置換先を
     `..._honest`
     へ向けた
   - さらに
     remaining caller の実コード参照も
     旧 public 名から
     `_research`
     名へ差し替えた
     :
     `PrimitiveBeam.lean`
     の 2 箇所、
     `GcdNextResearch.lean`
     の research-only boundary receiver 注入、
     `CosmicPetalBridgeGNNoWieferichResearch.lean`
     の primitive-core theorem
   - これにより
     actual code path 上で
     research debt がある箇所だけが
     `_research`
     名を明示的に踏む構造になった
3. 結論:
   - `ZsigmondyCyclotomicResearch`
     側の honest migration は、
     「使える caller は `..._honest` へ寄せ、
     まだ寄せられない caller は `_research` 名へ落とす」
     という整理段階まで進んだ
   - これで
     unrepaired statement の root は依然
     `squarefree_implies_padic_val_le_one_research`
     に残るが、
     旧 public 名を mainline API と誤認する余地はかなり減った
   - 今後の作業は、
     squarefree bridge を持てる caller をさらに
     `..._honest`
     へ移し、
     持てない箇所だけを
     `_research`
     依存として追跡する、という形にしやすくなった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.ZsigmondyCyclotomicResearch` 成功
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
   - `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - （未報告）
