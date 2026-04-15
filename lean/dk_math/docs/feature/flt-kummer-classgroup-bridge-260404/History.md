# History

prev cid: 69ca1b34-0bcc-83a2-bcfd-529624b85356
cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af
cid: 69dc6565-d700-83a7-8e6f-14cd0f32b6fa

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

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (作業概要の見出し)

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
   - `PrimitiveBeam` の honest squarefree-GN 版を
     実 caller へどこまで供給できるかを判定し、
     可能な箇所から `..._of_squarefree_GN` へ migration する

## 2026/04/15 01:32:38 JST

1. 背景:
   - `review-061`
     の認識に従い、
     次の本線は
     `PrimitiveBeam`
     の remaining research dependency を
     honest route / research route の名札でさらに分けることだと判断した
   - 判断の分岐点は
     「すぐに caller を `..._of_squarefree_GN` へ移せるか」
     と
     「まず theorem 名の上で research 依存を露出させるべきか」
     の二択だった
   - 今回は後者を先に選んだ
     :
     `Gcd.GN` と `GcdNextResearch` の caller は
     現時点では
     `Squarefree (GN ...)`
     を持っておらず、
     そのまま honest theorem へ移すより
     まず research 依存を明示する方が正確だからである
2. 実施:
   - `PrimitiveBeam.lean`
     の research 依存 theorem
     `primitive_prime_factor_forbids_perfect_pow_diff`
     と
     `primitive_prime_obstructs_GN_perfect_power`
     を、
     それぞれ
     `_research`
     名の本体へ改めた
   - 旧 public 名は
     `@[deprecated ...]`
     付き compatibility alias として残し、
     docstring で
     `..._of_squarefree_GN`
     を honest route、
     `_research`
     を未修復 route として使い分ける方針を明示した
   - そのうえで実 caller も
     旧 public 名から `_research` 名へ差し替えた
     :
     `Gcd/GN.lean`
     の
     `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add`
     と、
     `GcdNextResearch.lean`
     の
     `_hGN_not_pow`
     生成箇所
   - `primitive_prime_obstructs_GN_dth_power`
     /
     `primitive_prime_obstructs_beam_perfect_power`
     も
     `_research`
     本体に寄せ、
     `PrimitiveBeam`
     内の依存線を一本化した
3. 結論:
   - これで
     `PrimitiveBeam`
     に残る primitive obstruction 系も、
     honest 版
     `..._of_squarefree_GN`
     と
     research 版
     `_research`
     の二系統に明示分離された
   - 実コード上で
     squarefree 仮定をまだ供給していない caller は
     theorem 名の上でも
     `_research`
     依存だと見えるようになり、
     次の honest migration 対象を追いやすくなった
   - 今回の最善手は、
     無理に仮定を増やして caller を壊すことではなく、
     **research debt の位置を theorem 名で固定してから次段の移行準備を整える**
     ことだった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.PrimitiveBeam` 成功
   - `./lean-build.sh DkMath.NumberTheory.Gcd.GN` 成功
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - 旧 public 名へ付ける deprecation 属性の置換先として、
     後ろで定義される
     `..._of_squarefree_GN`
     を直接指定したところ、
     Lean が前方参照を解決できず build が失敗した
   - そのため今回は、
     deprecation 属性の置換先は先に存在する
     `_research`
     名へ向け、
     honest route の案内は docstring で補う形に修正した
6. 次の課題:
   - `Gcd.GN` / `GcdNextResearch`
     の research caller に対して
     `Squarefree (GN ...)`
     を局所供給できる経路があるかを調べ、
     可能な 1 本から
     `..._of_squarefree_GN`
     へ実 migration する

## 2026/04/15 02:20:05 JST

1. 背景:
   - 前回の次課題に従い、
     `Gcd.GN` / `GcdNextResearch`
     の research caller について
     `Squarefree (GN ...)`
     を局所供給できるかを調べた
   - 判断の分岐点は
     「既存 theorem の仮定だけから local に `Squarefree (GN ...)` を作ってそのまま migration する」
     か、
     「local supply はできないと確定させたうえで、squarefree を受け取る honest route をこの層に増設する」
     かの二択だった
   - 今回は後者を選んだ
     :
     `Gcd.GN.body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add`
     と
     `GcdNextResearch.body_not_perfect_pow`
     は現状どちらも
     `Squarefree (GN ...)`
     を仮定に持たず、
     既存の local 情報だけではそれを honest に導く経路が見当たらなかったためである
2. 実施:
   - `GcdNextResearch.lean`
     に
     `primitive_prime_contradicts_diff_dth_power_of_squarefree_GN`
     を追加し、
     primitive-prime valuation contradiction の
     squarefree-GN 版を局所化した
   - あわせて
     `body_not_perfect_pow_of_squarefree_GN`
     を追加し、
     `Squarefree (GN d x u)`
     を caller が供給できる場合の
     honest route を
     `GcdNextResearch`
     側でも明示した
   - この新 theorem は
     `PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN`
     を経由して閉じており、
     research valuation placeholder を踏まない
3. 結論:
   - `GcdNextResearch`
     でも
     `body_not_perfect_pow`
     に対する
     squarefree-GN 付き honest migration 先ができた
   - 一方で、
     既存の research caller 本体から
     `Squarefree (GN ...)`
     を局所供給する経路は今回も確認できなかった
   - したがって現時点の最善手は、
     **無理に既存 theorem の仮定を捻じ曲げるのではなく、squarefree を渡せる caller の受け口を先に増やして migration 先を固定する**
     ことだった
4. 検証:
   - `./lean-build.sh DkMath.NumberTheory.GcdNextResearch` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - `Gcd.GN` / `GcdNextResearch`
     の上位 caller 側で
     `Squarefree (GN ...)`
     を provider / bridge から受け取れる経路があるかを調べ、
     実際に 1 本を
     `body_not_perfect_pow_of_squarefree_GN`
     もしくは既存の
     `..._of_squarefree_GN`
     へ差し替える

## 2026/04/15 13:28:04 JST

1. 背景:
   - `review-062`
     の方針に従い、
     次は lower theorem をさらに磨くよりも
     `Squarefree (GN ...)`
     を already 持てる上位 branch / provider から
     honest route を 1 本でも実配線する段だと判断した
   - 分岐点は
     「`ProviderImpl` をそのまま import して upper layer を繋ぐ」
     か、
     「name conflict を避けつつ provider 契約そのものから upper layer を繋ぐ」
     かの二択だった
   - 今回は後者を選んだ
     :
     `TriominoSquarefreeGNBridgeProviderImpl`
     は既存の
     `triominoNoWieferichBridge_impl`
     と theorem 名が衝突するため、
     `CosmicPetalBridgeGN`
     / `TriominoCosmicGapInvariant`
     から直接 import するのは筋が悪かったからである
2. 実施:
   - `TriominoCosmicGapInvariant.lean`
     に
     `triominoWieferichBranchBridge_of_squarefreeGNProvider`
     を private で追加し、
     `TriominoSquarefreeGNBridgeProvider`
     から
     `triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge`
     を経由して
     current branch contract
     `TriominoWieferichBranchBridge`
     へ注入する薄い橋を作った
   - あわせて
     `triominoCosmicNoPowOnGN_of_squarefreeGNProvider`
     と
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider`
     を追加し、
     squarefree provider から
     `NoPowOnGN`
     /
     `BodyInvariant`
     まで直接届く honest route を固定した
   - これにより、
     既存の
     `triominoCosmicNoPowOnGN_of_padicValNatLeOneTarget`
     /
     `triominoCosmicBodyInvariant_of_padicValNatLeOneTarget`
     の generic target 注入に対して、
     provider 契約そのものを受ける concrete な migration 先ができた
3. 結論:
   - 今回の 1 本目の実 migration は、
     `PrimitiveBeam`
     直上ではなく
     `TriominoCosmicGapInvariant`
     側で成立した
   - つまり
     `Squarefree (GN ...)`
     を already 持てる上位 provider については、
     もはや
     `_research`
     target を明示注入せずとも
     `NoPowOnGN`
     /
     `BodyInvariant`
     まで honest route で上げられる
   - 今回の最善手は、
     **`ProviderImpl` 名の import を無理に通すことではなく、provider 契約そのものを受ける clean wrapper を上位本丸へ置く**
     ことだった
4. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl` 成功
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
5. 失敗事例:
   - `TriominoCosmicGapInvariant`
     から
     `TriominoSquarefreeGNBridgeProviderImpl`
     を直接 import して
     wrapper を置こうとしたが、
     環境内に既にある
     `DkMath.FLT.triominoNoWieferichBridge_impl`
     と同名 theorem がぶつかり、
     import 時点で build が失敗した
   - そのため、
     implementation alias ではなく
     `TriominoSquarefreeGNBridgeProvider`
     契約そのものを受ける形へ切り替えた
6. 次の課題:
   - 今回追加した
     `triominoCosmicNoPowOnGN_of_squarefreeGNProvider`
     /
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider`
     を実 caller が使える branch を探し、
     `TriominoSquarefreeGNBridgeProvider`
     を持つ上位 route から
     default / target 注入経路を 1 本差し替える

## 2026/04/15 14:11:12 JST

1. 背景:
   - 前回の次課題に従い、
     `triominoCosmicNoPowOnGN_of_squarefreeGNProvider`
     /
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider`
     を
     actual upper caller へ差し込める branch を探した
   - 調査の結果、
     `CyclotomicPrincipalization.lean`
     で
     `triominoCosmicNoPowOnGN_default`
     を concrete に使っている箇所が 2 本あり、
     特に non-first-case receiver は
     theorem 本体が小さく、
     provider 付き variant を立てる差し替え先として最も筋がよかった
   - 分岐点は
     「first-case 側の長い wrapper を provider 版へ複製する」
     か、
     「non-first-case receiver の default 注入を provider 版へ置き換える concrete variant を先に立てる」
     かの二択だった
   - 今回は後者を選んだ
     :
     変更範囲が小さく、
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider`
     をそのまま使えて、
     default 注入経路の置換先を明確に固定できるからである
2. 実施:
   - `CyclotomicPrincipalization.lean`
     に
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree_and_squarefreeGNProvider`
     を追加した
   - この theorem は
     旧
     `cyclotomicNormDescentNonFirstCaseGNPowerReceiver_of_classGroupPTorsionFree`
     が
     `bodyInvariant_of_NoPowOnGN triominoCosmicNoPowOnGN_default`
     を使っていた箇所を、
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider hSqProv`
     へ差し替えた provider-branch 版である
   - あわせて
     `cyclotomicNormDescentNonFirstCaseUnitNormalizedReceiver_of_classGroupPTorsionFree_and_squarefreeGNProvider`
     を追加し、
     実際の downstream receiver 1 段ぶんも
     provider route で繋がるようにした
3. 結論:
   - これで
     `TriominoSquarefreeGNBridgeProvider`
     を持つ upper route については、
     `CyclotomicPrincipalization`
     の non-first-case Stage 3 receiver まで
     default / target 注入を経ずに到達できる
   - つまり今回の 1 本目の concrete replacement は、
     `TriominoCosmicGapInvariant`
     で作った provider route を
     `CyclotomicPrincipalization`
     の actual caller 側へ引き上げる形で成立した
   - 今回の最善手は、
     **default theorem を直接書き換えて既存 caller を壊すことではなく、provider を持つ branch 専用の concrete variant を実 caller 層へ増設する**
     ことだった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - `CyclotomicPrincipalization`
     で今回足した
     `..._and_squarefreeGNProvider`
     版をさらに上位の split / one-shot theorem へ繋げられるかを調べ、
     first-case 側または non-first-case principalization 側でも
     provider route を 1 段上へ引き上げる

## 2026/04/15 15:26:04 JST

1. 背景:
   - `review-063`
     の整理に従い、
     いま重要なのは
     provider route を branch-local receiver で止めず、
     `CyclotomicPrincipalization`
     の split / one-shot theorem へ 1 段上げることだと判断した
   - 前回追加したのは
     non-first-case Stage 3 receiver
     (`...GNPowerReceiver...and_squarefreeGNProvider`,
     `...UnitNormalizedReceiver...and_squarefreeGNProvider`)
     までだったので、
     次の自然な対象は
     `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization`
     以降の composition 群だった
   - 分岐点は
     「first-case 側の長い wrapper に provider route を入れる」
     か、
     「non-first-case 側の composition theorem を連鎖的に provider 版へ持ち上げる」
     かの二択だった
   - 今回は後者を選んだ
     :
     既に追加した receiver provider 版をそのまま再利用でき、
     変更が pure composition で済むため、
     リスクが最小で一番高い位置まで clean route を押し上げられるからである
2. 実施:
   - `CyclotomicPrincipalization.lean`
     に
     `cyclotomicNormDescentNonFirstCase_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     を追加し、
     non-first-case principalization を
     provider route で返す variant を作った
   - 続けて
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     を追加し、
     global Stage 3 `NormDescent`
     まで provider route を引き上げた
   - さらに
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     を追加し、
     one-shot principalization まで
     clean route で供給できる形にした
3. 結論:
   - これで
     `TriominoSquarefreeGNBridgeProvider`
     を持つ branch については、
     non-first-case receiver だけでなく
     `CyclotomicPrincipalization`
     の non-first-case principalization /
     norm descent /
     one-shot principalization
     まで provider route が届くようになった
   - つまり provider route は
     `TriominoCosmicGapInvariant`
     → `CyclotomicPrincipalization` receiver
     → split / one-shot theorem
     と段階的に actual orchestration 層まで押し上がった
   - 今回の最善手は、
     **first-case 側の長い concrete wrapper を先に複製することではなく、
     既に closed した non-first-case provider route を composition theorem 群へ連鎖的に昇格させる**
     ことだった
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - `CyclotomicPrincipalization`
     で残っている
     default / non-liftable route と
     今回の squarefree provider route の住み分けを見直し、
     first-case 側にも provider variant を足すべきか、
     それとも non-first-case orchestration 側からさらに downstream caller を差し替えるべきかを判定する

## 2026/04/15 15:45:21 JST

1. 背景:
   - 前回の次課題に従い、
     `CyclotomicPrincipalization`
     に残る
     default / non-liftable route と
     squarefree provider route の住み分けを見直した
   - 調査の結果、
     `TriominoSquarefreeGNBridgeProvider`
     を値として受ける downstream caller はまだ薄く、
     すぐに外側 caller を差し替えるよりも、
     まず
     `CyclotomicPrincipalization`
     内で
     first-case も含めて provider route を閉じる方が筋が良いと判断した
   - 決定的だったのは、
     既に追加していた
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     が、
     non-first-case 側は provider route でも、
     first-case 側はなお
     `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree`
     経由の default を踏んでいた点である
   - したがって今回の分岐では
     「downstream caller 差し替え」
     より
     「first-case 側へ provider variant を追加して one-shot provider theorem を本当に clean にする」
     方を選んだ
2. 実施:
   - `CyclotomicPrincipalization.lean`
     に
     `qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_squarefreeGNProvider`
     を追加し、
     `triominoCosmicBodyInvariant_of_squarefreeGNProvider`
     から first-case gap-divisible witness を返す thin wrapper を作った
   - あわせて
     `cyclotomicPrincipalizationFirstCase_of_classGroupPTorsionFree_and_squarefreeGNProvider`
     を追加し、
     first-case principalization target まで provider route を上げた
   - さらに
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_nonFirstCase_and_squarefreeGNProvider`
     を追加し、
     global Stage 3 `NormDescent`
     の case-split でも first-case を provider route で束ねる形にした
   - 最後に
     `cyclotomicNormDescent_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     をこの新 route に差し替えた
     :
     これにより、
     既存の one-shot provider theorem は
     first-case / non-first-case の両枝で squarefree provider route を通るようになった
3. 結論:
   - 今回の判定は
     **downstream caller 差し替えより first-case provider variant の追加が先**
     で正しかった
   - 理由は、
     downstream に provider を渡せる actual caller がまだ乏しい一方で、
     `CyclotomicPrincipalization`
     内の provider one-shot theorem は
     first-case 側が default のままだったからである
   - これで
     `CyclotomicPrincipalization`
     における squarefree provider route は、
     non-first-case だけでなく first-case も含めて
     actual one-shot theorem まで clean に閉じた
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
5. 失敗事例:
   - （未報告）
6. 次の課題:
   - `CyclotomicPrincipalization`
     の provider one-shot theorem が閉じたので、
     次はそれを実際に受け取れるさらに外側 caller があるかを調べる
   - もし無ければ、
     `TriominoSquarefreeGNBridgeProvider`
     をどの orchestration / package 層で concrete に持たせるかを定め、
     default route を使っている theorem を 1 本 provider route へ差し替える

## 2026/04/15 16:11:29 JST

1. 背景:
   - 前回の次課題に従い、
     `CyclotomicPrincipalization`
     の provider one-shot theorem を
     さらに外で actual に受ける caller があるかを調べた
   - 調査の結果、
     直接それを受ける theorem は見当たらず、
     外側では依然として
     `CyclotomicNormDescentTarget`
     や
     `CyclotomicPrincipalizationTarget`
     を abstract に受ける orchestration 層が主だった
   - そこで分岐は
     「caller 探索をさらに外へ続ける」
     か
     「`TriominoSquarefreeGNBridgeProvider` を orchestration 層で concrete に持たせる」
     かになった
   - 今回は後者を選んだ
     :
     `ClassGroupBridge`
     と
     `RegularPrimeRoute`
     がまさに
     `hUnit` / `hNorm`
     を束ねて FLT 幹線へ渡す package 層であり、
     ここが provider concrete 化の最初の着地点として最も自然だからである
2. 実施:
   - `ClassGroupBridge.lean`
     に
     `qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加し、
     regular-prime route の Stage 3 `NormDescent` を
     abstract target ではなく
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     経由で concrete に供給する版を作った
   - 続けて
     `RegularPrimeRoute.lean`
     に
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加し、
     既存の推奨 mainline
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
     に対する provider concrete 版を実装した
   - これにより、
     provider route は
     `CyclotomicPrincipalization`
     の one-shot theorem で止まらず、
     `RegularPrimeRoute`
     の actual FLT theorem 1 本まで引き上がった
3. 結論:
   - 今回の判定は
     **外側 caller の探索継続より、`ClassGroupBridge` / `RegularPrimeRoute` を provider concrete orchestration 層として固定する方が正しい**
     だった
   - 理由は、
     現状の outer layer は `CyclotomicPrincipalizationTarget` や `CyclotomicNormDescentTarget` を abstract に束ねる構造であり、
     provider one-shot theorem を直接受ける caller より、
     まずそこで concrete 化する方が mainline に近いからである
   - これで
     `TriominoSquarefreeGNBridgeProvider`
     は
     `TriominoCosmicGapInvariant`
     →
     `CyclotomicPrincipalization`
     →
     `ClassGroupBridge`
     →
     `RegularPrimeRoute`
     と、FLT 幹線の orchestration 層まで届いた
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.ClassGroupBridge` 成功
   - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
   - `ClassGroupBridge`
     /
     `RegularPrimeRoute`
     の provider 版を最初は universe polymorphic なまま追加したが、
     `CyclotomicPrincipalization`
     側の provider theorem が `.{0}` 固定のため
     `CyclotomicUnitNormalizationTarget`
     の universe が噛み合わず build が失敗した
   - そのため今回は、
     provider concrete route を `.{0}` に揃えて実装し、
     既存の abstract route はそのまま保持する方針に直した
6. 次の課題:
   - `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     ができたので、
     これをさらに使える top-level / public route があるかを調べる
   - もし無ければ、
     regular-prime mainline のどの theorem を provider concrete 版へ昇格させるのが最も自然かを決め、
     legacy / abstract route との住み分けを整理する

## 2026/04/15 16:15:19 JST

1. 背景:
   - 前回の次課題に従い、
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     をさらに受ける top-level / public route があるかを調べた
   - 調査の結果、
     直接この theorem を受ける外側 caller は見当たらず、
     その外側では
     `CyclotomicNormDescentTarget`
     や
     `CyclotomicPrincipalizationTarget`
     を abstract に束ねる orchestration 層が主であった
   - したがって今回の分岐は
     「さらに outer caller を探し続ける」
     か
     「`ClassGroupBridge` / `RegularPrimeRoute` を public orchestration 層として provider concrete 版を立てる」
     かの二択になった
   - 今回は後者を選んだ
     :
     `RegularPrimeRoute`
     は review-014 以来の推奨 mainline であり、
     ここを concrete 化するのが
     provider route を public 側へ押し上げる最短手だからである
2. 実施:
   - `ClassGroupBridge.lean`
     に
     `qAdicGapReductionGapDivisible_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加した
     :
     regular-prime route の gap-divisible branch 生成を、
     abstract `hNorm`
     ではなく
     `cyclotomicPrincipalization_of_classGroupPTorsionFree_and_unitNormalization_and_squarefreeGNProvider`
     から concrete に供給する版である
   - つづいて
     `RegularPrimeRoute.lean`
     に
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加し、
     既存の推奨 mainline
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
     に対する provider concrete 版を actual FLT theorem として固定した
3. 結論:
   - 今回の判定は
     **外側 caller の探索継続より、
     `RegularPrimeRoute`
     を provider concrete public mainline の最初の着地点として昇格させる方が自然**
     だった
   - これにより
     `TriominoSquarefreeGNBridgeProvider`
     は
     `TriominoCosmicGapInvariant`
     →
     `CyclotomicPrincipalization`
     →
     `ClassGroupBridge`
     →
     `RegularPrimeRoute`
     と、推奨 regular-prime mainline まで到達した
   - したがって、現時点での public 側の住み分けは
     「abstract mainline は従来どおり保持しつつ、
     provider を concrete に持てる branch では
     `_and_squarefreeGNProvider`
     版を parallel mainline として立てる」
     のが最善だと判断できる
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.ClassGroupBridge` 成功
   - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
   - provider concrete 版を最初は universe polymorphic に保とうとしたが、
     `CyclotomicPrincipalization`
     側の provider theorem が `.{0}` 固定のため
     `CyclotomicUnitNormalizationTarget`
     の universe が一致せず build が失敗した
   - そのため今回は、
     provider concrete route は `.{0}` に揃え、
     既存の abstract route の universe polymorphism は保つ方針に修正した
6. 次の課題:
   - `RegularPrimeRoute`
     の provider concrete mainline が立ったので、
     これを使うさらに上位の public/provider 接続
     （例:
     `PrimeGe5FLTProvider`
     系や
     `TriominoPrimeProvider`
     系）
     があるかを調べる
   - もしそれらが abstract `FLTPrimeGe5Target` だけを受けるなら、
     provider concrete 版をどこで canonical default 相当として案内するかを整理する

## 2026/04/15 16:21:05 JST

1. 背景:
   - 前回の次課題に従い、
     `RegularPrimeRoute`
     の provider concrete mainline
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     をさらに受ける top-level / public provider 接続を調べた
   - 調査の結果、
     直接この theorem を呼ぶ外側 caller は見当たらなかったが、
     `TriominoCosmicPrimeGe5Core`
     には
     `triominoCosmic_globalProvider_of_FLTPrimeGe5`
     と
     `triominoPrimeProvider_of_FLTPrimeGe5`
     があり、
     abstract `FLTPrimeGe5Target`
     から
     `GlobalPrimeExponentFLTProvider`
     /
     `TriominoPrimeProvider`
     へ上げる canonical core bridge 自体は既に存在していた
   - したがって今回の分岐は
     「provider 側モジュールに regular-prime wrapper を追加する」
     か
     「依存循環を避けるため、
     `RegularPrimeRoute`
     側で provider-facing wrapper を立てる」
     かの二択になった
   - 今回は後者を選んだ
     :
     `PrimeProvider`
     側から
     `Kummer.RegularPrimeRoute`
     を import すると、
     既存の
     `Kummer.Basic`
     ←
     `PrimeProvider`
     依存と衝突して循環しうるため、
     provider concrete route の案内位置は
     `RegularPrimeRoute`
     自身に置くのが最も自然だからである
2. 実施:
   - `RegularPrimeRoute.lean`
     に
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加した
     :
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を
     `triominoCosmic_globalProvider_of_FLTPrimeGe5`
     へ合成し、
     `GlobalPrimeExponentFLTProvider`
     を直接返す public/provider 入口である
   - つづいて
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加した
     :
     同じ regular-prime concrete mainline から
     `triominoPrimeProvider_of_FLTPrimeGe5`
     を経由して
     `TriominoPrimeProvider`
     へ直結する版である
   - docstring にも、
     `TriominoSquarefreeGNBridgeProvider`
     を concrete に持てる branch では
     これらを canonical default 相当の provider-facing route とみなす方針を明記した
3. 結論:
   - 今回の判定は
     **さらに外側の caller を探し続けるより、
     `RegularPrimeRoute`
     を provider concrete public/provider 入口として閉じる方が自然**
     だった
   - これにより
     `TriominoSquarefreeGNBridgeProvider`
     は
     `TriominoCosmicGapInvariant`
     →
     `CyclotomicPrincipalization`
     →
     `ClassGroupBridge`
     →
     `RegularPrimeRoute`
     →
     `GlobalPrimeExponentFLTProvider`
     /
     `TriominoPrimeProvider`
     と、
     provider 公開面まで到達した
   - したがって現時点での住み分けは
     「abstract `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
     は theorem-parameterized route として保持しつつ、
     provider を concrete に持てる branch では
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を canonical public/provider route として案内する」
     のが最善と判断できる
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute` 成功
5. 失敗事例:
   - provider 側モジュール
     （
     `TriominoCosmicPrimeGe5Core`
     や
     `TriominoPrimeProvider`
     系）
     に直接 wrapper を置く案も考えたが、
     `PrimeProvider`
     → `Kummer`
     の逆向き import が必要になり、
     既存の依存方向と衝突するため採用しなかった
6. 次の課題:
   - いま追加した
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を、
     実際に使える top-level theorem /
     package export があるかを調べる
   - もし既存 public export が abstract route しか案内していないなら、
     `DkMath.FLT`
     公開面または関連 doc/comment のどこで
     provider concrete route を推奨導線として明記するかを整理する

## 2026/04/15 16:32:05 JST

1. 背景:
   - 前回の次課題に従い、
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     が
     実際に top-level / public export として使えるかを調べた
   - 調査の結果、
     `DkMath.FLT`
     は
     `DkMath.FLT.Kummer`
     と
     `DkMath.FLT.PrimeProvider`
     の両方を import しており、
     theorem 自体はすでに top-level import 入口から到達可能だった
   - したがって今回の分岐は
     「さらに export theorem を増やす」
     か
     「`DkMath.FLT`
     / `INDEX.md`
     / README 群で
     provider concrete route を推奨導線として明記する」
     かの二択になった
   - 今回は後者を選んだ
     :
     追加の wrapper/export は不要で、
     現状の問題は public 面での discoverability だからである
2. 実施:
   - `DkMath/FLT.lean`
     に module docstring を追加し、
     `DkMath.FLT`
     が
     `Main`
     /
     `Kummer`
     /
     `PrimeProvider`
     を束ねる top-level import 入口であること、
     および
     `TriominoSquarefreeGNBridgeProvider`
     を concrete に持てる branch の canonical provider-facing route が
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     であることを明記した
   - `DkMath/FLT.md`
     冒頭に
     「公開導線の更新メモ」
     を追加し、
     old status 文書を読む前に見るべき current route を固定した
   - `lean/dk_math/INDEX.md`
     の
     `3.10 FLT`
     節に、
     abstract regular-prime mainline と
     provider concrete public route の住み分けを追記した
   - `lean/dk_math/README.md`
     に、
     `RegularPrimeRoute`
     の provider concrete 公開導線と
     `DkMath.FLT`
     が top-level 入口である旨を追記した
   - さらに project top
     `README.md`
     にも、
     nightly 側で
     `RegularPrimeRoute`
     から
     `GlobalPrimeExponentFLTProvider`
     /
     `TriominoPrimeProvider`
     へ直結する public/provider route が案内されるようになったことを反映した
3. 結論:
   - 今回の判定は
     **新しい export の追加ではなく、
     既存 top-level import
     `DkMath.FLT`
     上で provider concrete route の案内を明記する方が自然**
     だった
   - これにより、
     `TriominoSquarefreeGNBridgeProvider`
     を concrete に持てる branch は
     `DkMath.FLT`
     を import した公開面から
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     をそのまま辿れることが、
     Lean コード側と Markdown 案内の両方で明示された
4. 検証:
   - `./lean-build.sh DkMath.FLT` 成功
5. 失敗事例:
   - 既存 public export が弱いなら
     `DkMath.FLT`
     直下にさらに wrapper theorem を増やす案もありえたが、
     import aggregator だけで十分到達可能であり、
     theorem 名の重複導線を増やす方がむしろ公開面を散らすため採用しなかった
6. 次の課題:
   - 今回明記した provider concrete route が、
     実際の利用者導線
     （例:
     `DkMath.FLT`
     import 後の theorem discovery、
     `DkMath/FLT/README.md`
     や
     `docs/PROJECT_STATUS.md`
     の更新）
     で十分かを見直す
   - 必要なら、
     `DkMath.FLT`
     公開面からの推奨導線を
     `FLT/README.md`
     などの近接ドキュメントにも同期し、
     old route と new provider route の住み分けをさらに揃える

## 2026/04/15 16:47:56 JST

1. 背景:
   - 前回の次課題に従い、
     今回明記した provider concrete route が
     実際の利用者導線で十分かを見直した
   - この確認では、
     ユーザー指示どおり
     `logs/summary_report`
     以下の既存レポートのみを参照し、
     summary report の再生成は行っていない
   - `__imports.txt`
     から
     `DkMath.FLT`
     が
     `DkMath.FLT.Kummer`
     と
     `DkMath.FLT.PrimeProvider`
     の両方を import していることを再確認し、
     `__theorems-heading.txt`
     から
     `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     が theorem discovery 上も拾えることを確認した
   - その一方で、
     `DkMath/FLT/README.md`
     は
     `d=3`
     中心の記述に偏っており、
     `docs/PROJECT_STATUS.md`
     も 2026-03-15 snapshot 評価のままなので、
     provider concrete route の current status が近接ドキュメントに同期されていないことが分かった
2. 実施:
   - `DkMath/FLT/README.md`
     冒頭に
     「現在の公開導線」
     節を追加し、
     `DkMath.FLT`
     import 後の current route を
     `d = 3`
     公開面
     と
     regular-prime / prime-ge5 provider 面
     に分けて明記した
   - 同ファイルの
     「モジュール責務」
     に
     `Kummer/RegularPrimeRoute.lean`
     と
     `PrimeProvider/*.lean`
     の役割を追記し、
     `RegularPrimeRoute`
     の provider concrete theorem 群と
     `TriominoCosmicPrimeGe5Core`
     の core bridge との関係を説明した
   - さらに
     「現在の入口」
     節にも、
     prime-ge5 / provider 向けの推奨入口
     `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     /
     `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
     を追加した
   - `docs/PROJECT_STATUS.md`
     には
     2026-04-15 の注記を追加し、
     current nightly では
     `DkMath.FLT`
     が top-level 公開面であり、
     `TriominoSquarefreeGNBridgeProvider`
     を concrete に持てる branch の canonical public/provider route は
     `RegularPrimeRoute`
     側の provider concrete theorem 群であることを明記した
   - 同ファイルの
     `PrimeProvider`
     節、
     `n > 3`
     実装状況節、
     および末尾の
     「次に打つべき手」
     節にも current route の補足を追記し、
     old snapshot 評価と new provider route の住み分けを同期した
3. 結論:
   - 今回の判定は
     **利用者導線として不足していたのは theorem export ではなく、
     `FLT/README.md`
     と
     `PROJECT_STATUS.md`
     の近接案内だった**
   - summary report 上でも、
     theorem discovery と import 導線そのものはすでに成立している
   - したがって現時点の最善手は、
     `DkMath.FLT`
     を import した利用者に対し、
     `d=3`
     なら `Main`、
     `TriominoSquarefreeGNBridgeProvider`
     を持つ prime-ge5 branch なら
     `RegularPrimeRoute`
     の provider concrete theorem 群、
     という住み分けをドキュメントで先回りして示すことだった
4. 検証:
   - Lean コード変更なし
   - summary report の既存出力
     `logs/summary_report/__imports.txt`
     /
     `logs/summary_report/__theorems-heading.txt`
     を参照して導線を確認
5. 失敗事例:
   - `PROJECT_STATUS.md`
     全体を current state に全面書き換える案もあったが、
     この文書は 2026-03-15 snapshot 評価としての価値も残っているため、
     今回は上書きではなく
     2026-04-15 注記を重ねる方針を採った
6. 次の課題:
   - 近接ドキュメントの同期は進んだので、
     次は
     `DkMath.FLT`
     import 後に実際に theorem を探す利用者が
     `RegularPrimeRoute`
     側の provider concrete route へ迷わず到達できるかを、
     必要なら
     `DkMath/FLT/Samples.lean`
     や
     `DkMath/FLT` 配下の追加 README
     で補強する
   - 併せて、
     high-exponent 側の current open が
     「provider route の不在」ではなく
     「その route を埋める数論核の未完」
     であることを、
     他の status 文書にも揃えるかを判定する
