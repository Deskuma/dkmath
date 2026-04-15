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
