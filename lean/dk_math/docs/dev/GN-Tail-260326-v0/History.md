# History of GN / G / GC Naming and Refactor Plan

## Log

### 日時: 2026/03/26 JST

1. 目的:
   - `GN` / `G` / `Gn` / 将来の `GC` の命名・配置の衝突を、
     現在ワークスペースでどう抱えているかを棚卸しする。
   - `高次 Tail 構造による一般化 GN 多項式` と
     `G 構造から D-加群へ` の未来設計を踏まえ、
     どこから refactor すべきかを明確にする。

2. 調査対象:
   - `[docs/not_implements/高次 Tail 構造による一般化 GN 多項式の定義.md]`
   - `[docs/not_implements/G構造からD-加群へ.md]`
   - `[lean/dk_math/DkMath/CosmicFormula/Defs.lean]`
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
   - `[lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean]`
   - `rg` による `GN` / `Gn` / `G` / `Gamma` 系の横断検索

3. 事実確認:
   - `Defs.lean` には
     - `G (R) (x u) d`
     - `Gn (R) (x u) d n`
     - `Big / Body / Gap`（ただし `ℝ` 固定）
     がある。
   - しかし `Defs.lean` の `Body` は `G ℝ x u d` そのものであり、
     後続 mainline の
     `Body = x * GN`
     あるいは
     `Body = x * G`
     とは意味が一致していない。
   - `CosmicFormulaBinom.lean` には
     - `CommRing` 側 `G`
     - `CommSemiring` 側 `GN`
     - `Big / Gap / Body`
     があり、
     downstream 実装は主にこちらを参照している。
   - `NumberTheory/Gcd/GN.lean` や
     FLT / Zsigmondy / PrimitiveBeam 周辺は、
     既に `DkMath.CosmicFormulaBinom.GN` を正規 API として使っている。
   - 文書側では
     - `GN` は差冪 `(x+u)^d - u^d = x * GN`
     - `G` は Body `(x+u)^d - x^d = u * G`
     - `Γ_{d-1}(x,u)` は `G` 構造の別記法
     という 3 層が併存している。
   - `GC` は現状コード未実装で、
     複素版計画書・複素半宇宙式メモなど将来設計にのみ現れる。

4. 調査結論:
   - mainline の事実上の中心は `CosmicFormulaBinom.GN` であり、
     `Defs.lean` の `Gn` は名前が近いのに下流からほぼ使われていない。
   - `Defs.lean` は
     - 型が `ℝ` 固定の定義を持つ
     - `Body` の意味が mainline とずれる
     - `G / Gn` の命名が `CosmicFormulaBinom.G / GN` と競合する
     ため、
     現状では refactor の起点候補になっている。
   - 文書設計としては
     - `GN = standard tail (r = 1)`
     - `GZ <- G`（Body 正規化側）
     - `GC` 新設（複素化）
     という成長図が見えている。
   - したがって refactor の本筋は
     「`Gn` を一般 tail 構造へ昇格させ、
      `GN` / `G` / `GC` を同じ family の specializations として並べ直す」
     方向になる。

5. 現時点の見立て:
   - まず canonical family を 1 つ決める必要がある。
   - 最有力は
     `GNtail d r x u` あるいは `GNGen d r x u`
     のような一般 tail 定義を本体にして、
     - `GN d x u := GNtail d 1 x u`
     - `Big d x u := GNtail d 0 x u`
     - `tailTop d x u := GNtail d d x u = 1`
     を派生化する構成。
   - その上で
     `G` 側は変数役割の swap / Body 正規化 specialization として再定義し、
     `Γ` は notation / doc alias に留めるのが自然に見える。
   - `Defs.lean` は最終的に
     旧名 alias 層へ縮退するか、
     役割を失う可能性が高い。

6. refactor 候補の優先順位:
   - 第1段:
     `CosmicFormulaBinom` に一般 tail family を新設し、
     `GN` をその `r = 1` specialized notation に落とす。
   - 第2段:
     `Defs.lean` の `Gn` と `Body` を、
     mainline と整合する alias / wrapper へ置き換えるか、
     旧実験層として隔離する。
   - 第3段:
     `G` 構造文書で言う `G_{d-1}` / `Γ_{d-1}` を、
     Lean 上では
     `Body`-normalization family として formalize する。
   - 第4段:
     複素版 `GC` を、
     既存 `GN` / `G` family の scalar extension として設計する。

7. 当面の実装方針:
   - いきなり全体 rename はしない。
   - 先に tool 定理補題として
     一般 tail family の定義・基本恒等式・special cases
     を下層へ実装し、
     そのあと `GN` / `G` / `Defs.Gn` の接続を整理する。
   - 理由:
     下流（FLT / NumberTheory / Zsigmondy）が既に `CosmicFormulaBinom.GN`
     を多数参照しているため、
     先に refactor だけ進めると破壊範囲が大きい。

8. 次の課題:
   - `GN` family の canonical placement を
     `CosmicFormulaBinom` に置くか、
     `CosmicFormula/Defs` を整理して移すかを決める。
   - 一般 tail family の仮名
     `GNtail` / `GNGen` / `GSeries`
     を比較し、命名を確定する。
   - `Defs.lean` の `Gn` を、
     実際に残すべき alias なのか
     置換対象なのかを次段で判断する。

### 日時: 2026/03/26 15:25 JST

1. 目的:
   - 調査結果を踏まえ、
     一般 tail family 実装の開始前に
     命名・配置・移行方法を合意事項として固定する。

2. 今回の合意:
   - 一般 tail family は
     `[lean/dk_math/DkMath/CosmicFormula/GTail.lean]`
     を新設して実装する。
   - `CosmicFormulaBinom.lean` は
     `GTail.lean` を import する側に回し、
     本線 `GN` は general tail の `r = 1` specialization とする。
   - 既存 `GN` は当面 `def` ではなく `abbrev` wrapper にする。
     想定形:
     `abbrev GN ... := GTail d 1 x u`
   - 以後の下流新規実装では、
     必要に応じて `GTail` 直接参照も許容し、
     既存コードは段階的に移行する。

3. この方針を採る理由:
   - 下流は既に `CosmicFormulaBinom.GN` を広く参照しており、
     先に rename / move をかけると破壊範囲が大きい。
   - `abbrev` wrapper なら、
     移行期でも既存の展開系証明や `simp [GN]` が壊れにくい。
   - `GTail.lean` を `CosmicFormulaBinom.lean` より前段に置くことで、
     一般 family を canonical source として扱える。

4. 実装開始時の最小スコープ:
   - `GTail` 本体の定義
   - tail 分解の基本恒等式
   - `r = 0`
   - `r = 1`
   - `r = d`
   - 基本再帰
   - 評価点 `x = 0`

5. 現時点の保留事項:
   - 一般 tail family の公開名を
     `GTail` で行くか、
     内部で `GTail` / `GNtail` を併置するかは、
     実装時の可読性を見て最終決定する。
   - `Defs.lean` の `Gn` はこの段階では触らず、
     一般 tail family 実装後に alias 化 / 廃止候補として再評価する。

6. 次の課題:
   - `GTail.lean` を新設し、
     一般 tail family の最小 API を実装する。
   - その後
     `CosmicFormulaBinom.GN` を `abbrev` wrapper へ置き換え、
     既存補題がそのまま通るかを確認する。

### 日時: 2026/03/26 15:48 JST

1. 目的:
   - `GTail.lean` を新設し、
     一般 tail family の最小 API を先に下層へ固定する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/GTail.lean]`
     を新設した。
   - 以下を実装した。
     - `GTail` の本体定義
     - `add_pow_eq_prefix_add_xpow_mul_GTail`
     - `GTail_zero_eq_add_pow`
     - `GTail_self_eq_one`
     - `GTail_rec`
     - `GTail_eval_zero`
     - `GTail_one_eq_sum`
   - `GTail_one_eq_sum` により、
     既存 `GN` の係数和の形へ戻す専用 bridge も先に置いた。

3. 結論:
   - 一般 tail family の最小 API は、
     既存 `GN` を wrapper 化する前提として十分な形で先に独立した。
   - とくに
     - tail 分解
     - `r = 0`
     - `r = d`
     - 再帰
     - `x = 0` 評価
     - `r = 1` 既存和形への bridge
     が揃ったため、
     次段は `CosmicFormulaBinom.GN := GTail d 1 x u`
     への置換に移れる。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`
     を実行し、ビルド成功を確認した。

5. 備考:
   - この段階では downstream にはまだ触れていない。
   - `Defs.lean` の `Gn` 整理は保留のままにしている。
   - `GTail_one_eq_sum` は、
     wrapper 化の直後に既存 `GN` 補題群を移植する際の基礎補題になる。

6. 次の課題:
   - `CosmicFormulaBinom.lean` に `GTail` を import し、
     既存 `GN` を `abbrev` wrapper へ置き換える。
   - `cosmic_id_csr'` など既存 `GN` ベース補題を、
     `GTail_one_eq_sum` を使って破壊なく通す。
   - 必要なら `GTail` 側に
     `r = 1` specialized decomposition を追加し、
     `GN` 側の移行コストをさらに下げる。

### 日時: 2026/03/26 16:02 JST

1. 目的:
   - `CosmicFormulaBinom.lean` に `GTail` を取り込み、
     既存 `GN` を general tail family の `r = 1` wrapper へ置き換える。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     に `import DkMath.CosmicFormula.GTail` を追加した。
   - `GN` を
     `@[simp] abbrev GN ... := DkMath.CosmicFormula.GTail d 1 x u`
     へ置き換えた。
   - `cosmic_id_csr` / `cosmic_id_csr'` は、
     旧来の二項展開の手書き証明をやめ、
     `GTail` の主恒等式
     `add_pow_eq_prefix_add_xpow_mul_GTail`
     を `r = 1` で使う形へ整理した。

3. 結論:
   - 本線 `GN` は、
     既に general tail family の thin wrapper として再配置された。
   - これにより今後の `GN` 系補題は、
     必要に応じて
     `GTail`
     または
     `GTail_one_eq_sum`
     を介して整理できる状態になった。
   - `CosmicFormulaBinom` 側の重複していた二項展開 spine も、
     少なくとも主恒等式については下層 API へ寄せられた。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.NumberTheory.Gcd.GN`
   を実行し、ビルド成功を確認した。

5. 備考:
   - この段階では downstream の API 名は変えていない。
   - したがって既存 import / 参照側は、
     `GN` をそのまま使いつつ内部だけ `GTail` family へ接続された状態である。

6. 次の課題:
   - `CosmicFormulaBinom` 内の `GN` 補題群を、
     必要に応じて `GTail_one_eq_sum` や
     `GTail` の generic 補題へ寄せていく。
   - `BigN` / `BodyN` / `GapN` のうち、
     tail family に自然に吸収できるものを再点検する。
   - 次段で `Defs.lean` の `Gn` をどう整理するかを判断する。

### 日時: 2026/03/26 16:20 JST

1. 目的:
   - `GN := GTail d 1 x u` への差し替え後に
     full build で出た downstream 障害が、
     rollback を要する種類か、
     それとも compatibility shim で吸収できる種類かを調べる。

2. 観測された障害:
   - `CoreBeamGap.lean` では、
     `unfold GN; rw [Finset.mul_sum]`
     のような「旧和形を直接仮定した rewrite」が
     `GTail` 本体に対して失敗した。
   - `CosmicDerivativePower.lean` では、
     `GN` の swap 互換証明が
     `GTail` 展開後の指数正規化で止まった。
   - `FLT/Core.lean` では、
     `x = 0` のときの `GN` 先頭項化を
     `Finset.sum_range_succ'` で直接書いていたため、
     `GTail` 化後の形と噛み合わなくなった。

3. 実施:
   - `[CosmicFormulaBinom.lean]` に
     `GN_eq_sum`
     を追加し、
     legacy `GN` の explicit sum shape へ戻す互換 bridge を置いた。
   - `[CoreBeamGap.lean]` は
     `rw [GN_eq_sum]`
     を経由して旧証明 spine を維持した。
   - `[CosmicDerivativePower.lean]` は
     `GN_eq_sum`
     を使う形へ切り替えた。
   - `[FLT/Core.lean]` の
     `GN_eq_head_of_x_eq_zero`
     は、
     旧 `Finset` 直接処理をやめ、
     `GTail_eval_zero`
     を使う薄い橋へ整理した。

4. 調査結論:
   - 今回の変更は
     「影響範囲が大きくて rollback が必要」
     というより、
     「旧和形依存を吸収する互換層が 1 枚必要」
     という種類の変更だった。
   - したがって方針は
     rollback ではなく
     `GTail` 本体
     → `GN_eq_sum` の compatibility shim
     → downstream 段階移行
     の 3 層で進めるのが自然である。

5. 検証:
   - `lake build DkMath.CosmicFormula.CoreBeamGap`
   - `lake build DkMath.CosmicFormula.CosmicDerivativePower`
   - `lake build DkMath.FLT.Core`
   - `./lean-build.sh`
   を実行し、full build 成功を確認した。

6. 次の課題:
   - `unfold GN` に依存する downstream 箇所を、
     機械的に `GN_eq_sum` / `GTail_eval_zero` / `GTail` generic 補題
     へ寄せられるか、順次棚卸しする。
   - 互換層として
     `GN_eq_sum`
     以外に有用な bridge
     （例えば `GN_eq_head_of_zero` の generic 版）
     を `CosmicFormulaBinom` に置くべきか検討する。

### 日時: 2026/03/26 16:29 JST

1. 目的:
   - full build は通っても、
     単体 target build
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     が落ちる事象の原因を切り分ける。

2. 事実確認:
   - 失敗原因は import chain の欠落ではなかった。
   - `TriominoCosmicBranchA.lean` 内で
     local let `N := GN p u y`
     を `unfold` した際、
     `GN` が `GTail` 本体へ降り、
     旧 explicit sum 形を期待した `sum_erase_add` の後続 `simpa`
     が噛み合わなくなっていた。

3. 実施:
   - `[TriominoCosmicBranchA.lean]` の該当箇所で、
     `unfold N`
     の直後に
     `rw [GN_eq_sum]`
     を入れ、
     `GN` を legacy sum shape に戻してから
     `A / B / u` を展開する順へ修正した。

4. 結論:
   - 単体 target build の failure も、
     本質的には import chain 問題ではなく
     `GN -> GTail` refactor 後の reduction 順序の問題だった。
   - したがって段階移行の基本方針は変わらず、
     `GN_eq_sum`
     を「局所 let 展開の直後に当てる」
     という実装規約を足せば吸収できる。

5. 検証:
   - `./lean-build.sh DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     を実行し、ビルド成功を確認した
     （既存の `sorry` warning は継続）。

6. 次の課題:
   - `let N := GN ...` 型の局所略記を持つ downstream コードで、
     `unfold N` の後に和形を仮定している箇所がないかを点検する。
   - 必要なら
     `GN_eq_sum`
     の利用パターンを
     小さな refactor guideline として残す。

### 日時: 2026/03/26 21:36

突き合わせ結果は、かなり良いです。文書の主張のうち、**定義・基本恒等式・主要 special case は実装済み**で、**Beam 解釈や可除性の独立補題化はまだ薄い**、という状況です。

**対応済み**

- §2 一般化定義  
  [GTail.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L19) の `GTail` が文書の `GN_d^(r)` に対応しています。添字の書き方だけ違い、内容は
  `sum_{j=r}^d ... x^(j-r) u^(d-j)` を `k = j-r` に直した形です。
- §3 Tail 分解  
  [add_pow_eq_prefix_add_xpow_mul_GTail](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L30) がそのまま対応しています。
- §4.1 `r = 0`  
  [GTail_zero_eq_add_pow](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L87)
- §4.2 `r = 1` 標準 GN  
  [GTail_one_eq_sum](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L139) と、[CosmicFormulaBinom.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L266) の `abbrev GN := GTail d 1 x u`、さらに [GN_eq_sum](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L275)
- §4.3 `r = d`  
  [GTail_self_eq_one](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L95)
- §5 再帰  
  [GTail_rec](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L107)
- §8 評価点  
  [GTail_eval_zero](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L154)

**部分実装**

- §1 背景の `(x+u)^d - u^d = x * GN_d(x,u)`  
  これは [cosmic_id_csr'](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L304) と [add_pow_gap_factor](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean#L318) で維持されています。しかも今は `GTail` 主定理ベースに寄っています。
- §9 まとめの「可除性・p進付値・原始素因子解析への応用」  
  これは実際に下流で使い始めていますが、`GTail` 名義の generic API としてはまだ薄いです。現状は `GN` wrapper を通じた利用が中心です。

**まだ薄い / 未整理**

- §6 最小次数と可除性  
  数学的には [add_pow_eq_prefix_add_xpow_mul_GTail](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean#L30) から読めますが、
  「`x^r ∣ ...`」を standalone lemma としてはまだ切っていません。
- §7 Beam 解釈  
  文書上の意味づけは合っていますが、Lean ではまだ comments / 命名方針の段階です。`GTail` を Beam family の canonical API として整理し切ったところまでは行っていません。
- `Defs.lean` の `Gn` 整理  
  まだ未着手です。履歴どおり保留中です。

**見立て**

- 文書のコア数式部分は、もう実装済みと言ってよいです。
- 未完は「generic tool lemma の磨き込み」と「古い `Defs.Gn` / Beam 語彙との統合」です。
- 次に自然なのは 2 つです。
  - `x^r ∣ ...` の standalone 補題を `GTail` 側に足す
  - `Defs.lean` の `Gn` を `GTail` family へどう接続するか決める

要するに、**設計書の第2〜5節・第8節は実装済み、第6・7・9節は意味論と補題 API の整備が残っている**、という評価です。

### 日時: 2026/03/26 21:44

突き合わせると、`GTail` 文書のコアはかなり実装済みですが、`Defs` への定義集約はまだ未着手です。しかも `Defs` は今のままでは、そのまま canonical 置き場にするには少し危ないです。

現状の整理はこうです。

- [GTail.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/GTail.lean)  
  文書の `GN_d^(r)` 本体です。定義、tail 分解、`r=0/1/d`、再帰、`x=0` 評価まであります。
- [CosmicFormulaBinom.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean)  
  ここで `GN := GTail d 1 x u` の wrapper 化が済んでいます。
- [Defs.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/Defs.lean)  
  ここには今も古い `G` / `Gn` / `Big` / `Body` / `Gap` がありますが、意味が mainline と揃っていません。

特に問題なのは `Defs` 側です。

- `Gn` は実際ほぼ使われていません。
- しかし `G` は使われています。主に [KUS/CosmicBridge.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/KUS/CosmicBridge.lean) が依存しています。
- しかも `Defs.G` は今の意味では「将来の `GZ` に近いもの」で、mainline `GN` とは別物です。
- `Defs.Big` / `Defs.Body` / `Defs.Gap` は `ℝ` 固定で、mainline の generic 定義ともずれています。

なので、結論はこれです。

1. `Defs` を最終的な固定点にする方針自体は妥当  
2. ただし今すぐ「散らばった def を全部 Defs へ移す」のは危険  
3. 先に `Defs` を canonical-definition file に作り替える段階が必要

安全な移行順はこうです。

1. [Defs.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/Defs.lean) に新 canonical 名を追加する  
   - `GN`
   - `GZ`
   - 将来の `GC` 用 placeholder
   - ここで `GN := GTail d 1 x u` に寄せる
2. 既存の `Defs.G` はすぐ消さず、`GZ` へ意味を明記して残す
3. [CosmicFormulaBinom.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean) は Defs を import する側へ変える
4. その後に downstream を `Defs.GN` / `Defs.GZ` へ段階移行する
5. 最後に旧 `Gn` を alias か廃止候補へ落とす

import chain の観点では、`Defs` は定義だけの薄い層にできるので、そこへ `GTail` を入れて [CosmicFormulaBinom.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean) が `Defs` を参照する形は作れます。逆向きに `Defs -> Binom` にすると循環しやすいので、それは避けるべきです。

要するに、

- `Gn -> GN`
- `G -> GZ`
- `GC` 新設

という最終図は良いです。  
ただし次の実装作業は「移設」そのものではなく、まず **`Defs` を新 canonical API の受け皿に改造する** ことです。

必要なら次に、その Phase 1 として
[Defs.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/Defs.lean)
へ `GN` / `GZ` の新定義を追加し、`CosmicFormulaBinom` をそれに寄せる最小 patch を切ります。

### 日時: 2026/03/26 22:03 JST

1. 目的:
   - `Defs.lean` を
     `GN / GZ / 将来の GC`
     を受ける canonical definition layer へ寄せる。
   - 未使用の `Gn` を廃止し、
     `GN` 本線を `Defs` 経由で参照する import chain を確立する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/Defs.lean]`
     に
     - `def GZ`
     - legacy alias `abbrev G := GZ`
     - `@[simp] abbrev GN := GTail d 1 x u`
     を追加した。
   - 旧 `Gn` 定義は削除した。
   - `Body` は `GZ` を参照する形へ揃えた。
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     は `GTail` 直 import をやめ、
     `Defs` を import して
     `GN` を `DkMath.CosmicFormula.GN` の wrapper に置き換えた。
   - fallout 修正として
     `[lean/dk_math/DkMath/KUS/CosmicBridge.lean]`
     の `G_one_one_eq` / `body_one_one`
     を `GZ` ベースへ更新した。
   - namespace shadowing 修正として
     `[lean/dk_math/DkMath/CosmicFormula/CosmicTheorems.lean]`
     の `GN` 参照を
     `DkMath.CosmicFormulaBinom.GN`
     明示に直した。

3. 結論:
   - import chain は
     `GTail -> Defs -> CosmicFormulaBinom`
     に整理できた。
   - `Gn` はワークスペース上から消え、
     canonical 名は
     `Defs.GN` / `Defs.GZ`
     に寄った。
   - 既存下流は
     `CosmicFormulaBinom.GN`
     を通じて従来どおり利用できるため、
     段階移行の足場として十分に安定している。

4. 検証:
   - `lake build DkMath.CosmicFormula.Defs`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.KUS.CosmicBridge`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   - `lake build DkMath`
   を実行し、成功を確認した。

5. 備考:
   - 途中で `KUS.CosmicBridge` は
     `G` の展開形に依存して落ちたが、
     `GZ` 明示化で吸収できた。
   - `CosmicTheorems` は
     `DkMath.CosmicFormula.GN`
     と
     `DkMath.CosmicFormulaBinom.GN`
     の shadowing で落ちたため、
     Binom 側を明示参照する方針にした。
   - migration marker として
     `[GNZC]`
     タグを docstring / line comment に導入した。
     以後、
     canonical 定義点・legacy alias・shadowing 回避点には
     このタグを刺して検索可能にする。
   - full build の warning は既存の `sorry` に限られ、
     今回の refactor で新たな warning は増やしていない。

6. 次の課題:
   - `Defs.G` を参照している downstream を、
     コメント・docstring も含めて
     `GZ` へ段階移行する。
   - `CosmicFormulaBinom` / `CoreBeamGap` /
     `CosmicDifference` 周辺で、
     `GN` と `GZ` の役割分担を補題名でも揃える。
   - 将来の `GC` をどの層に置くか
     (`Defs` 直下か別ファイルか)
     を次段で決める。

---

## 6. 次にやるとよい順番

わっちなら、次はこの順で進める。

### 6.1. `[GNZC]` grep で棚卸し

まずタグを入れた効用を回収する。
`[GNZC]` を grep して、箇所を

- canonical point
- legacy point
- shadowing point
- theorem-name-stable point

に分類するのじゃ。

### 6.2. `G` 実使用箇所の置換候補を洗う

コメントだけでなく、実際に

- `unfold G`
- `simp [G]`
- theorem statements with `G`
  を拾って、`GZ` へ移せるものと、まだ残すものを分ける。

### 6.3. `GN` 参照先の一本化方針を決める

新規コードは `Defs.GN` を使う、旧コードは wrapper 許容、のように方針を固定するとぶれにくい。

### 6.4. `GC` の最小 skeleton を 1 個だけ置く

実装を広げる前に、たとえば定義名とコメントだけでも置く。
それで「三本柱の場所」が確定する。

### 日時: 2026/03/26 22:15 JST

1. 目的:
   - `[GNZC]` タグの効用を回収し、
     migration 対象を
     canonical / legacy / shadowing / theorem-name-stable
     に棚卸しする。
   - `G` の実使用箇所を洗い、
     すぐ `GZ` へ移せるものと
     当面残すものを切り分ける。
   - `GC` の最小 skeleton を先に置き、
     `GN / GZ / GC` の三本柱の場所だけ確定する。

2. 実施:
   - `[GNZC]` grep を行い、
     現状の分類を次のように整理した。
     - canonical point:
       `Defs.GZ`, `Defs.GN`
     - legacy point:
       `Defs.G`, `CosmicFormulaBinom.CommRing.G`,
       `CosmicFormulaBinom.GN` wrapper,
       `KUS.CosmicBridge` 冒頭説明
     - shadowing point:
       `CosmicTheorems.cid_csr_iff'`
     - theorem-name-stable point:
       `KUS.CosmicBridge.G_one_one_eq`
   - `G` 実使用の grep を行い、
     次の切り分けを得た。
     - `GZ` へ寄せやすい:
       `KUS/CosmicBridge.lean` の comment / theorem wording
     - 当面残す:
       `CosmicFormulaBinom.lean` の `CommRing.G`,
       `CosmicFormulaDim.lean`,
       `CosmicFormulaCellDim.lean`
       （独立 family / 幾何和 family としてまだ意味差がある）
     - 対象外:
       `SilverRatioCircle.lean` など、
       Cosmic naming と無関係な局所記号 `G`
   - `[lean/dk_math/DkMath/CosmicFormula/Defs.lean]`
     に
     `@[simp] abbrev GC (z u : ℂ) (d : ℕ) : ℂ := GZ ℂ z u d`
     を追加した。
   - `GC` には
     `[GNZC]`
     docstring を付け、
     「今は complex specialization だが、
      後で意味を独立させても名前は維持する」
     ことを明記した。

3. 結論:
   - `[GNZC]` タグだけで、
     「どこが canonical で、
      どこが legacy で、
      どこが namespace collision 回避か」
     を追える状態になった。
   - `GN` 参照先の一本化方針は、
     - 新規コード:
       `Defs.GN`
     - 旧コード:
       `CosmicFormulaBinom.GN` wrapper 許容
     として固定するのが自然だと確認した。
   - `GC` も `Defs` に席を持ったため、
     三本柱の配置だけは先に安定した。

4. 検証:
   - `lake build DkMath.CosmicFormula.Defs`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   - `lake build DkMath.KUS.CosmicBridge`
   を実行し、成功を確認した。

5. 備考:
   - 今回の `GC` は semantics 完成版ではなく、
     まず public name と placement を固定するための
     skeleton である。
   - `CommRing.G` / `CosmicFormulaDim.G` /
     `CosmicFormulaCellDim.G`
     は同名でも直ちに統合すべき段階ではない。
     先に comment / theorem naming を整理してから、
     本当に `GZ` へ寄せるかを決めるべきと判断した。

6. 次の課題:
   - `KUS/CosmicBridge.lean` の theorem 名と説明文を、
     `GZ` 中心語彙へさらに寄せる。
   - `CosmicFormulaBinom.CommRing.G` を
     alias 化できるか、
     それとも独立 family として残すべきかを検討する。
   - `CosmicFormulaDim.G` / `CosmicFormulaCellDim.G`
     を
     `GNZC` 範囲外の別 family として明示分離するかを決める。

### 日時: 2026/03/26 22:22 JST

1. 目的:
   - `KUS/CosmicBridge.lean` の語彙を、
     theorem 名は壊さずに `GZ` 中心へ一段寄せる。

2. 実施:
   - `cosmicTerm` の docstring を
     `CosmicFormula.GZ`
     基準へ更新した。
   - `cosmicBodyCoeffSum` の説明文も
     `Body = GZ`
     の wording に直した。
   - `G_one_one_eq` は残しつつ、
     canonical-name alias
     `GZ_one_one_eq`
     を追加した。
   - `body_one_one` の docstring も
     `GZ` 中心の表現へ修正した。

3. 結論:
   - `KUS/CosmicBridge` では、
     theorem-name stability を保ったまま
     説明文・新入口だけを `GZ` 側へ寄せる形が取れた。
   - 以後の downstream 移行では、
     新規参照は `GZ_one_one_eq`
     を使い、
     旧名 `G_one_one_eq`
     は compatibility name として維持できる。

4. 検証:
   - `lake build DkMath.KUS.CosmicBridge`
   - `lake build DkMath.CosmicFormula.Defs`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   を実行し、成功を確認した。

5. 次の課題:
   - `KUS/CosmicBridge` 内の残る
     `G`
     wording を、必要に応じて alias 注記付きでさらに整理する。
   - `CosmicFormulaBinom.CommRing.G`
     について、
     `Defs.GZ` とどこまで theorem alias 化できるかを検討する。

### 日時: 2026/03/26 22:29 JST

1. 目的:
   - `CosmicFormulaBinom.CommRing.G` が
     `Defs.GZ`
     に直 alias できるかどうかを、
     橋定理として明示化する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     に
     - `mul_G_eq_GZ`
     - `Body_eq_GZ`
     を追加した。
   - どちらにも
     `[GNZC]`
     docstring を付け、
     `CommRing.G` は pre-normalized kernel、
     `Defs.GZ` は Body-normalized kernel
     だと明記した。

3. 結論:
   - `CommRing.G` は
     `Defs.GZ`
     と同一名に畳むべき対象ではなく、
     `x * G = GZ`
     という橋で接続される独立 family と整理するのが正しい。
   - したがって今後の移行方針は
     - Body-normalized を使う新規コード:
       `GZ` / `Body_eq_GZ`
     - pre-normalized を明示的に使う旧コード:
       `G`
     で分岐させるのが自然になった。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   を実行し、成功を確認した。

5. 次の課題:
   - `big_is_body_and_gap` / `cosmic_id` 系の docstring を、
     必要なら
     `Body_eq_GZ`
     を参照する wording へ寄せる。
   - `CosmicFormulaDim.G` / `CosmicFormulaCellDim.G`
     が本当に
     `GNZC`
     範囲外の別 family かどうか、
     bridge 補題の有無を含めて次段で判定する。

### 日時: 2026/03/27 00:03 JST

1. 目的:
   - `CosmicFormulaBinom` の `cosmic_id` 系説明文を
     `Body_eq_GZ`
     ベースの canonical wording に寄せる。
   - `CosmicFormulaDim.G` / `CosmicFormulaCellDim.G`
     が現段階で `GNZC` 範囲外の別 family だと
     コード上でも明示する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     の
     - `big_is_body_and_gap`
     - `cosmic_id`
     - `cosmic_formula_binom`
     - `cosmic_id'`
     の docstring に
     `Body_eq_GZ`
     ベースの `[GNZC]` 注記を追加した。
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean]`
     の冒頭 section comment に、
     この `G` は解析・幾何寄りの別 family であり、
     直ちに `Defs.GZ` 移行対象ではないと注記した。
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaCellDim.lean]`
     の `G` 定義にも、
     幾何級数 / cell-counting family であり
     `GNZC` 範囲外だが
     bridge 補題は今後整理対象である、
     という注記を追加した。

3. 結論:
   - `CommRing.G` については
     `x * G = GZ`
     の橋でつながる一方、
     `CosmicFormulaDim.G` と `CosmicFormulaCellDim.G`
     は現時点では別 family と見るのが自然だと整理できた。
   - したがって次段の refactor は、
     まず `Binom` 側 canonical wording を進め、
     `Dim` / `CellDim` は bridge 補題の有無を見て
     後で接続する方針が妥当である。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   - `lake build DkMath.CosmicFormula.CosmicFormulaDim`
   - `lake build DkMath.CosmicFormula.CosmicFormulaCellDim`
   を実行して確認する。

5. 次の課題:
   - `CosmicFormulaCellDim` に既にある
     `Gbinom`
     との橋を再点検し、
     `GNZC` から見た接続点を整理する。
   - `CosmicFormulaDim.G`
     にも canonical family との橋が必要か、
     あるいは完全に別 namespace 方針にすべきかを決める。

### 日時: 2026/03/27 00:11 JST

1. 目的:
   - `CosmicFormulaDim.G` と
     `CosmicFormulaCellDim.G`
     の同名衝突を避けるため、
     別 family であることが名前でも分かるようにする。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean]`
     の定義名を
     `GReal`
     へ変更し、
     file 内の `cosmic_id` 説明・本体参照も追従させた。
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaCellDim.lean]`
     の定義名を
     `GCell`
     へ変更し、
     file 内の
     - `pow_sub_pow_eq_mul_G`
     - `card_Body_eq_mul_G`
     - `mul_G_eq_mul_Gbinom`
     - `G_eq_Gbinom_of_pos`
     - `G_two_dim_eval`
     - slab/card chain
     - paper-chain comment
     を追従させた。
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
     の
     `dim_G_iff`
     は
     `DkMath.CosmicFormulaDim.GReal`
     を参照するように更新した。

3. 結論:
   - canonical family
     `Defs.GN / Defs.GZ / Defs.GC`
     と、
     analytic family `GReal`、
     cell-counting family `GCell`
     が名前の上でも分離された。
   - これで `G` という短名は、
     少なくとも `Dim` / `CellDim`
     では今後新しい衝突源になりにくくなった。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   - `lake build DkMath.CosmicFormula.CosmicFormulaDim`
   - `lake build DkMath.CosmicFormula.CosmicFormulaCellDim`
   を実行して確認する。

5. 次の課題:
   - `CosmicFormulaCellDim` の theorem 名
     `pow_sub_pow_eq_mul_G` などは、
     互換を残すか
     `..._GCell`
     へ改名するかを次段で決める。
   - `ZsigmondyCyclotomic` などの comment 中に残る
     `G d x u`
     表記を、
     canonical / pre-normalized / cell-counting
     のどれかへ分類して整理する。

### 日時: 2026/03/27 00:18 JST

1. 目的:
   - `CosmicFormulaCellDim.Gbinom` が
     canonical family のどこに位置するかを、
     橋補題として明示化する。

2. 実施:
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaCellDim.lean]`
     に
     - `Gbinom_eq_GN`
     - `x_mul_Gbinom_eq_GZ`
     を追加した。
   - `Gbinom_eq_GN` では
     `CosmicFormulaBinom.GN_eq_sum`
     を用いて、
     `Gbinom`
     が canonical `GN`
     と同一であることを明示した。
   - `x_mul_Gbinom_eq_GZ` では、
     `CellDim` 側の binomial kernel から
     `Defs.GZ`
     への Body-normalized bridge を置いた。

3. 結論:
   - `Gbinom` は「ほぼ GN」ではなく、
     code 上でも
     `Gbinom = GN`
     と確定した。
   - さらに
     `x * Gbinom = GZ`
     が揃ったため、
     `CellDim`
     の binomial branch は canonical family に完全接続された。
   - したがって
     `CellDim`
     に残る固有名詞の意味差は、
     もはや `Gbinom`
     ではなく
     `GCell`
     との対比だけである。

4. 検証:
   - `lake build DkMath.CosmicFormula.CosmicFormulaCellDim`
   - `lake build DkMath.CosmicFormula.CosmicFormulaBinom`
   - `lake build DkMath.CosmicFormula.CosmicTheorems`
   を実行し、成功を確認した。

5. 次の課題:
   - `CellDim` 内で
     `Gbinom`
     を名前として残すべきか、
     `GN` alias へ寄せるべきかを検討する。
   - `ZsigmondyCyclotomic` などの文章中の
     `G d x u`
     記法を、
     `GN / GZ / GCell / GReal`
     のどれかへ分類して直す。
