# Gate 001 report — DkMath × Anthropic Kummer

2026-10-15 JST。**Gate 001 完了 / Outcome B。FLT7 independent closure は OPEN。**

PID・class number=1・具体的次数6環との同型は既存だった。
さらに chosen ramified quotient では整数合同、単数七乗化、`L=π*γ^7` まで既に証明されていた。
今回の新しい整理は、一般単数補題の未実装と、実際に未解決の下降構成を分離したことである。
一般 Kummer unit lemma の具体的 p=7 版を3補題に絞った Gate 002 候補を提示する。
それを閉じても chosen packet の後段の加法的下降は別途必要である。

完全な照合は [bridge-matrix-001.md](bridge-matrix-001.md) の17行。
そこでは各行に exact source、carrier、仮定差、restricted theorem、検証範囲と次手を記載した。

## 1. Baseline と scope

| 項目 | 実測 / 確認結果 |
|---|---|
| cwd | `/home/deskuma/develop/lean/dkmath` |
| Lean project cwd | `/home/deskuma/develop/lean/dkmath/lean/dk_math` |
| branch | `research/FLT7-Kummer-Anthropic-Bridge-261015-v0` |
| HEAD | `451394c336fc7547f192acb70fd2b4f5e3ddcf5a` |
| 最終 commit | `fix: docs: instruction`、author/committer Deskuma、2026-10-15 07:30:36 +0900 |
| 開始時 `git status --short` | 出力なし、clean |
| research branch | ローカルに存在し、既に checkout 済み |
| `lean-toolchain` 全文 | `leanprover/lean4:v4.34.1` |
| nested `lake env lean --version` | Lean 4.34.1、commit `5045d0056413266e57c625dcd7c365b10e377c52` |
| nested `lake --version` | Lake 5.0.0-src+5045d00、Lean 4.34.1 |
| Mathlib inputRev | `v4.34.1` |
| Mathlib manifest / actual checkout | ともに `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| artifacts | 指定4 production targets と Mathlib ClassNumber の `.olean` は存在 |

`lakefile.toml` の **全文**、manifest の Mathlib entry、取得した reference と添付の SHA-256、
commands の exit/stdout は [evidence/001-baseline.json](evidence/001-baseline.json)。
package は `dk_math`、defaultTargets=`DkMath`、testDriver=`DkMathTest`。
Lean libraries は `DkMath`、`DkMathTest`、`DkMathlib`。

最初に repository root で実行した `lake --version` は Lean 4.32.2 を表示した。
これは本プロジェクトの toolchain ではない。build と probe は全て nested cwd で実行し、
上表の 4.34.1 を確認した。

`AGENT.md` と本フォルダの README/ROADMAP/instruction を読み、Gate 001 の
research/source audit の範囲で実施した。production proof は変更していない。
この report で提案する Gate 002 以降の補題は実装済みの成果に含めない。

## 2. 参照版と添付コピーの差

参照 commit は `6e837e75355538c7f80bab5b956861e86c4eacc2`。
添付4ファイルを中心に読み、固定版を読み取り取得して比較した。
最初の sandbox 内 Python fetch は DNS failure、その後の読み取り専用の network 実行は成功。
固定版に `lakefile.toml` はなく、その URL は404、実際の設定は `lakefile.lean`。

| 項目 | 固定 upstream | DkMath |
|---|---|---|
| Lean | 4.33.1 | 4.34.1 |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| package | `flt_e2e`、`lakefile.lean` | `dk_math`、`lakefile.toml` |
| proof namespace | `P2MW.S_flt_regular...` と P2M macros | `DkMath.FLT...` |

`__Util.lean.txt` は固定版 `P2M/Util.lean` と byte-identical。
他3ファイルは一致しない。短い FLT7/PID ファイルは `have`/`let` と `haveI`/`letI` の差。
regular の長いファイルにはこれに加えて API 名変更、simp 引数、1行追加等がある。
例：添付の `nthRootsFinset_pairwise_associated_sub_one_sub_of_prime` に対し固定版は
`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`、
`finrank_modTorsion` / `rank_modTorsion` も異なる。
**添付のビルド済み同一版という扱いはしていない。**

さらに案内文の `KummersLemma` / `FltIdeals` は該当箇所では **section**。
一般単数補題の actual source name は
`P2MW.S_flt_regular.FltRegular.eq_pow_prime_of_unit_of_congruent` であり、
`...FltRegular.KummersLemma.eq_pow_prime_of_unit_of_congruent` ではない。
Case I principalization も `...FltRegular.is_principal`。matrix に対応する完全修飾名を訂正した。
これは source-level の名前解決の確認であり、upstream を typecheck したとの主張ではない。

全差分は [evidence/001-reference-copy-diff.txt](evidence/001-reference-copy-diff.txt)。
元の添付を保持し、重複する取得 proof 本体は比較後に除いた。
固定版の config、generic theorem signature、PROOF-PATH、ATTRIBUTION、NOTICE、LICENSE は evidence に残した。

upstream の
[PROOF-PATH](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md#L28)
は p=7 の Kummer/PID 経路を説明するが、今回の比較判断は該当 proof bodies に基づく。
[ATTRIBUTION §3](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md#3-files-containing-material-from-the-flt-regular-project)
は `S_flt_regular.lean` を flt-regular からの port として記録する。
Apache-2.0、原著者と元ファイル一覧を確認した。今回 proof の移植はしていない。
今後 proof text を適応する場合は、DkMath の MIT header だけに置換せず、
該当 upstream notices と由来を引き継ぐ必要がある。

## 3. 現在の FLT7 frontier

### 3.1 GTail / STOP042

`docs/dev/GTail-SelectiveGap-FLT7-261009-v0/research-decision-042.md` と live owners を確認した。
Row-Z の discriminant −7、`TraceOneInt (-2)` の signed root extraction と
common ramified summit は既証明である。
`PrimeTraceOnePrimitiveRamifiedProvenance.lean:323` は x/y/z の各場合から
actual provenance を構成し、その `#print axioms` に sorryAx はない。

残る frontier は lifted primitive next triple、source-compatible additive identity、
original-coordinate CRT の独立 strict bounds と surviving row contradiction、
global measure / recursive closure。STOP042 を新しい抽出補題の未実装と読み替えない。

### 3.2 旧 Kummer peel

`DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:4296` の normal-form target は
`∃ z' : ℕ, z'^p=(x/q)^p+y^p`。
`:4454` はこの等式を仮定して smaller primitive pack と `z'<z` を示す。
`:5389` の existence core は `hCl` を clear し、`:5409` に直接 `sorry` が残る。
`#print axioms` でも sorryAx を確認した。

### 3.3 degree-six current route / R64

`docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/CURRENT_STATE_FREEZE.md`
は selected factor uniqueness、current/conjugate ownership、exact multiplicity `14*eQ` を
局所終点として保持し、upper cutoff、global oriented aggregation、terminal contradiction を defer している。
live `SevenRealCubicCurrentSelectedFactorUniqueness.lean:758,829` に対応する multiplicity theorem がある。
この historical frontier の全体を今回再ビルドしたとは主張しない。

### 3.4 より新しい Mod42

`docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/report-019.md`、
`source-constraint-frontier-019.md` と actual source/test を確認した。
`SevenRamifiedFusionSourcePrimeValuationLedger.lean:61` は source prime の valuation exclusivity。
`DkMathTest/FLT/Seven/SevenRamifiedFusionSourceConstraintSeparation.lean:72`
は actual complementary seventh root `N>1` を示す **test-only** theorem。
scalar ledger の M=841 model にある N=1 を actual source としては排除するが、
M=841 の全 realization や usable prime の存在を排除・供給しない。

source→natural endpoint reconstruction は未供給。
historical closeout の build 成功は本 gate の新しい実測に転用していない。

## 4. P0 — PID は完成、一般単数補題は仕様、chosen 単数は完成

主な live declarations（prefix は `DkMath.FLT.Seven`）：

- `CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing`：`SevenRamifiedFusionCyclotomicSevenPID.lean:92`。
- `CyclotomicSeven.classNumber_eq_one`：同`:158`。
- `SevenCyclotomicDegreeSixInt.ringOfIntegersToRing`：`SevenRamifiedFusionCyclotomicDegreeSixPID.lean:129`。
- 同写像の全射`:161`、単射`:205`、PID instance`:234`。
- `SevenCyclotomicDegreeSixInt.ringOfIntegersToRingEquiv`：`PrimeTraceOneDirectCyclotomicCMUnitPhase.lean:21`。
- `sevenIdeal := Ideal.span {(7 : Ring)}`：`PrimeTraceOneDirectCyclotomicUnitCongruence.lean:23`。
- `DegreeSixKummerUnitLemmaAtSeven`：同`:144`、**def : Prop**。

upstream の unit lemma は `u : (𝓞 K)ˣ`、`∃ n:ℤ, p∣u-n`、odd prime と
class-number coprimality を仮定し、**unit group 内で** `u=v^p` を返す。
前段の `(ζ-1)^p∣u-1` の lemma は **field K 内の根**を返す。
この二つを区別した。

local の一般単数仕様は非零整数 residue を追加している。
scalar congruence と `(7)` の輸送に障害は見つからない。
ただし actual general theorem の inhabitation は未実装。

chosen packet では `unit_congruentToRationalModSeven`（UC:229）が合同を構成済み。
`exists_directCyclotomicChosenQuotientPowerPacket`（UC:291）が actual ideal root と
generator/unit を構成するため、未構成 field を仮定しているだけではない。
CM:357,365,373 は相対 norm-one phase と実三次 unit class を使い、
chosen unit の七乗、quotient の七乗、ramifier 付き factor の七乗を証明済み。
したがって **chosen packet に一般 Kummer lemma を適用できないことが現行停止理由ではない**。

## 5. P1 — ideal、単数、ramifier を保持する

中立 API は既存：

- `DkMath.Lib.NumberTheory.exists_eq_pow_of_isCoprime_mul_eq_pow`：`IdealPowerFactor.lean:73`。
- `ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt`：同`:54`。
- `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt`：`PrincipalIdealPower.lean:82`。
- `UnitPowerSectorSystem`：`UnitPowerSector.lean:29`、sector を保持した endpoint も同ファイル。

一般に `(a)=I^7` と principalization から得るのは `a=u*b^7`。
exact power を返す `PrincipalIdealPower.lean:100` は全単数の power surjectivity を別途仮定する。
これを Kummer の整数合同制約の代わりに使ってはいけない。

actual chosen quotient では `(Q)=I^7`（CT:527）から packet を作り、
`Q=γ^7`、`L=π*γ^7` に達する。
`π=ramifiedUniformizer=1-zeta`（`SevenRamifiedFusionCyclotomicRamifiedPrime.lean:24`）、
upstream の `π=zeta-1` とは符号が違う。
principal ideals の符号差は消えるが、element 等式・orientation は保存する。
`L=γ^7` と読み替えることはできない。

## 6. P2 — 同じ Case I/II ではない

upstream は `p∣a*b*c` か否か。
旧 DkMath Kummer Gap branch は `q∣x`、`q≠p`、`q∣z-y`。
さらにその first/non-first split は `p∣z-y` か否か。
arbitrary q と p、source axis と全 endpoint の divisibility を混同しない。

p=7 では、mod-7 equation により `7∣x ↔ 7∣z-y` の両方向の既存 theorem があり、
PR:323 の provenance constructor が source に対応する summit を選ぶ。
upstream に入れる plus-form triple は xCase `(z,-y,x)`、yCase `(z,-x,y)`、zCase `(x,y,z)`。
これは formal な sign/permutation 対応だが、upstream が生成する次の円分整数解を
再び正値自然数 source とする構成にはなっていない。

## 7. P3 — 根本的な不足は下降の状態空間と次状態

upstream Case II は `x y z : 𝓞 K` と `ε : (𝓞 K)ˣ` に対し

```text
x^p + y^p = ε * (π^(m+1) * z)^p,  π ∤ y, π ∤ z
    ↓ actual construction
x'^p + y'^p = ε' * (π^m * z')^p,  π ∤ y', π ∤ z'
```

を証明する（添付:4010 / fixed:4011）。ideal ratios から三つの root を選び、
3-factor formula を作り、ε₁/ε₂ の整数合同と Kummer unit lemma で左辺の単数を吸収する。
`one_le_m` と induction による contradiction は添付:4083 / fixed:4084。

local peel は **x/q と y を固定した自然数 z'** を要求する。
upstream の x',y',z' は全て動き、円分整数のままでよい。
したがって unit lemma だけを移せば local peel core が埋まるという対応は成立していない。
自然数への integrality/positivity と literal seventh-power additive equation、
q-peel への同定が不足する。norm は加法を保存しないので、この写像の代用にならない。

upstream の主要なヒントは **下降を閉じる十分広い状態空間を保つこと**にある。
それを採るなら、local 自然数 reconstruction とは別の円分整数・unit付き下降を構成し、
actual next solution と ramifier 指数減少を示す研究が必要。
現在の packet の存在や ideal 等式から、その construction はまだ得られていない。

## 8. C 判定の旧 target と active sorry provenance

`CyclotomicIdealPthPowerTarget`（CP:873）の結論は `True`。
ideal の p乗性を一切表していない。scratch の example は class-group 入力なしにこれを証明した。

`CyclotomicClassGroupPTorsionFreeTarget`（CP:4816）は全 domain・全 n を量化。
n=0 により全 ClassGroup が subsingleton になることを scratch で確認した。
`IsRegularPrimeReceiver`（`ClassGroupBridge.lean:96`）も全 domain を量化する。
具体的 `Ring` の7-torsion-free theorem は、いずれの universal receiver も供給しない。
新しい consumer は固定環・固定指数の `classGroupPTorsionFreeAt Ring 7` を使うべきである。

再帰的に compiled declaration の type/body（opaque を含む）と inductive constructors を調べた結果：

| Root | Reachable constants | direct sorry callers / 結果 |
|---|---:|---|
| `DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute` | 47604 | peel existence core、`primeGe5BranchANormalFormNePCoprimeKernel_default`、`squarefree_implies_padic_val_le_one_research` |
| `DkMath.FLT.FLTPrimeGe5Target_of_kummerRoute_of_kernelSplit` | 47547 | `squarefree_implies_padic_val_le_one_research`。peel core の直接呼出しはないが別 sorry が残る |
| `DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute` | 16314 | sorry caller なし。ただし hCl/hUnit/hNorm 等を入力する conditional theorem |
| `DkMath.FLT.Seven.nonempty_primitiveCounterexampleRamifiedProvenance` | 12798 | sorry caller なし |
| `DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.exists_directLinearFactor_seventhPower_unconditional` | 74756 | sorry caller なし |

direct sorry declarations の actual source：

- peel core：`DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389`、tactic `sorry` は5409。
- `DkMath.FLT.primeGe5BranchANormalFormNePCoprimeKernel_default`：`DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`。
- `DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one_research`：`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`。

従って旧 one-shot route の非信頼部分は peel core だけではない。
一方、import しているという理由だけで clean chosen theorems を sorry-dependent と分類するのも誤り。
五つの recursive audits では missing/unreadable がなく、
finished FLT7 / upstream regular theorem の指定 name filters に該当する dependency はなかった。
この filter は一般的な全完成 FLT 定理の独立性検証を主張するものではない。

## 9. Gate 002 の具体的提案（3補題）

**具体的次数6環の congruence-constrained unit lemma に限定すれば着手可能**。
matrix 末尾に G1–G3 の exact signatures、配置・imports・proof plan を記した。

1. `u≡m mod (7)` から `u=starUnit u`。既存 relative norm-one phase theorem を一般単数に適用する。
2. 同じ合同から `quadraticNormUnit u=v^7`。norm≡m² から theta 非定数座標=0 を示し、既存 real-unit projective log classification を使う。
3. 1と2から `DegreeSixKummerUnitLemmaAtSeven` を証明。u² の七乗性と gcd(2,7)=1 の明示計算で root を構成する。

Gate 002 に whole Hilbert94 port、arbitrary prime、all-unit surjectivity、
旧 universal targets の書換え、下降 core の補完を入れない。
新しい数学的 residual obligation は G2 の scalar congruence→norm coordinates の導出であり、
現時点では typed contract と既存 proof-body の照合による feasible 判定である。
G1–G3 の proof term や kernel acceptance を今回得たとは報告しない。

Gate 003 は既存 chosen packet/constructor と重複する計画を修正すべきである。
Gate 005 は次状態構成が未提示なので実装準備未完了。
一般単数補題の完成を FLT7 の最終不足橋と扱う scope は修正が必要である。

## 10. 実行した検証と結果

cwd は全て `lean/dk_math`（git baseline は repo root）。

| Command / audit | Exit / 結果 |
|---|---|
| `LEAN_NUM_THREADS=1 lake build DkMath.FLT.Kummer.RegularPrimeRoute DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer DkMath.FLT.Seven.PrimeTraceOneCyclotomicPidBypassAudit` | **0**、9175 jobs、既存 artifacts の replay を含む focused build |
| `LEAN_NUM_THREADS=1 lake env lean DkMathTest/FLT/Seven/KummerAnthropicBridgeAudit001.lean` 初回 | **1**、未知 option `pp.width`。宣言名の不明エラーはなかった |
| 同 command 修正後 | **0**。49宣言の #check / #print axioms、vacuity と n=0 example、3候補型、5 dependency traversals |
| `git diff --check` および新規ファイル whitespace / scope audit | 結果は `evidence/001-final-verification.txt` |

compiler 初回失敗と最終成功の raw logs を別々に保存した。
focused build には既存 `sorry` warnings が4箇所あった：ZsigmondyCyclotomicResearch:147、
TriominoCosmicBranchA:4187、GcdNextResearch:850、CyclotomicPrincipalization:5389。
warning の存在はその import graph の事実であり、各 theorem の axiom dependency とは区別した。

49宣言中、sorryAx を持つのは peel core、legacy principalization、legacy FLT route、
kernel-split FLT route の4宣言。他45宣言の axiom leaves は
`propext`、`Classical.choice`、`Quot.sound` の部分集合だった。
この45には Prop の定義も含むため、「45個の新定理を証明した」という意味ではない。
具体的 unit/ideal/class-group/packet の既存 theorem は標準 axioms のみ。

ログ：

- [focused build](evidence/001-focused-build.txt)
- [exact types and recursive audits](evidence/001-type-axiom-probe.txt)
- [compact axiom summary](evidence/001-axiom-summary.txt)
- [initial probe failure](evidence/001-type-axiom-probe-initial.txt)

upstream proof 本体は source-only であり、local toolchain への port/build は未実施。
Mod42 全 suite や DkMath 全体の再ビルドも今回の検証範囲には含めない。

## 11. 成果物と判定

追加したのは本 report、bridge matrix、evidence、opt-in audit probe。
probe は production imports に接続しておらず、その例は既存 target の意味を検査するためのもの。
既存 production proof、添付、README、ROADMAP は変更していない。

| 判定 | 内容 |
|---|---|
| A に相当する既存事実 | PID・同型・固定環の class-group torsion・chosen packet の合同と exact extraction を確認。新しい production bridge の実装成果はない |
| **B / Gate 001 outcome** | source/type/axiom の照合と、3補題に限定した p=7 一般単数 bridge の提案を完了 |
| C | universal class-group receiver、`True` ideal target、Case II と Gap branch の無条件同一視、円分整数下降を自然数 x/q-peel に直結する案 |

**Gate 002 は上記の限定 scope で ready。FLT7 closure に向けた下降は、actual next-state construction が未供給のため OPEN。**
