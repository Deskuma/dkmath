# Gate 001 — source-indexed bridge matrix

2026-10-15 JST。対象 HEAD: `451394c336fc7547f192acb70fd2b4f5e3ddcf5a`。
総合 **B（部分整合）**。production Lean の変更・外部完成定理の import は行っていない。

## 読み方と出典

ローカルのパスは Lean project root `lean/dk_math/` からの相対パス。
以下の短縮名は **ファイル名の省略**であり、宣言の namespace ではない。

| 記号 | ファイル |
|---|---|
| Up | [P2M/Sol/S_flt_regular.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_flt_regular.lean) |
| US | [P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean) |
| UF | [P2M/Sol/S_fermatLastTheoremSeven.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_fermatLastTheoremSeven.lean) |
| CP | `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean` |
| CG | `DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean` |
| IP | `DkMath/Lib/NumberTheory/IdealPowerFactor.lean` |
| PP | `DkMath/Lib/NumberTheory/PrincipalIdealPower.lean` |
| SP | `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean` |
| DP | `DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicDegreeSixPID.lean` |
| UC | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean` |
| CT | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicChosenTail.lean` |
| RP | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean` |
| CM | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean` |
| CE | `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMUnitPhase.lean` |
| PR | `DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean` |
| PB | `DkMath/FLT/Seven/PrimeTraceOneCyclotomicPidBypassAudit.lean` |
| RC | `DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean` |

Up は [固定版](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_flt_regular.lean)。

### Erratum 002 — canonical source pointers（2026-10-15）

Gate 001 の比較に使った temporary copies は Git-tracked の恒久入力ではない。
本表の参照を固定 upstream commit の path:line に統一した。
`evidence/001-reference-copy-diff.txt` は当時の比較記録として保存するが、
そこに記録された copy の存在や再取得をこの文書の入力条件にしない。
元の Outcome B、型検査・axiom 検査・build 結果は変更していない。
以下の `Up:3247` は上表の固定 URL `P2M/Sol/S_flt_regular.lean#L3247` を表す。
DkMath 側の行番号・定理状態は Gate 001 の冒頭 HEAD における source index。
Gate 002 で証明された一般単数補題 G1–G3 の現在の状態は [report-002.md](report-002.md) を参照。

upstream の短名 `FltRegular.*` は原則 `P2MW.S_flt_regular.FltRegular.*`。
`IsRegularPrime` は `P2MW.S_flt_regular.IsRegularPrime`。
`section` は namespace を作らないため、案内文の名前をそのまま完全修飾名とは扱わない。
具体的には `FltIdeals`（Up:323）、後半の `KummersLemma`（Up:3212）は section。
`CaseI` namespace も Up:1134 で閉じている。従って実際の宣言名は
`P2MW.S_flt_regular.FltRegular.fltIdeals_coprime`、
`P2MW.S_flt_regular.FltRegular.is_principal`、
`P2MW.S_flt_regular.FltRegular.exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`、
`P2MW.S_flt_regular.FltRegular.eq_pow_prime_of_unit_of_congruent` になる（S）。
案内文の `FltIdeals.fltIdeals_coprime` / `CaseI.is_principal` /
`KummersLemma.eq_pow_prime_of_unit_of_congruent` は概念的ラベルとして読む。

検証区分 **K** = live checkout の型・`#print axioms` を確認、**S** = ソース読解のみ。
upstream は全て S。upstream 全体の再ビルド・kernel audit は実行していない。
ローカル49宣言の完全修飾名・展開前の型・axiom sets は
`evidence/001-type-axiom-probe.txt` と opt-in
`DkMathTest/FLT/Seven/KummerAnthropicBridgeAudit001.lean` にある。
Prop 定義への `#print axioms` は、その Prop の証明を与えるものではない。

## 番号付き行列

| # / 優先 | Anthropic の正確な境界・出典 | DkMath の境界・出典 | 整合性 / 仮定差 / restricted packet / 最小次手 |
|---|---|---|---|
| 01 P0 | `IsRegularNumber n := n.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField n ℚ))))`、`IsRegularPrime p := IsRegularNumber p`。Up:48–52 | `DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt R p := ∀ a : ClassGroup R, a^p=1 → a=1`、IP:25。CG:47 `classGroupPTorsionFreeAt_of_coprime_card` | **specializable, K/S, B**。upstream regularity は固定した円分環と指数。局所 class-group torsion-free への変換は既存。逆同値を今回新証明していない。p=7 の PID 入力があり新 lemma 不要。 |
| 02 P0 | `P2MW.S_flt_regular.isPrincipal_of_isPrincipal_pow_of_coprime`：Dedekind domain、finite class group、`Coprime p card`、`(I^p).IsPrincipal → I.IsPrincipal`。Up:54–70 | `DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt`、IP:54。`classGroupPTorsionFreeAt_of_coprime_card`、CG:47 | **specializable, K/S**。local API は `I ∈ (Ideal R)⁰` を明示し upstream は `I=0` を別処理する。非零 ideal で同じ作用。単数吸収は結論に含まない。新 principalization lemma 不要。 |
| 03 P0 | `P2MW.S_IsCyclotomicExtension_Rat_seven_pid.SevenPidPort.seven_pid (K)`：`[Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K] → IsPrincipalIdealRing (𝓞 K)`。US:58、wrapper US:81 | `DkMath.FLT.Seven.CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing`、SP:92。`classNumber_eq_one`、SP:158 | **exact endpoint, K/S**。証明方法は両者 Minkowski bound と2,3の residue degree。upstream は floor=4、local は floor≤4 で足りる。PID / class number=1 は既証明。再実装不要。 |
| 04 P0 | 円分整数環上の定理を使う。Up:3247 の `K` と US:58 の `K` | `DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.ringOfIntegersToRing : (𝓞 (CyclotomicField 7 ℚ)) →ₐ[ℤ] Ring`、DP:129。単射 DP:205、全射 DP:161。`ringOfIntegersToRingEquiv`、CE:21。`ringIsPrincipalIdealRing`、DP:234 | **exact carrier equivalence, K/S**。実際の `ℤ`-algebra equivalence がある。生成元の像 DP:150、conjugation coherence CM:101、units equivalence CM:131 もある。norm だけの類推ではない。PID 移送は全射で十分、単射により equivalence も既存。 |
| 05 P0 | `FltRegular.eq_pow_prime_of_unit_of_congruent`：`u : (𝓞 K)ˣ`、`∃ n : ℤ, (p : 𝓞 K) ∣ ((u : 𝓞 K)-n)`、`p≠2`、regularity → `∃ v : (𝓞 K)ˣ, u=v^p`。Up:3247 | `DegreeSixUnitCongruentToRationalModSeven u := ∃ m : ℤ, ¬7∣m ∧ u-(m:Ring)∈sevenIdeal`、UC:136。`DegreeSixKummerUnitLemmaAtSeven`、UC:144 は **def : Prop** | **partial, K/S, B**。local は非零整数 residue を追加要求する。upstream は u が unit であることからその非零性を証明する。modulus は local UC:23 により正確に `(7)`。equivalence による map は整数と7を保つ。local の一般単数 theorem は未発見。下記 G1–G3 が最小候補。 |
| 06 P0 | `FltRegular.exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`：`(ζ.toInteger-1)^p ∣ (u:𝓞 K)-1 → ∃ v : K, v^p=(u:K)`、regularity、p≠2。Up:3221 | `RelativeNormOneScalarUnitAtSeven`、RP:159、および `SevenCyclotomicDegreeSixInt.relativeNormOneScalarUnitAtSeven_unconditional`、CM:350：norm-one unit δ で `δ-1∈(7)` なら δ=1 | **partial / different hypothesis, K/S**。upstream は field の根を返し、後続で integrality と unit 性を回収する。local は相対 norm-one 位相を消す theorem。`(7)=(π^6)` up to unit であり `(π^7)` と同一視しない。一般 Kummer extension / Hilbert94 の同一 theorem は local で未確認。p=7 の一般単数補題には local CM+real-unit log ルートを先に評価する。 |
| 07 P1 | `FltRegular.fltIdeals_coprime`：`p≥5`、`x^p+y^p=z^p`、`IsCoprime x y`、異なる p-th roots η₁,η₂、`¬p∣xyz` → corresponding ideals coprime。Up:502 | `DkMath.FLT.chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack_withoutProduct`、CP:2635。さらに chosen quotient と tail の coprimality、`directCyclotomicPhaseQuotient_one_isCoprime_with_tail`、CT:266 | **partial / specializable, K/S**。CP は chosen factor `z-ζ*y`、`¬p∣z-y` で実施。CT は ramified uniformizer を割った6個の quotient に対する証明。original linear factors 同士の無条件 coprimality ではない。新 coprimality API は不要、orientation と ramifier を保存して使う。 |
| 08 P1 | `FltRegular.exists_ideal`、Up:1212：Case I の `(a+ζb)=I^p`。`FltRegular.is_principal`、Up:1232：regularity を加えて `∃ u : Rˣ, α : R, ↑u*α^p=a+ζb` | `chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin_withoutProduct`、CP:2831。`cyclotomicUnitNormalization_of_firstCase_of_pack_thin_withoutProduct`、CP:3038。PP:82 `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` | **specializable, K/S**。local exact types は probe。ideal seventh power と `a=u*b^7` は既存。PP:100 の exact-power API は **全 unit の p-power surjectivity を仮定**するので、Kummer congruence lemma の代用にはしない。 |
| 09 P1 | Case II `divZetaSubOne`、`exists_ideal_pow_eq_c`、Up:3556,3697：gcd と π を除いた ideal の p-th-power extraction | `directCyclotomicChosenQuotient_ideal_is_seventh_power`、CT:527：`∃ I : Ideal Ring, span {Q}=I^7`。`directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power`、CT:581：`span {L}=ramifiedPrime*I^7` | **partial, K/S; restricted source already constructed**。`r : PrimitiveCounterexampleRamifiedProvenance source` から供給される。local は fixed summit の linear factor と6 quotient を扱う。π=`1-zeta`、upstream π=`zeta-1`、差は unit `-1`。ideal は一致するが element-level 等式では符号を保存。 |
| 10 P0/P1 | Case II `exists_solution'` 内の ε₁/ε₂ の mod-p integer congruence、Up:4016–4031。これを Kummer unit lemma に入力する | `exists_directCyclotomicChosenQuotientPowerPacket`、UC:291。`DirectCyclotomicChosenQuotientPowerPacket.unit_congruentToRationalModSeven`、UC:229。`directRamifiedGapTail_mem_sevenIdeal`、UC:322 | **restricted chosen packet: proved, K/S**。合同は未構成 field ではない。tail の `(7)` divisibility、β^7 の scalarization、β の非零 residue、endpointRight の7非可除性から m を構成。異なる source の ε₁/ε₂ 合同を無条件に得る定理ではない。 |
| 11 P0/P1 | Up:3247 の一般 Kummer unit theorem を Case II に適用 | `SevenCyclotomicDegreeSixInt.DirectCyclotomicChosenQuotientPowerPacket.unit_isSeventhPower_unconditional`、CM:357。`exists_quotient_seventhPower_unconditional`、CM:365。`exists_directLinearFactor_seventhPower_unconditional`、CM:373 | **local restricted theorem は既にさらに具体化済み, K/S**。結論は `Q=γ^7` と `L=ramifiedUniformizer*γ^7`。**L=γ^7 ではない**。packet 引数は残るが UC:291 に constructor、r は PR:323 に constructor がある。両 constructor の axioms を別確認。一般単数補題の証明にはならないが、chosen-factor 消費者にその補題を追加する必要もない。 |
| 12 P2 | `FltRegular.caseI` / `caseII`、Up:4190,4196：`¬p∣abc` / `p∣abc`、後者は nonzero product と primitive gcd、odd prime | `CounterexamplePack`、`DkMath/FLT/Seven/Basic.lean:18`。`PrimitiveSevenDivisibleEndpoint` と theorem、`PrimeTraceOnePrimitiveRamifiedResolution.lean:17,25`。PR:62 の x/y/zCase と PR:323 | **partial branch transport, K/S**。local generic Gap の `q∣z-y` と upstream Case II は同値ではない。p=7 では全 primitive source から unique 7-divisible endpoint を構成済み。符号付き summit は xCase `(z,y,x)`、yCase `(z,x,y)`、zCase `(x,-y,z)`。詳細は後述。既存 orientation constructor を再実装しない。 |
| 13 P3 | `CaseII.exists_solution'`、Up:4011：`x^p+y^p=ε*(π^(m+1)*z)^p`、π∤y,z → `∃ x' y' z' : 𝓞 K, ε' : (𝓞 K)ˣ, π∤y',z' ∧ x'^p+y'^p=ε'*(π^m*z')^p` | `CyclotomicPrincipalizationNonFirstCasePeelNormalFormDescentTarget`、CP:4296：normal form と q conditions → `∃ z':ℕ, z'^p=(x/q)^p+y^p` | **incompatible as a direct adapter, K/S, C for identification**。local は自然数・y固定・x/q固定・away prime q。upstream は全3変数を円分整数に動かし RHS unit を許す enlarged family。m と natural z、または q の exponent の写像は未構成。local signature を満たす根の構成が不足。 |
| 14 P3 | `not_exists_solution`、Up:4084：m≥1 の enlarged family を induction で排除。`one_le_m` が base m=1 を潰す | `cyclotomicPrincipalizationNonFirstCasePeelNamedSmallerCounterexample_of_hzEq`、CP:4454：**hzEq を仮定**して smaller primitive pack と z'<z を証明。existence core、CP:5389–5409 に `sorry` | **partial conditional / missing construction, K/S, B**。小さくなることの検証は完成、実際の z' はない。core → normal-form → exact-error → non-first-case → legacy principalization → `FLTPrimeGe5Target_of_kummerRoute` に sorryAx が到達する。kernel-split route も別依存を含むので probe の結果を参照。新しい仮定 packet でこの不足を隠さない。 |
| 15 P0/spec | upstream regularity は固定円分環の p と class number。Up:48–52 | `CyclotomicClassGroupPTorsionFreeTarget`、CP:4816 は `∀ R, ∀ n : ℕ, ∀ a : ClassGroup R, a^n=1 → a=1`。`IsRegularPrimeReceiver`、`ClassGroupBridge.lean:96` も全 R を量化。`CyclotomicIdealPthPowerTarget`、CP:873 は結論 `True` | **incompatible / vacuous target, K/S, C**。n=0 を代入すると全 ClassGroup R が subsingleton。local p=7 PID はこれを供給しない。Ideal target は ideal や等式を一切返さず無条件に証明可能。両事実は scratch の example で検証。新コードは IP:25 の `classGroupPTorsionFreeAt Ring 7` と `∃ I, span {a}=I^7` を使う。production の修正は本 gate 外。 |
| 16 P1/analogy | Kummer unit theorem は global unit の等式 Up:3247 | `SevenRealCubic.directOrbitCommonPrime_kummer_residue_condition`、RC:432、`directOrbitCommonPrime_kummer_beta_form`、RC:481 | **partial / analogous, K/S**。`t : DirectOrbitSquareRefinementPacket p`、prime ideal P、**residue field 内の14乗根 h14** が入力。結論は residue field の7乗根、後者は β³=2β²+β−1 と z⁷=β(1+β)。global unit seventh power の供給でも terminal contradiction でもない。 |
| 17 endpoint | `flt_regular`、`Theorems/Thm_flt_regular.lean:6` は `Coprime p card`、p≠2 → `FermatLastTheoremFor p`。UF:11 は PID→class number1→これを呼ぶ | `DkMath.FLT.FLTPrimeGe5Target_of_refinedRegularPrimeRoute`、`RegularPrimeRoute.lean:435` 等は複数の未構成 target を引数に取る implication | **partial conditional, K/S, B**。upstream 完成定理は比較 oracle。local の受信口の存在を FLT7 閉鎖と数えない。一般単数補題を閉じても P3 の enlarged-family descent / integer reconstruction は残る。 |

## 正確な主要型

upstream（Up:3214–3249、全修飾 prefix `P2MW.S_flt_regular.FltRegular`）：

```lean
-- Context shared by the two Kummer declarations, source-only here:
variable {K : Type} {p : ℕ} [Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [Fintype (ClassGroup (𝓞 K))]
  (hp : p ≠ 2)
  (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))

-- eq_pow_prime_of_unit_of_congruent:
-- (u : (𝓞 K)ˣ)
-- (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ ((u : 𝓞 K) - (n : 𝓞 K)))
-- : ∃ v : (𝓞 K)ˣ, u = v ^ p
```

local（UC:23,136,144）：

```lean
-- Namespace DkMath.FLT.Seven
-- Ring = SevenCyclotomicDegreeSixInt.Ring
def sevenIdeal : Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.span ({(7 : SevenCyclotomicDegreeSixInt.Ring)} : Set _)

def DegreeSixUnitCongruentToRationalModSeven
    (u : SevenCyclotomicDegreeSixInt.Ring) : Prop :=
  ∃ m : ℤ, ¬ (7 : ℤ) ∣ m ∧
    u - (m : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal

def DegreeSixKummerUnitLemmaAtSeven : Prop :=
  ∀ u : SevenCyclotomicDegreeSixInt.Ringˣ,
    DegreeSixUnitCongruentToRationalModSeven (u : SevenCyclotomicDegreeSixInt.Ring) →
    ∃ v : SevenCyclotomicDegreeSixInt.Ringˣ, u = v ^ 7
```

`sevenIdeal` は定義どおり `(7)`。e=`ringOfIntegersToRingEquiv` による
`Ideal.map e.toRingHom (Ideal.span {(7 : 𝓞 (CyclotomicField 7 ℚ))}) = sevenIdeal`
は map_span と e の natCast 保存で示せる transport contract（この等式自体の新証明は本 gate では追加していない）。
units は `ringOfIntegersUnitsEquiv`、integer casts は ℤ-algebra equivalence で移す。
逆向きの単数合同には `¬7∣m` が必要で、unit と `sevenIdeal≤ramifiedPrime`、
`ramifiedEval` から導く。arbitrary m の非零性を仮定なしに言わない。

## P2：branch と orientation

元の `x^7+y^7=z^7` で `7∣(z-y)` と `7∣x` の対応は mod-7 Frobenius。
既存方向は `CounterexampleRouting.lean:132` と
`PrimeTraceOnePrimitiveRamifiedResolution.lean:86`。前者は gap→x、後者は x→gap。
これは **7に関する対応**であり、arbitrary `q≠7` の `q∣z-y` は Case II の定義ではない。

upstream の plus-factor `a+ζb` と local `L=endpointLeft-ζ*endpointRight` は
`(a,b)=(endpointLeft,-endpointRight)` で整合する。p=7 の符号変換は odd power を使う。
summit の整数等式は `endpointLeft^7-endpointRight^7=distinguished^7`。
従って upstream に入れる triple はそれぞれ `(z,-y,x)`、`(z,-x,y)`、`(x,y,z)`。
元の endpoint と summit の順序を保持する PR:62 の equality fields が根拠。
正値自然数の pack と符号付き整数の triple はそのまま同じ型にはならない。

upstream Case II の一般整数 permutation も Up:4196–4218 に実装済み。
local の generic first-case `¬p∣z-y` は selected x の非可除性であり、
`¬p∣xyz` と同じ条件ではない（y/z が p-divisible な orientation を除外しない）。
この意味でも旧 Kummer branch と upstream cases を名前だけで同一視できない。

## P3：不足は「より小さい解の検証」ではなく「解の構成」

Up:4011 は円分整数 **全3変数**を変え、RHS の unit を次状態に保持する。
Up:4084 はこの状態空間で m の減少を反復する。unit seventh power は途中の
ε₁/ε₂ を吸収し、この反復可能な形へ戻すために用いられる。

CP:4296 は `q≠p`、q∣x,gap、p∣gap、
`gap=p^(p-1)*t^p`、`GN=p*s^p`、`x=p*(t*s)`、三つの coprimality、p∤s、p∣t
から **x/q と y を固定した自然数 z'** を要求する。CP:4320 は q∣t、q∤s を証明済み。
この自然数根を upstream の円分整数解から取り出す写像は見つかっていない。
「norm を取れば z' になる」も、norm の加法非保存のため根拠にならない。

本 audit では m と z の対応、π-valuation と arbitrary away-q peel の対応を提案しない。
今後 upstream 型の下降を採るなら、自然数 pack の復元を毎段要求しない
**円分整数・unit付き方程式の状態空間**を別途設計し、その上の actual next solution を構成する必要がある。
これは G1–G3 より後の数学的作業であり、この gate の実装提案には含めない。

## Gate 002 候補：3補題に限定した native p=7 unit bridge

候補配置：`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`。
import はまず既存 `PrimeTraceOneDirectCyclotomicCMTorsionPhase`。
以下の三つの proposition の型は scratch で確認したが、**証明はまだ追加していない**。
namespace を `DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt`、
`open DkMath.FLT.Seven` として記す。

```lean
-- G1: scalar congruence kills the relative CM phase.
-- theorem unit_eq_starUnit_of_congruent_mod_seven
--     (u : Ringˣ)
--     (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
--     u = starUnit u

-- G2: the norm unit has scalar residue, hence trivial real-unit class.
-- theorem exists_normUnit_seventhPower_of_congruent_mod_seven
--     (u : Ringˣ)
--     (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
--     ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7

-- G3: the full existing Prop specification, now to be inhabited.
-- theorem degreeSixKummerUnitLemmaAtSeven :
--     DegreeSixKummerUnitLemmaAtSeven
```

G1 は RP:111 の packet-specific phase congruence proof を u と h に一般化し、
CM:350 の **既証明** relative-norm-one theorem に適用する。
G2 は `u=m+7*k` から norm≡m² mod 7 を示し、実三次環の thetaLinear/Square の消失を導く。
`SevenRealCubicUnitClass.lean:694` の
`DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero`
で global root を得る。必要なのは finite residue 計算と既存 unit-class theorem。
G3 は RP:183–239 の square/norm と Bézout の議論を一般化する：
`u²=(ofRealUnit v)^7` から `w=(ofRealUnit v)^4*u⁻¹` と置く。
この root は全 unit の surjectivity からでなく **h を使って**構成する。

G1/G2 の private helpers を既存ファイルから無理に参照せず、責務を小さく取り直す。
三補題の proof feasibility は source-grounded な見込みであり、kernel 検証済みの新定理ではない。
Hilbert90–94 の大規模移植を先に仮定する必要はないが、
G2 の congruence→norm coordinates が通るまでは一般補題の完成と呼ばない。

G3 を固定 K の `(𝓞 K)ˣ` へ運ぶ場合、K=`CyclotomicField 7 ℚ`、
e と units equivalence、mod-(7) の上記 transport を用いる。
任意の seventh cyclotomic field K への拡張は別の field equivalence transport を必要とする。
本 Gate 002 の scope は具体的 Ring に限る。

## 依存と信頼性

local chosen path は PR:323 → CT:527 → UC:291 → UC:229 / real norm unit
→ RP の phase reduction → CM:350,357,365,373。
PID は SP と DP、CM は CE の equivalence と Mathlib の CM units/torsion を使う。
選択 packet に対する結論は `sorryAx` なしで確認し、一般 Prop の inhabitation と分ける。

旧 CP:5389 core は直接 `sorry`。legacy consumer への到達を確認する。
一方、CT が CP の ideal factor lemma を import するだけで、CP の全 theorem の
sorry が各宣言に混入するわけではない。`#print axioms` と再帰的 kernel body audit
の結果を `report-001.md` に記す。

upstream の proof body は、Kummer field の unramifiedness（Up:3044）、
Hilbert94 class-number divisibility（Up:2709）、Kummer unit（Up:3221,3247）、
Case II ideal ratios・three-root formula・unit ratio congruence（Up:3448–4038）、
strict induction（Up:4084）を実際に辿った。S に留まり、
外部ライブラリ全体の axiom-free 性を local `#print axioms` の結果から推測しない。
