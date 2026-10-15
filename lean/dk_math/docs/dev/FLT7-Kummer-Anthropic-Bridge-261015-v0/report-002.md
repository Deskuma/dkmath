# Gate 002 — concrete congruent-unit seventh-power bridge

2026-10-15 JST。**G1 / G2 / G3 proved、local Outcome A、review pending。**
既存の `DegreeSixKummerUnitLemmaAtSeven : Prop` を証明する定理を追加した。
入力は一般の `u : Ringˣ` と整数への mod-7 合同であり、chosen packet を仮定しない。
**FLT7 independent closure と実際の下降構成は OPEN。Gate 003 は開始していない。**

## Baseline と変更範囲

- Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`。
- 作業開始 HEAD: `dcf423a4d2a87c92d3ec4ed43ae0c8e228ef4d87`。
- 開始時 `git status --short` は出力なし。既に指定 branch を checkout 済み。
- Lean project cwd: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。
- toolchain: `leanprover/lean4:v4.34.1`。Mathlib checkout は
  `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- build の parallelism 指定は追加していない。

実装は新規 production module 1本、既存 helper の公開化2件、opt-in test 1本。
既存 Prop・合同条件・chosen packet の証明内容は変更していない。
新 module の direct import は
`DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase` の1本。
`DkMath.FLT.Seven` 等の facade、`DkMath.Lib.*`、default root/test driver には配線していない。

以下の source paths は `lean/dk_math/` からの相対パス。

## G1–G3 の exact API と証明状態

source:
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`。
namespace:
`DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt`。

```lean
theorem unit_eq_starUnit_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    u = starUnit u

theorem exists_normUnit_seventhPower_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7

theorem degreeSixKummerUnitLemmaAtSeven :
    DegreeSixKummerUnitLemmaAtSeven
```

| Obligation | Source line | Result | Kernel axioms |
|---|---:|---|---|
| G1 `unit_eq_starUnit_of_congruent_mod_seven` | 30 | proved | propext, Classical.choice, Quot.sound |
| G2 `exists_normUnit_seventhPower_of_congruent_mod_seven` | 53 | proved | propext, Classical.choice, Quot.sound |
| G3 `degreeSixKummerUnitLemmaAtSeven` | 97 | proved; inhabits original Prop | propext, Classical.choice, Quot.sound |

元の仕様は `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean:144`：

```lean
-- namespace DkMath.FLT.Seven
def DegreeSixKummerUnitLemmaAtSeven : Prop :=
  ∀ u : SevenCyclotomicDegreeSixInt.Ringˣ,
    DegreeSixUnitCongruentToRationalModSeven
      (u : SevenCyclotomicDegreeSixInt.Ring) →
    ∃ v : SevenCyclotomicDegreeSixInt.Ringˣ, u = v ^ 7
```

今回はこの仕様そのものを変えず、その proof term を G3 として与えた。
`#check` による Prop の型確認だけでなく、production build と実際の arbitrary-unit consumer が成功した。

## G1 — relative phase を除く

`h` から `u-m∈(7)` を取り出す。
既存の `DkMath.FLT.Seven.star_sub_int_mem_sevenIdeal` を再利用して
`star(u)-m∈(7)`、従って `u-star(u)∈(7)` を得る。
δ=`u / starUnit u` に対して relative norm=1 と δ−1∈(7) を証明し、
既存の
`DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.relativeNormOneScalarUnitAtSeven_unconditional`
（`PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean:350`）を適用する。
δ=1 から `u=starUnit u` を得る。共役不変性を前提として置いていない。

## G2 — 合同から座標、projective log、実三次単数の七乗へ

`Ring` は
`QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)`
（`SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean:30`）。
`quadraticNormUnit` は `Units.map QuadraticAlgebra.norm`
（`PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean:35`）。
これは実三次環への **相対 quadratic norm**。整数への absolute norm とは区別する。

`h` の ideal membership を divisibility に戻して k を取り、`u=m+7*k` と書く。
実三次環内で

```text
c = 2*m*k.re + (alpha-1)*m*k.im + 7*QuadraticAlgebra.norm k
quadraticNormUnit(u) - m^2 = 7*c
```

を証明した（新 module:62–75）。
使用する polynomial norm は
`Mathlib/Algebra/QuadraticAlgebra/Basic.lean:251,256` の
`re² + b*re*im - a*im²` である。
従って、この等式は実三次環の正確な mod-7 integer congruence を与える。

`SevenRealCubicInt` の integer casts と座標射影を展開すると、
`thetaLinearModSeven (quadraticNormUnit u)=0` と
`thetaSquareModSeven (quadraticNormUnit u)=0` が得られる（新 module:76–89）。
これらは `SevenRealCubicUnitClass.lean:56,61` の実際の非定数座標であり、
単なる absolute norm の合同から推測したものではない。

`projectiveLog_apply`（同:208）、`unitNilpotentX/Y`（同:131,136）の式に代入し、
**projective log の両成分=0** を証明した。
最後に
`DkMath.FLT.Seven.SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero`
（同:694）の逆方向を適用する。この既存 theorem は unit-class の
projective-log injectivity と global unit root extraction に基づく。
finite residue enumeration だけで global root を推測する手順は使っていない。

G1/G2 は h の scalar congruence 部分を実際に使用する。
`¬7∣m` は元仕様に保持したままで、今回の証明では別途使用しない。
これは無条件の全単数七乗 surjectivity を導くものではない。

## G3 — square と Bézout の明示計算

G1 と G2 から `u=starUnit u`、`quadraticNormUnit u=v^7` を得る。
既存 helper で `u²=(ofRealUnit v)^7`。
`t=ofRealUnit v` として `w=t^4*u⁻¹` を選び、

```text
w^7 = (t^7)^4 * (u^7)^(-1) = (u^2)^4 * (u^7)^(-1) = u
```

を unit group の等式として証明した（新 module:104–111）。
chosen-factor framework の複製は行っていない。

## 再利用 helper の公開化

`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean` で
private を外し docstring を追加した。proof bodies と statements は保持した。

| Fully qualified identifier | New source line | Role | Axioms |
|---|---:|---|---|
| `DkMath.FLT.Seven.star_sub_int_mem_sevenIdeal` | 73 | star が scalar congruence を保存 | propext, Classical.choice, Quot.sound |
| `DkMath.FLT.Seven.unit_sq_eq_ofReal_normUnit_pow` | 181 | conjugation-fixed unit の square/norm identity | propext, Classical.choice, Quot.sound |

この2件は既存の一般補題のアクセス範囲の変更であり、新しい数学的仮定はない。
G3 の短い group 計算は新 module 内で行い、追加の public helper は作っていない。

## Gate 001 の provenance erratum

`bridge-matrix-001.md` と `report-001.md` に **Erratum 002** を明示した。
temporary comparison copies を本フォルダの Git-tracked な恒久入力として扱う記述を訂正し、
matrix の narrative references を固定 upstream の URL/path:line に統一した。
Gate 001 の baseline HEAD・Outcome B・raw command evidence は変更していない。

canonical comparison theorem は
[P2M/Sol/S_flt_regular.lean:3247–3288](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_flt_regular.lean#L3247-L3288)、
actual source name は
`P2MW.S_flt_regular.FltRegular.eq_pow_prime_of_unit_of_congruent`。
`KummersLemma` は同ファイル:3212 の section 名。
固定 URL をこの gate で再取得し、該当 proof body と context:3214–3217 を読み直した。
SHA-256 は `558d93d519303e12b192f980a8bf3153854508b894ab259e0ec05a0ebe29af43`。
upstream 全体の再ビルド・移植はしていない。

new production proof は既存 DkMath の relative phase / real-unit classification を再利用した。
upstream の Hilbert94/Kummer field proof text は移植していない。
source-reading reference と native implementation の由来を区別する。

## 検証 commands、失敗、結果

すべての build/test は Lean project cwd から実行した。

| Command | Attempt / exit | Evidence / result |
|---|---|---|
| `lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicKummerUnit` | initial / **1** | `evidence/002-build-initial.txt`。unit group の `div_self` rewrite、numeral の座標射影、log の simplification、group product-power 展開の未解決 goal |
| 同 command | second / **1** | `evidence/002-build-second.txt`。norm 差の等式と group 計算は通過。残りは `7=0 : ZMod 7` と prime-seven local instance を伴う division normalization |
| 同 command | third / **0** | `evidence/002-build-third.txt`。**9149 jobs、G1–G3 の proof を compile。新 module の warning なし** |
| `lake env lean DkMathTest/FLT/Seven/KummerAnthropicBridgeAudit002.lean` | **0** | `evidence/002-regression-axioms.txt`。G1–G3/spec/helper の型、arbitrary congruent unit と literal ideal congruence への適用、6宣言の axioms |
| `git diff --check`、new files を含む whitespace / forbidden constructs / scope scan | final | `evidence/002-final-verification.txt` |

build は既存 import dependencies の cache replay を含む focused target の検証。
import chain にある既存 `sorry` warnings は
`ZsigmondyCyclotomicResearch.lean:147`、`TriominoCosmicBranchA.lean:4187`、
`GcdNextResearch.lean:850`、`CyclotomicPrincipalization.lean:5389`。
**G1/G2/G3 と helper の axiom dependency には sorryAx がない**。
これらは Gate 001 の clean chosen-factor / unit-class baseline と整合する。
全 DkMath build や broad FLT7 facade build の成功を今回の結果としていない。

test の
`DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit002.congruentUnit_seventhPower`
も `[propext, Classical.choice, Quot.sound]` のみ。
test は packet ではなく arbitrary `u,h` への G3 適用を実際に elaboration している。
新 production/test source に `sorry`、`admit`、`axiom`、vacuous `True` target、
`unsafe`、`native_decide`、完成済み FLT 定理への direct import/call は追加していない。

## 変更ファイル

- 新規 `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`：G1–G3。
- 変更 `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean`：既存 helper 2本の公開化と docstrings。
- 新規 `DkMathTest/FLT/Seven/KummerAnthropicBridgeAudit002.lean`：opt-in regression / axioms。
- 変更 `docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/bridge-matrix-001.md` と `report-001.md`：明示した provenance erratum。
- 同フォルダの `README.md` / `ROADMAP.md`：local Gate 002 の実装・検証完了と review pending を記録。
- 同フォルダの `report-002.md` と `evidence/002-*`：今回の実測、失敗、source/axiom/scope audit。

## 残る境界と Gate 003 への提案

Gate 001 の「一般合同単数仕様が未証明」は今回 G3 で解消した。
既存 chosen-factor constructor の再実装や、`L=π*γ^7` から π を消す結論には進んでいない。
旧 universal class-group receiver、`True` ideal target、natural x/q-peel existence core も変更していない。

Gate 003 は、円分整数 x/y/z・RHS unit・π-adic exponent・非可除条件を保つ
**下降状態の新しい研究設計**として scope を見直すのが適切。
必要なのは actual next solution と exponent の strict decrease であり、
既に完成した chosen-factor constructor の追加 wrapper ではない。
具体的定義や遷移 theorem の実装には着手していない。

将来の wiring は、個別 consumer に一般 congruent-unit lemma が必要と判明した段階で
この module を直接 import することを提案する。broad facade や Lib への自動昇格は行わない。

**Gate 002 の G1–G3 に限り local Outcome A。human/Wise Wolf review に提出して停止する。FLT7 は OPEN。**
