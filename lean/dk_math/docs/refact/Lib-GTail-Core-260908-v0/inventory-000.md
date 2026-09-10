# GTCORE-000 Inventory

Date: 2026-09-10
Status: complete for the inventory checkpoint; implementation not started
Branch: `refact/DkMath-Lib-GTail-Core-260908-v0`
Source/build root: `lean/dk_math`

この文書は `analysis-001.md` と `analysis-002.md` を読んだ後の、現行
workspace に対する GTCORE-000 の事実 inventory である。ここで確認したのは
宣言、参照、import、既存の依存方向、候補定理の有無、変更前 build 状態だけで
ある。

## 0. Attached documents と今回の依頼の切り分け

### 今回の依頼で実行した範囲

- 2 文書を全文確認した。
- `GTail` / `GN` / `GNZC` / `cosmic_id_csr*` / `Nat.choose` / gcd / congruence /
  valuation の現行 source inventory を取った。
- `DkMath.Lib.*` の import 方向を実ソースで確認した。
- downstream consumer を FLT3、FLT5、ABC、Primitive/Pascal、RH/CFBRC、Goldbach
  に分類した。
- 変更前の focused build を再実行した。
- この報告ファイルだけを追加した。

### 添付文書から採用した inventory 要件

`analysis-001.md` §15, §20--21 と `analysis-002.md` §5, §9 の inventory 要件を
参照した。具体的には次を inventory の項目にした。

- 全 `[GNZC]` site
- `GN` の定義 / abbrev / compatibility wrapper
- 全 `cosmic_id_csr*` 参照
- public `GTail*` surface
- `DkMath.Lib.*` から上位 research package への import
- gcd / congruence / valuation / Pascal の重複候補
- downstream consumer の群別一覧
- 既存 canonical replacement と、まだ存在しない candidate theorem
- baseline focused-build target と結果

### この checkpoint では実行していないこと

以下は添付文書が後段に提案している作業であり、今回の direct request の範囲外
として実行していない。

- 実装、定理追加、定理 statement の変更
- `@[deprecated]` の追加
- GN の global rename または consumer の rewrite
- FLT3 / FLT5 / ABC / RH / Goldbach の source migration
- ファイル移動、facade の再編、大規模 refactor
- candidate theorem の「不在」を replacement 作成で埋めること

なお、既存ソースにすでにある `@[deprecated]` は inventory の事実として記録し
たが、この checkpoint で追加したものではない。

## 1. Workspace snapshot と evidence method

### Snapshot

- `git status --short`: 作業前、作業後とも空。
- 現在の branch: `refact/DkMath-Lib-GTail-Core-260908-v0`。
- 対象文書のディレクトリには開始時点で `analysis-001.md` と `analysis-002.md`
  のみが存在した。

### 主な検索境界

検索は nested source root の `DkMath/**/*.lean` と `DkMathTest/**/*.lean` を
中心に行った。historical standalone artifact と markdown は source migration
site と混同しないよう別記した。

代表的な再現コマンド:

```bash
cd lean/dk_math
rg -n '\[GNZC\]' DkMath DkMathTest
rg -n 'cosmic_id_csr' DkMath DkMathTest --glob '*.lean'
rg -n 'GTail|GN_eq_sum|GN_tail|Gbinom' DkMath DkMathTest --glob '*.lean'
rg -n '^import ' DkMath/Lib --glob '*.lean'
rg -n 'Nat\.choose|Nat\.gcd|padicValNat|Nat\.ModEq|\[MOD' DkMath/ABC DkMath/FLT DkMath/CFBRC DkMath/NumberTheory
```

検索結果の単純な lexical count は、名前・docstring・コメントも含むため、
semantic duplication の証明とは扱っていない。

## 2. 現行 ownership map

| 現行ファイル | 現行の役割 | GTCORE-000 判定 |
|---|---|---|
| `DkMath/Lib/Cosmic/GTail.lean` | `GTail` の唯一の現行定義、一般分解、recursion、境界 evaluation | canonical core owner 候補ではなく、すでに canonical definition owner |
| `DkMath/Lib/Cosmic/GTailNat.lean` | `ℕ` divisibility と head-unit non-divisibility | core natural layer |
| `DkMath/Lib/Cosmic/GTailCongruence.lean` | `Nat.ModEq` propagation と `x = 0` collapse、GN の `mod p²/p³` wrapper | core congruence layer。ただし GN-only theorem が残る |
| `DkMath/Lib/Cosmic/GTailPadic.lean` | higher tail の valuation lower/exact theorem と GN specialization | core valuation layer。ただし ABC への upward import が残る |
| `DkMath/CosmicFormula/GTail.lean` | `Lib.Cosmic.GTailCongruence` と `GTailPadic` を import する facade | declaration はない。移行後の互換 import 面 |
| `DkMath/CosmicFormula/Defs.lean` | `GZ`, temporary `G`, canonical naming home とされている `GN`, `GC` | canonical public vocabulary。ただし namespace は `DkMath.CosmicFormula` |
| `DkMath/CosmicFormula/CosmicFormulaBinom.lean` | legacy `G`、`GN` wrapper、`GN_eq_sum`、`cosmic_id_csr*`、Body-side compatibility | compatibility / downstream root。一般 GTail theorem 自体はここにない |
| `DkMath/Lib.lean` | Lib facade。GTail core 4 層と `Lib.Basic` を export | public Lib entrance |
| `DkMath/NumberTheory/WeightedBinomial.lean` | `GTailOneTerm`、filtered one-gap tail、weighted row bridge | generic downstream candidate。GTail core へまだ戻していない |
| `DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean` | FLT5 `GN5` と generic `GN` の bridge | project-specific consumer。`GN5_eq_generic_GN` は既存 |
| `DkMath/NumberTheory/Goldbach/Basic.lean` | degree-two `GN` fiber と `GN 2 x u = x + 2*u` | downstream consumer |
| `DkMath/NumberTheory/Goldbach/PairOverlap.lean` | support.card の `Nat.choose` hierarchy と r-fold observer | downstream Pascal observer。GTail equivalence は未証明 |
| `DkMath/ABC/PadicValNat.lean` | generic-looking `padicValNat` support lemmas | `GTailPadic` が現在依存する provider。dependency inversion candidate |

重要な現状は、definition の path は `DkMath.Lib.Cosmic.GTail` だが、宣言の
namespace は `DkMath.CosmicFormula` であること、また `GN` に canonical public
abbrev と compatibility abbrev の二つの入口があることである。

## 3. Public GTail core surface

### 3.1 `DkMath.Lib.Cosmic.*` の宣言

以下は `DkMath/Lib/Cosmic` の declaration search の全件である（private helper
`sum_range_modEq` を除く）。

| ファイル:行 | 宣言 | semantic role |
|---|---|---|
| `GTail.lean:40` | `GTail` | general normalized tail definition |
| `GTail.lean:50` | `add_pow_eq_prefix_add_xpow_mul_GTail` | general binomial decomposition; current root theorem |
| `GTail.lean:114` | `higher_tail_eq_pow_mul_GTail` | subtraction-shaped higher-tail factorization |
| `GTail.lean:125` | `GTail_zero_eq_add_pow` | r = 0 endpoint |
| `GTail.lean:133` | `GTail_self_eq_one` | r = d endpoint |
| `GTail.lean:146` | `GTail_rec` | one-step r recursion |
| `GTail.lean:176` | `GN_tail_rec` | r = 1 vocabulary wrapper |
| `GTail.lean:186` | `GN_tail_decomposition` | plan-name compatibility alias |
| `GTail.lean:198` | `Gbinom_tail_rec` | old Gbinom-flavored compatibility alias |
| `GTail.lean:211` | `GTail_one_eq_sum` | explicit r = 1 sum |
| `GTail.lean:226` | `GTail_eval_zero` | general boundary head at x = 0 |
| `GTail.lean:244` | `GN_zero_eval` | r = 1 boundary wrapper |
| `GTail.lean:255` | `Gbinom_zero_eval` | old Gbinom-flavored compatibility alias |
| `GTailNat.lean:28` | `pow_dvd_higher_tail` | natural higher-tail boundary divisibility |
| `GTailNat.lean:51` | `GTail_not_dvd_of_head_unit_of_prime_dvd_x` | general head-unit obstruction |
| `GTailNat.lean:69` | `GN_not_dvd_of_head_unit_of_prime_dvd_x` | r = 1 wrapper |
| `GTailCongruence.lean:59` | `GTail_congr_of_modEq` | general congruence propagation |
| `GTailCongruence.lean:77` | `GTail_modEq_eval_zero_of_dvd_x` | general boundary collapse |
| `GTailCongruence.lean:91` | `GN_modEq_choose_mul_pow_of_dvd_x` | r = 1 boundary wrapper |
| `GTailCongruence.lean:105` | `GN_modEq_head_of_dvd_x` | r = 1 naming duplicate |
| `GTailCongruence.lean:118` | `GN_modEq_mul_pow_self_of_dvd_x` | d-modulus specialization |
| `GTailCongruence.lean:131` | `GN_modEq_head_mod_sq_of_prime_dvd_x` | prime r = 1 mod p² theorem |
| `GTailCongruence.lean:170` | `GN_mod_p2_head` | plan-name alias |
| `GTailCongruence.lean:180` | `GN_eq_head_add_p_sq_mul_of_prime_dvd_x` | explicit p² remainder equality |
| `GTailCongruence.lean:205` | `GN_mod_p3_head` | conditional p³ wrapper |
| `GTailCongruence.lean:220` | `GN_eq_head_add_p_cube_mul_of_dvd_tail` | conditional explicit p³ equality |
| `GTailPadic.lean:27` | `padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x` | general normalized-tail valuation zero |
| `GTailPadic.lean:39` | `padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x` | r = 1 valuation wrapper |
| `GTailPadic.lean:53` | `padicValNat_higher_tail_lower_bound` | valuation lower bound for factored tail |
| `GTailPadic.lean:86` | `padicValNat_tail_exact_of_head_unit` | exact higher-tail valuation |
| `GTailPadic.lean:134` | `padicValNat_GN_exact_of_head_unit` | r = 1 exact valuation wrapper |

### 3.2 Downstream declarations whose names contain `GTail`

これらは core surface ではなく、現時点の downstream abstraction / consumer で
ある。大規模 rename の対象にはまだしていない。

- `DkMath/CosmicFormula/SquareGnomon.lean:84`
  `squareGnomonKernel_eq_GTail`
- `DkMath/NumberTheory/GNRepresentationBounds.lean:74`
  private `pow_le_GTail_two`
- `DkMath/NumberTheory/WeightedBinomial.lean:55,65,71,87,113,327,341,362,373,396,500,537,571,591`
  `GTailOneTerm`, `filteredGTailOneSum` と、それらの divisibility / bridge theorem
- `DkMath/NumberTheory/WeightedGNBridge.lean:37,48,63,73,84,140`
  filtered-tail と GN の bridge 群
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:1707,1762,1796,1835,1869`
  Branch A の scaled `GTail` estimates

## 4. `GN` definitions, aliases, and wrappers

### 4.1 現行 production definitions

| ファイル:行 | 宣言 | 判定 |
|---|---|---|
| `DkMath/CosmicFormula/Defs.lean:63` | `GZ` | Body-normalized kernel; GN rename path とは別 family |
| `DkMath/CosmicFormula/Defs.lean:74` | `G` abbrev to `GZ` | legacy Body alias |
| `DkMath/CosmicFormula/Defs.lean:85` | `DkMath.CosmicFormula.GN (R) (x) (u) (d) := GTail d 1 x u` | canonical naming home according to current docstring |
| `DkMath/CosmicFormula/CosmicFormulaBinom.lean:72` | `CommRing.G` | pre-normalized kernel; `x * G = GZ`, not a mere alias of GZ |
| `DkMath/CosmicFormula/CosmicFormulaBinom.lean:319` | `DkMath.CosmicFormulaBinom.GN d x u := DkMath.CosmicFormula.GN R x u d` | compatibility abbrev with legacy argument order |
| `DkMath/FLT/Five/GN5.lean:27` | `GN5` | exponent-five specialized polynomial |
| `DkMath/FLT/Five/Standalone.lean:29` | standalone `GN5` | Mathlib-only comparison artifact |

`DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean:59` に
`GN5_eq_generic_GN` が既にあり、production `GN5` と generic `GN 5` の同一性は
現行 theorem で確認できる。ただしこれは `GTail` core の新規実装ではない。

### 4.2 現行 compatibility theorem 群

`CosmicFormulaBinom.lean` の `CommSemiring` section は次を提供する。

- `GN_eq_sum` (`:328`): `GTail_one_eq_sum` から旧 explicit sum shape への bridge
- `GN_eq_G` / `G_eq_GN` (`:335--345`): CommRing の旧 G vocabulary
- `cosmic_id_csr` (`:354`): `BigN = BodyN + GapN`
- `cosmic_id_csr'` (`:366`): `(x+u)^d = x * GN + u^d`
- `add_pow_gap_factor` (`:383`): add-commuted wrapper
- `body_not_perfect_pow_of_squarefree_GN` (`:497` 付近): GN-specific arithmetic wrapper

`GN_tail_rec`, `GN_zero_eval`, `GN_not_dvd...`, congruence wrappers、valuation
wrappersは §3.1 に列挙した。いずれも現時点では deprecation を追加していない。

### 4.3 Historical standalone copies

以下の standalone/museum artifact は production import graph と別に保持されている。
inventory では rename target に含めず、互換性の注意点として記録する。

- `DkMath/FLT/docs/StandAlone/__FLT3#StandAlone-NC-v0.lean-v3.lean:468`
  の local `GN` と `:471` の local `cosmic_id_csr'`
- 同じ standalone source の `.txt` snapshots:
  `FLT3#StandAlone-NC-v0.lean-v2r1.lean.txt:464`,
  `FLT3#StandAlone-NC-v0.lean-v3.lean.txt:468`,
  `FLT3#StandAlone-NC-v0.lean.txt:540`,
  `FLT3#StandAlone-v4.lean.txt:869`
- standalone `GN5` は `FLT5#StandAlone-v1-v4330.lean.txt:122` にもある。

## 5. 全 `[GNZC]` site

`lean/dk_math/DkMath/**/*.lean` で 30 occurrences。`DkMathTest` には該当 source
marker はなかった。各 site を current meaning に従って A--D に仮分類した。

- **A: canonical/general GTail** — general theorem または canonical Lib surface を示す
- **B: useful r = 1 specialization** — GTail theorem を先に作れば wrapper として残せる
- **C: compatibility-only legacy** — replacement が安定してから後段で deprecate 検討
- **D: separate family / do not mechanically migrate** — GZ/GC/GCell/analytic family

| ファイル:行 | 内容 | 仮分類 |
|---|---|---|
| `Lib/Cosmic/GTail.lean:196,253` | `Gbinom_tail_rec` / `Gbinom_zero_eval` より `GN_*` を優先 | C |
| `Lib/Cosmic/GTailNat.lean:67` | standard GN layer の non-divisibility wrapper | B |
| `Lib/Cosmic/GTailPadic.lean:132` | standard GN layer の exact valuation wrapper | B |
| `CosmicFormula/Defs.lean:54` | canonical names centralized in Defs | A/B |
| `CosmicFormula/Defs.lean:69` | old `G` と `GZ` naming anchor | C/D |
| `CosmicFormula/Defs.lean:80` | `Defs.GN` is naming-stable r = 1 entry | B |
| `CosmicFormula/Defs.lean:91` | future `GC` seat | D |
| `CosmicFormula/CosmicFormulaDim.lean:18` | analytic/geometry-facing separate family | D |
| `CosmicFormula/CosmicFormulaCellDim.lean:106,115` | local `Gbinom` contrast-name | C/D |
| `CosmicFormula/CosmicFormulaCellDim.lean:126` | CellDim counterpart of `x * GN = GZ` | C/D |
| `CosmicFormula/CosmicFormulaCellDim.lean:311` | new `GN` spelling; old `pow_sub_pow_eq_mul_Gbinom` | C |
| `CosmicFormula/CosmicFormulaCellDim.lean:370` | geometric-series `GCell` family | D |
| `CosmicFormula/CosmicTheorems.lean:43` | qualify `CosmicFormulaBinom.GN` to avoid shadowing | C/B |
| `CosmicFormula/CosmicFormulaBinom.lean:61,69` | legacy CommRing `G` | C |
| `CosmicFormula/CosmicFormulaBinom.lean:87,103,112,149` | `G` / `GZ` bridge and normalized identity | C/D |
| `CosmicFormula/CosmicFormulaBinom.lean:182,189` | thin `cosmic_id` corollary and legacy duplicate | C |
| `CosmicFormula/CosmicFormulaBinom.lean:312` | canonical `Defs.GN` note for wrapper | B/C |
| `CosmicFormula/CosmicFormulaBinom.lean:491` | FLT-like GN-specific obstruction wrapper | B; not generic yet |
| `KUS/CosmicBridge.lean:20,56` | `GZ` canonical, legacy `G` temporary alias | C/D |
| `KUS/CosmicBridge.lean:118,128,138` | stable theorem names with GZ wording | C/D |

The current marker inventory itself therefore confirms that `[GNZC]` is broader than a
mechanical `GN -> GTail` rename. In particular, GZ/GC/GCell and CommRing pre-normalized
G require separate semantic handling.

## 6. 全 `cosmic_id_csr*` reference inventory

`DkMath/**/*.lean` と `DkMathTest/**/*.lean` の Lean source で 46 occurrences。行番号
は current workspace の検索結果である。

| ファイル | 行 |
|---|---|
| `ABC/GNLegacyTailCountingBridge.lean` | 399, 410 |
| `ABC/GNOddPrimeExceptionalExcess.lean` | 48 |
| `ABC/GNPowerLift.lean` | 46, 50 |
| `BookOfMagic/GNFiniteDifference.lean` | 97 |
| `CFBRC/Basic.lean` | 97 |
| `CosmicFormula/CoreBeamGap.lean` | 107 |
| `CosmicFormula/CosmicDerivativePower.lean` | 51 |
| `CosmicFormula/CosmicFormulaBinom.lean` | 354, 366, 383 |
| `CosmicFormula/CosmicTheorems.lean` | 29, 32, 35, 38 |
| `CosmicFormula/SquareGnomon.lean` | 123 |
| `FLT/Basic.lean` | 1038, 1103, 1105 |
| `FLT/Core.lean` | 51, 53, 153 |
| `FLT/CosmicPetalBridge.lean` | 27 |
| `FLT/PrimeProvider/TriominoCosmicBranchADescentChain.lean` | 1182, 2592, 2595, 2661, 2678, 2707 |
| `FLT/PrimeProvider/TriominoCosmicBranchARestore.lean` | 2741, 2760, 2803 |
| `FLT/PrimeProvider/TriominoCosmicBranchARestoreArithmeticStrong.lean` | 895, 926 |
| `FLT/Seven/CounterexampleRouting.lean` | 49 |
| `NumberTheory/GNDegreeFactorization.lean` | 39, 42, 45 |
| `NumberTheory/GNThreePrimeArithmetic.lean` | 201 |
| `NumberTheory/Primitive/SquareBody.lean` | 22 |
| `NumberTheory/UniqueFactorizationGN.lean` | 1641 |
| `NumberTheory/ZsigmondyCyclotomic.lean` | 412, 425 |
| historical `FLT/docs/StandAlone/__FLT3#StandAlone-NC-v0.lean-v3.lean` | 471, 501 |

Production source だけでなく standalone artifact にも同名 theorem があるため、
後段の compatibility plan では import graph と museum artifact を分ける必要が
ある。markdown の historical mentions はこの 46 occurrence count には含めていない。

## 7. GTail direct imports と upward dependency

### 7.1 Direct import surface

現行の direct import search で確認できた主な入口は次の通り。

```text
DkMath.Lib
  -> DkMath.Lib.Cosmic.GTail
  -> DkMath.Lib.Cosmic.GTailNat
  -> DkMath.Lib.Cosmic.GTailCongruence
  -> DkMath.Lib.Cosmic.GTailPadic

DkMath.CosmicFormula.GTail
  -> DkMath.Lib.Cosmic.GTailCongruence
  -> DkMath.Lib.Cosmic.GTailPadic

DkMath.CosmicFormula.Defs
  -> DkMath.CosmicFormula.GTail

DkMath.NumberTheory.WeightedBinomial
  -> DkMath.Lib.Cosmic.GTail

DkMath.NumberTheory.GNRepresentationBounds
  -> DkMath.CosmicFormula.CosmicFormulaBinom

DkMath.FLT.PrimeProvider.TriominoCosmicBranchA
  -> DkMath.CFBRC.Bridge
  -> DkMath.NumberTheory.Gcd.GN
  (source 内で GTail d 2 / d 3 を直接使用)
```

`DkMath.CosmicFormula.GTail.lean` 自体は空の namespace facade で、GTail theorem
の重複定義はない。

### 7.2 実際に確認できた upward import

唯一の明確な Lib-to-research upward import は次である。

```text
DkMath/Lib/Cosmic/GTailPadic.lean:7  import DkMath.Lib.Cosmic.GTailNat
DkMath/Lib/Cosmic/GTailPadic.lean:8  import DkMath.ABC.PadicValNat
```

さらに `GTailPadic.lean:69,71,77,125` で
`DkMath.ABC.padicValNat_pow'` と
`DkMath.ABC.padicValNat_le_iff_dvd` を使用している。

一方、`DkMath.Lib/Cosmic/GTail*.lean` から FLT / RH / CFBRC / Goldbach への
import は今回の source import search では見つからなかった。`Mathlib` の直接
import (`Lib/Basic.lean:7`, `GTail.lean:7`) は外部基礎層として別扱いにした。

Goldbach は逆方向で、`Goldbach/Basic.lean:6` が
`DkMath.CosmicFormula.CosmicFormulaBinom` を import している。Goldbach-specific
obstruction を Lib に持ち上げる source evidence はない。

## 8. gcd / congruence / valuation / Pascal の重複候補

ここでいう「重複」は同じ statement と確定した意味ではなく、同じ数学的役割を
GN-specific または project-specific vocabulary で再実装しているため、後段の
canonicalization audit が必要な候補を指す。

| family | 現行 evidence | GTCORE-000 判定 |
|---|---|---|
| gcd / boundary | `NumberTheory/Gcd/GN.lean:176,192,210,277,310,346,359,366` の `gcd_gap_GN_dvd_exp`, `coprime_boundary_GN...`, `padicValNat_sub_pow_eq_padicValNat_GN...`, degree-3 boundary gcd; `CFBRC/ExceptionalExistence.lean:46` の `gcd_GN_eq_prime`; `FLT/Seven/CounterexampleRouting.lean:78,92,103` の degree-7 gcd cases | generic `gcd_GTail` / `gcd_boundary_GTail` nameは search で 0。analysis-001 Candidate A は未実装候補として残る |
| congruence | `Lib/Cosmic/GTailCongruence.lean:59,77` の general theoremと `:91--224` の GN wrappers; `CFBRC/ExceptionalExistence.lean:88` の `GN_congr_mul_pow_mod_sq`; `ABC/GNLegacyTailCountingBridge.lean:216` の `GN_modEq_left`; FLT/Seven と PrimeProvider の degree-specific modulo packets | `GN_congr_mul_pow_mod_sq` は core の `mod p²` theoremと役割が重なるが assumptions/shape が異なるため、まだ duplicate と断定しない |
| valuation | `Lib/Cosmic/GTailPadic.lean:27,53,86` の general layer; `ABC/PadicValNat.lean:18,69,137,152,186,206,228` の reusable-looking provider; `ABC/GNLegacyTailCountingBridge.lean:1164,1226,1266`; `ABC/GNOddPrimeExceptionalExcess.lean:81,216`; `CFBRC/Bridge.lean:255,274,295,318,338,362,387,416,446,481`; `FLT/Three/CubicValuationDepth.lean:75`; `FLT/Five/Valuation.lean:29,43,64` | theorem familyは広い。まず provider dependency の向きを確定し、その後 GN-specific theorem が general `GTail` theorem の wrapper かを比較する必要がある |
| Pascal / choose | `GTail_rec` と `GTail_eval_zero`; `NumberTheory/WeightedBinomial.lean:55--87` の `GTailOneTerm` / filtered tail; `Goldbach/PairOverlap.lean:39--66` の r-fold observerと private `choose_two_eq_sub_one_add_choose_sub_one`; `NumberTheory/PascalPrimeDial.lean:30--149` の Pascal coefficient mass / prime dial | `GTailPascal` moduleも `GTail_split_at` / `GTail_transport_depth` も search で 0。Goldbach の `Nat.choose` hierarchy は GTail equivalent ではない |

既存の `@[deprecated]` は `CFBRC/Bridge.lean:50` などにあるが、これは既存
cyclotomic bridge の deprecation であり、GTCORE-000 の変更ではない。

### 8.1 candidate theorem の不在確認

次の proposed names は current source search で 0 occurrence だった。replacement
は作成していない。

```text
GTail_split_at
GTail_eq_prefix_between_add_pow_mul_GTail
GTail_transport_depth
gcd_GTail
gcd_boundary_GTail
GTail_modEq_head
GTail_mod_p2
```

ただし `padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x` のように、既に
もっと具体的な一般 theorem は存在する。したがって「generic valuation API が
全くない」とは記録しない。

## 9. Downstream consumers grouped by project

以下の件数は、`GN` の exact application (`GN ` / `GN(` または
`CosmicFormulaBinom.GN`) を source file 単位で数えたもの。名前に `GN` を含む
project-specific definition（例 `GNExcess...`）だけの file は別の migration target
とは数えていない。

| group | exact source-file count | primary evidence / notes |
|---|---:|---|
| FLT3 | 3 direct `GN`/related files under `FLT/Three`; plus `FLT/Core.lean`, `FLT/Basic.lean` for the old cosmic identity | `Three/CubicValuationDepth.lean`, `EisensteinSubstrate.lean`, `PrimitiveCubicLiftPacket.lean`; FLT3-specific valuation is not yet a generic GTail theorem |
| FLT5 | 14 `GN5` files, not `GN` application files | `FLT/Five/GN5.lean` is specialized; `StructuralArithmetic/GNBridge.lean:59` proves `GN5_eq_generic_GN`; no automatic rename is justified |
| FLT7 / other FLT | 11 degree-seven files plus 32 core/provider files with GN application | `Seven/CounterexampleRouting.lean` has explicit degree-seven gcd cases; PrimeProvider has large GN-heavy route surface |
| ABC | 40 source files | `GNLegacyTailCountingBridge`, `GNOddPrimeExceptionalExcess`, `GNPowerLift`, `GNExceptionalSplit`, `GNValuationSplit`, `ValuationFlowBridge`, and the GNExcess family |
| Primitive / Pascal | no direct exact `GN` application under `NumberTheory/Primitive` or root `Pascal.lean`; indirect/bridge use exists | `Primitive/SquareBody.lean:22` and `:unitSquare_body_eq` use `BodyN`/`GN_eq_sum`; `PrimitiveBeam.lean` has GN primitive-factor API; `PascalPrimeDial.lean` is Nat.choose/Pascal-only |
| RH | no direct exact `GN` application found under `DkMath/RH` | RH-CFBRC remains a future/independent audit surface; no source dependency to promote in this inventory |
| CFBRC | 4 source files | `CFBRC/Basic.lean`, `Bridge.lean`, `CyclotomicProduct.lean`, `ExceptionalExistence.lean`; `cyclotomicPrimeCore` and GN equality are project bridges |
| Goldbach | 5 source files with GN vocabulary/application | `Goldbach/Basic.lean:30,50,56`; `Capacity`, `Conservation`, `Obstruction`, `Signature` carry the GN fiber API; `PairOverlap` adds an independent `Nat.choose` hierarchy |

Representative exact consumer files:

```text
ABC:
  DkMath/ABC/GNLegacyTailCountingBridge.lean
  DkMath/ABC/GNOddPrimeExceptionalExcess.lean
  DkMath/ABC/GNPowerLift.lean
  DkMath/ABC/GNExceptionalSplit.lean
  DkMath/ABC/GNValuationSplit.lean
  DkMath/ABC/GNWieferichAccumulation.lean
  DkMath/ABC/ValuationFlowBridge.lean
  DkMath/ABC/ValuationFlowBridgeExamples.lean
  DkMath/ABC/GNExcessCubic*.lean

FLT3:
  DkMath/FLT/Three/CubicValuationDepth.lean
  DkMath/FLT/Three/EisensteinSubstrate.lean
  DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean

FLT5:
  DkMath/FLT/Five/GN5.lean
  DkMath/FLT/Five/CleanChannel.lean
  DkMath/FLT/Five/Valuation.lean
  DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean

CFBRC:
  DkMath/CFBRC/Basic.lean
  DkMath/CFBRC/Bridge.lean
  DkMath/CFBRC/CyclotomicProduct.lean
  DkMath/CFBRC/ExceptionalExistence.lean

Goldbach:
  DkMath/NumberTheory/Goldbach/Basic.lean
  DkMath/NumberTheory/Goldbach/Capacity.lean
  DkMath/NumberTheory/Goldbach/Conservation.lean
  DkMath/NumberTheory/Goldbach/Obstruction.lean
  DkMath/NumberTheory/Goldbach/Signature.lean
  DkMath/NumberTheory/Goldbach/PairOverlap.lean  # Nat.choose observer; no equivalence
  DkMathTest/NumberTheory/GoldbachGNFiber.lean
```

### Goldbach の扱い

`GoldbachGNFiberAt` は実際に `GN 2 x u` を使うため、Goldbach は単なる lexical
consumer ではない。一方 `goldbachOffsetROverlapMultiplicity` は
`Nat.choose support.card r` であり、GTail の `r` と共通するのは現時点では
Pascal recursion / filtration の形だけである。`PairOverlap.lean:21--22` の明記通り、
formal GTail equivalence は未証明であり、Goldbach を Lib dependency に移していない。

## 10. Baseline focused build

GTCORE-000 の source inventory 前に nested build root で次を実行した。

```bash
cd lean/dk_math
lake build \
  DkMath.Lib.Cosmic.GTail \
  DkMath.Lib.Cosmic.GTailNat \
  DkMath.Lib.Cosmic.GTailCongruence \
  DkMath.Lib.Cosmic.GTailPadic \
  DkMath.CosmicFormula \
  DkMath.FLT.Three \
  DkMath.FLT.Five \
  DkMath.ABC \
  DkMath.NumberTheory.Primitive \
  DkMath.CFBRC \
  DkMath.NumberTheory.Goldbach \
  DkMathTest.NumberTheory.GoldbachGNFiber
```

Result:

```text
Build completed successfully (9017 jobs).
```

確認された target marker は `GTail`, `GTailNat`, `GTailCongruence`, `ABC.PadicValNat`,
`GTailPadic`, `CosmicFormula`, `Primitive`, `CFBRC`, `Goldbach`,
`GoldbachGNFiber` などである。既存依存にある `sorry` warning / axiom audit output
は build 成功とは別の既存情報であり、この inventory で新規 theorem を追加した
結果ではない。今回の source tree は build 前後で変更されていない。

## 11. GTCORE-000 conclusion and next boundary

### Inventory conclusion

1. `GTail` の一般定義と一般 decomposition はすでに Lib に存在する。
2. `GN` は `Defs.GN` と `CosmicFormulaBinom.GN` の二つの public入口を持つ。
3. `GN_eq_sum`、`GN_eq_G`、`GN5_eq_generic_GN`、既存の GN-specific gcd/valuation
   bridge など、過去の compatibility foundation は再実装しない。
4. 現行 Lib の明白な architectural issue は `GTailPadic -> ABC.PadicValNat`
   の upward dependency である。
5. general `GTail` の r-to-s filtration と exact boundary gcd は現行 source search
   では確認できない candidate seat である。
6. Goldbach の r-fold `Nat.choose` observer は downstream evidence だが、GTail と
   の formal equivalence ではない。
7. FLT3/FLT5/ABC/CFBRC の GN surface は広く、global rename は proof shape と
   compatibility facade を壊す migration risk がある。

### 後段の候補（未実行）

添付文書の順序をそのまま実行指示とはせず、inventory 後の候補として記録する。

- generic Pascal / tail filtration surface の設計比較
- exact boundary gcd の既存 theorem search と条件整理
- ABC の generic `padicValNat` support を lower Lib に置く依存方向の設計
- その後に GN-specific wrappers / deprecations / downstream replay

このファイルの作成をもって、ユーザーが指定した **GTCORE-000 inventory only** の
terminal boundary とする。次の実装 checkpoint は、ユーザーの別指示があるまで
開始しない。
