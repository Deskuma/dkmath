# Step041 report — genuine focused capacity independence

2026-10-11。Outcome B / Step041 COMPLETE / STOP041。
Base HEAD `3e5db727b77799fd163834bb9b3c799097d7b187`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
[source inventory](source-inventory-041.md) / [frontier](frontier-041.md)。

## 実装と Lean 結果

新 production `GTailFocusedCapacityIndependence` の公開 theorem は二つ。
`exists_full_support_without_size` と `exists_size_without_full_support` は
正・primitive・focus・厳密な gap/endpoint inequalities を全て含む実際の存在定理。
一般 geometry structure や numeric public aliases は追加せず、private factor-support certificates と
kernel `decide` / `norm_num` で具体的 witnesses を構成した。

| Quantity | A=(13,35,46,2) | B=(1497,2797,2802,1492) |
|---|---|---|
| a+b=c+g | 48 | 4294 |
| Nat.Coprime a b / strict positive focus | checked | checked |
| Q | 1849=43² | 14251327=37*385171 |
| actual primeFactors Q | {43} | {37,385171} |
| actual M_Q | 1849 | 203100321260929=Q² |
| signed Δ | -371415611824 | -179820312066002 |
| natAbs Δ | 371415611824 | 179820312066002 |
| collective square support | True | False |
| strict natAbs<M_Q | False | True |
| Fermat / exact scalar balance | False / False | False / False |

43、37、385171 の primality は norm_num。実際の primeFactors は verified product equality、
Nat.primeFactors_mul、Nat.Prime.primeFactors で rewrite した。
巨大 primeFactors を raw decide で展開しない。候補の数学的数値訂正は不要だった。
負の defect は ℤ の subtraction、size は natAbs による。
¬Fermat は Step039 focusedFermatDefect_zero_iff、¬balance は Step032 equivalence を使用した。
B は37/385171の first-power および square support が共に false。
strict magnitude から divisibility を推論せず、B に selected square route を適用しない。

## Native A の実際の source selection と付値

T=GTail 7 1 2 46=75625342528、43²∣T、43∤35,46,2。
actual residue root=-13/35=7、Tail ratio=(46+2)/46=16 in ZMod43。
quadratic relation、r⁷=1、r≠0,1 を kernel-check した。
Step039 defect_square_prime_route を hEq なしで実際に適用した。

optional equality も成功:

```lean
nativeKernel (q := 43) 13 35 46 2
  (by decide) (by decide) (by decide) (by decide) (by decide) =
  GTailPrimeGrid.M (1 : Fin 2) (4 : Fin 6)
```

nativeEval を actual roots で rewrite し、RingHom を ext、全 coordinates の equality を rfl で証明、
congrArg RingHom.ker で actual ideal equality を得た。
既存 C=QuadraticAlgebra SevenCyclotomicDegreeSixInt.Ring (-1) 1 をそのまま使用する。
旧 M00=(37,11) とは異なる row/column address (7,16) が actual arithmetic input から選ばれる。
source image equality / signed-prime packet の証明ではない。

v43(Q)=2、v43(T)=2、v43(g)=0 を padicValNat_le_iff_dvd と checked q²/q³ bounds、
eq_zero_of_not_dvd で検証した。v43(g)+v43(T)=2≠4=2v43(Q)。
Step031 の hEq-conditioned exact budget は使用しない。

## 旧対照例と conditional certificate

| Actual tuple | Full support | Strict size | Fermat |
|---|---|---|---|
| Old Tail (1166,1857,1858,1165) | False | False | False |
| Old Gap (196,211,238,169) | False | False | False |
| New A | True | False | False |
| New B | False | True | False |

新 test で旧 Tail の7²、旧 Gap の3² support failure と actual size failure を再確認。
prime membership は Nat.mem_primeFactors の actual certificate、size は
quadratic_modulus_le_square と Q²<natAbs の numeric proof を合成した。
旧 geometry / non-Fermat / balance は Step040/039 direct regression に含まれる。
第四の True/True/non-Fermat row は既存 full_quadratic_defect_zero_certificate の
直接適用により不可能、symbolic example で確認した。新 number-theoretic obstruction と呼ばない。
A/B は conditional zero theorem の反例ではなく、その片方の前提だけでは足りない対照例。

## 公開宣言の実際の signatures / axioms

最終 test07 の #check 出力を以下に転記した。

```lean
DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_full_support_without_size :
  ∃ a b c g,
    (0 < a ∧ 0 < b ∧ a.Coprime b ∧ a + b = c + g ∧ 0 < g ∧ g < a ∧ g < b ∧ a < c ∧ b < c ∧ c < a + b) ∧
      (∀ p ∈ (a ^ 2 + a * b + b ^ 2).primeFactors, ↑p ^ 2 ∣ focusedFermatDefect a b c) ∧
        ¬(focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus (a ^ 2 + a * b + b ^ 2).primeFactors ∧
          ¬Fermat7Equation a b c
```

```lean
DkMath.FLT.Seven.GTailFocusedCapacityIndependence.exists_size_without_full_support :
  ∃ a b c g,
    (0 < a ∧ 0 < b ∧ a.Coprime b ∧ a + b = c + g ∧ 0 < g ∧ g < a ∧ g < b ∧ a < c ∧ b < c ∧ c < a + b) ∧
      (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus (a ^ 2 + a * b + b ^ 2).primeFactors ∧
        (¬∀ p ∈ (a ^ 2 + a * b + b ^ 2).primeFactors, ↑p ^ 2 ∣ focusedFermatDefect a b c) ∧ ¬Fermat7Equation a b c
```

両 theorem の #print axioms は `[propext, Classical.choice, Quot.sound]`。
新公理はない。全公開宣言を対象に監査した。

## 実行コマンド・失敗と修正

cwd `lean/dk_math`。全 Lake build は sequential、process-local LEAN_NUM_THREADS=2。
全ログ `.lake/build/gtail-step041/NN-build.log`、exact ledger `runs.json`。

| Log | Actual command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedCapacityIndependence` | 1 | 0 | 15.71 |
| 02 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedCapacityIndependence` | 0 | 0 | 15.64 |
| 03 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence` | 1 | 0 | 16.44 |
| 04 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence` | 0 | 0 | 16.55 |
| 05 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedCapacityIndependence` | 0 | 0 | 15.3 |
| 06 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence` | 0 | 0 | 16.1 |
| 07 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedCapacityIndependence` | 0 | 0 | 16.4 |
| 08 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 0 | 0 | 8.6 |
| 09 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 8.44 |

- 01 production: singleton primeFactors rewrite が同じ43を二度置換しようとして失敗。
  rw は hp.primeFactors 一つで両 occurrence を rewrite 済みだった。重複 hr rewrite と未使用 certificate を除去。
- 02: A/B existential と385171 primality を含む source 成功。
- 03 test: selected route の a,b と nativeKernel の q が結論から定まらず decide に metavariables が残った。
  `(a := 13) (b := 35) (q := 43)` / `(q := 43)` を明示して修正。数値や数学的前提は変更しない。
- 04: root/grid equality、numeric controls、valuation controls を含めて成功。
- 05 source: code spacing 校正後の最終 production が Built。
- 06 test: full support negation と fourth-row symbolic control 追加後成功。
- 07 test: long lines / spacing 校正後の最終 test が Built。
- 08/09: Step040/039 direct regression 成功。既存 targets の cached replay を含む。
  新 source/test の Built と区別する。全 clean suite 成功を主張しない。

初回ファイル生成用 Python は cwd に対する重複 lean/dk_math prefix により FileNotFoundError。
新ファイルを作る前に終了した。cwd-relative paths に修正して生成した。
compiler arithmetic failure、large-primality recursion failure、resource workaround は今回ない。

## Lean 結果からの気づき・試した命題・実装提案

1. 実際の strict primitive geometry 自体は full support も strict magnitude も保証しない。
   今回の二つの existential により、両前提の片方だけを geometry の帰結として期待する経路を具体的に診断できた。
   hypothetical Fermat input の追加構造に対する制約まで否定したわけではない。
2. A の nonsquarefree Q により M_Q<Q² が実例で厳密になる。
   Q² を支持法の modulus と同一視すると偽の support-capacity ledger になる。
   primeFactors の distinct support を取り、素数の重複 exponent を再投入しない方針を維持する。
3. full support と actual native common kernel が同時に存在しても size failure は残る。
   同じ local kernel interface を増やすだけでは、この global missing input は補えない。
4. B は size inequality が単独では q∣Δ さえ与えない near miss。
   magnitude と p-adic divisibility の証明義務は今後も別々に保持する。
5. A の exact valuation budget failure は square route と equation-conditioned budget の違いを明瞭にした。
   q²∣Δ を hEq の代用品として条件付き valuation theorem に渡さない。
6. 試した optional native grid equality は新 import なしの ext/rfl normalization で通った。
   今後 actual source-match が必要な場合も同じ carrier と全座標 RingHom equality を優先し、
   source-image equality や signed packet への飛躍を避ける。
7. 次の実装提案は、既存 hypothetical Fermat source から独立に証明可能な新 global restriction の
   契約を評価するか、old reconstruction の exact fields を genuine に構成する経路を評価すること。
   今回その restriction / reconstruction は証明していない。追加 catalogue は作らず STOP041。

## 依存・書式・履歴の最終監査

production closure8956（local176）、test closure8957（local177）、local union177 vertices、cycle0。
neutral GTailSevenRealTraceResidue closure1907（local20）に FLT reachability0。
production の27 neutral Lib owners の独立 closure も FLT reachability0。
Step040 saved module set から added は新 production owner 一つ、removed0。
historical module-set comparison を fresh historical build と呼ばない。
ABC.Rad / Seven facade / heavy excluded owners は closure にない。

新 test は example40件、公開2 theorem 全件を監査。最終 source05/test07/regression08/09 は exit0 / warning0。

新 source/test の comments/strings 除去後 sorry / admit / axiom / unsafe / native_decide /
set_option / False.elim は0。MIT2026 header、import 後 file print、二-space proof indentation、
新ファイルの tabs / trailing whitespace / newline と git diff --check を監査した。
旧 tracked source/report/review/correction は変更0、ROADMAP は HEAD bytes を保持して追記のみ。

AwayDescentClosureProvider は nextX/Y/Z、new CounterexamplePack、new AwayValuationTransferPacket、
exact carrier_match が依然必要。RamifiedSignedRootDepthPacket は balanced signed identities、
coprimality、gap/quotient roots、7-unit guards、normalizedEquation が依然必要。
本作業はこれらの構成や unconditional FLT7 contradiction ではない。

証拠 `.lake/build/gtail-step041/`: runs.json、全 build logs、signatures.json、imports.json、
import-impact.json、proof-contract-audit.json、audit.json、workspace-audit.json。
