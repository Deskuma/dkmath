# Step040 report — finite prime aggregation and signed absolute-size capacity

2026-10-11。Outcome B: conditional global zero criterion / capacity audit。
Base HEAD `58f3761acb336aaf41d378b86b26be1ddb8e4984`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
[source inventory](source-inventory-040.md) / [frontier](frontier-040.md)。

## 実装と正確な追加仮定

新 production/test owners を作成した。公開13宣言（definition1 / theorems12）。
production の direct import は Step039 一つのみ。追加の Mathlib / ABC / signed-owner import はない。

| Gate | Actual proof | Missing independent input |
|---|---|---|
| 1 | M_S>0、M_S=(S.prod id)²、integer divisor iff all selected prime squares divide | every p∈S is prime と collective local support を要求 |
| 2 | divisor + strict natAbs bound gives zero、nonzero divisor gives M≤natAbs | strict Archimedean bound を要求 |
| 3 | actual Q prime support、M_Q∣Q²、M_Q≤Q²、full-Q certificate | Q≠0、all actual primes の support と strict size を要求 |
| 4 | signed positive/negative controls と abstract all-support nonzero integers | coverage failure と size failure を別々に検証 |

finite aggregation は private Finset induction。
新 p と remaining set の r が distinct prime であるため coprime_primes、
pow_left/pow_right 2、coprime_prod_right_iff により p² と remaining product は coprime。
mul_dvd_of_dvd_of_dvd で product divisor を得た。
「各 factor が割るから任意の積が割る」という誤った合成は使わない。
逆向きは dvd_prod_of_mem で factor を取り出すので、optional iff まで証明した。

Int generic threshold と converse は actual Mathlib APIs を使用した。
m>0 を要求しない stronger signature で成立し、prime modulus の positivity は別 theorem で提供する。
negative z でも natAbs を使う。z<m という sign-sensitive bound は使わない。

Fermat-facing signatures に hsize と hlocal/hsupport を残した。
hEq / Δ=0、focus / positivity / coprimality を入口に仮定していない。
結論の equation は Step039 zero-defect iff を通して得る。
collective support を Step039 の selected q から一般化していない。

## Existing radical / dependency overlap

actual ABC.Rad.rad n の定義は n.factorization.support.prod (fun p=>p)。
その owner の Basic / Factorization.Basic / Mathlib.Tactic imports は既存 closure にあるので、
追加時の module-set 増分は ABC.Rad owner 一つに相当する。
既存 closure 自体は大きいが、今回 ABC import による巨大な regression が実測されたとしない。
新 FLT→ABC dependency が不要なため import せず、Mathlib.prod_primeFactors_dvd を利用した。

test の exact expression bridge は Nat.support_factorization により
M_(primeFactors n)=(n.factorization.support.prod (fun p=>p))²。
この右辺は actual rad の defining expression であり、数学的 identification を検証した。
ABC.rad named constant に対する production bridge theorem や第二の general radical library は追加していない。

Q=0 / 1 の prime support は empty、M=1。
M_Q∣Q² は Q=0 にも成立するが、M_Q≤Q² は Q≠0 を必要とする。
Q=0 で1≤0が false の test も保持した。full-Q certificate の hQ0 は明示的に残る。

## Numeric support と magnitude の独立した診断

全候補 products / primality / prime support / modulus / absolute values を Lean で検証した。
候補数値の訂正は不要だった。Step039 の positive primitive strict focused geometry と ¬hEq / ¬exact balance も再確認した。

| Quantity | Tail (1166,1857,1858,1165) | Gap (196,211,238,169) |
|---|---|---|
| Q | 6,973,267=7·43·23167 | 124,293=3·13·3187 |
| actual primeFactors Q | {7,43,23167} | {3,13,3187} |
| all factors prime | checked | checked |
| M_Q=Q² | 48,626,452,653,289 | 15,448,749,849 |
| signed Δ | +2,642,627,963,860,178,152,897 | −13,523,337,259,569,605 |
| natAbs Δ | 2,642,627,963,860,178,152,897 | 13,523,337,259,569,605 |
| selected square support | 43²∣Δ | 13²∣Δ |
| missing support | 7²∤Δ、23167²∤Δ | 3²∤Δ、3187²∤Δ |
| collective hsupport | false | false |
| strict hsize | false: M_Q<∣Δ∣ | false: M_Q<∣Δ∣ |

両例は zero certificate の二つの前提を BOTH 満たさない。
したがって conditional all-support-plus-size theorem の反例ではない。
一つの selected local square と potential full modulus の容量不足を別々に示す例である。

abstract integer controls は S={2,3}、M=36、z=+36 / −36。
全 local squares が割り、z は非零、strict threshold は成立しない。
これは collective congruence alone が zero を強制しない例であり、actual Fermat defect tuple として提示していない。
empty/zero conventions、signed thresholds、nonprime overlapping factors4/8の誤った積 divisor の否定も検証した。

新 test は example56件。generic symbolic tests は全 finite / full-Q certificate signatures をそのまま検証する。

## 公開宣言の実際の elaborated signatures

最終 test07 の #check 出力から記録した。collective support と independent hsize が実際の引数に残る。

### squarePrimeSupportModulus

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus (S : Finset ℕ) : ℕ
```

### squarePrimeSupportModulus_pos

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_pos (S : Finset ℕ)
  (hs : ∀ p ∈ S, Nat.Prime p) : 0 < squarePrimeSupportModulus S
```

### squarePrimeSupportModulus_eq

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_eq (S : Finset ℕ) :
  squarePrimeSupportModulus S = (∏ p ∈ S, p) ^ 2
```

### squarePrimeSupportModulus_dvd_iff

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.squarePrimeSupportModulus_dvd_iff (S : Finset ℕ) (z : ℤ)
  (hs : ∀ p ∈ S, Nat.Prime p) : ↑(squarePrimeSupportModulus S) ∣ z ↔ ∀ p ∈ S, ↑p ^ 2 ∣ z
```

### int_zero_of_modulus_size

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_zero_of_modulus_size {m : ℕ} {z : ℤ} (hdiv : ↑m ∣ z)
  (hsize : z.natAbs < m) : z = 0
```

### int_nonzero_modulus_bound

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.int_nonzero_modulus_bound {m : ℕ} {z : ℤ} (hdiv : ↑m ∣ z)
  (hz : z ≠ 0) : m ≤ z.natAbs
```

### finite_support_zero

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_zero (S : Finset ℕ) (z : ℤ) (hs : ∀ p ∈ S, Nat.Prime p)
  (hlocal : ∀ p ∈ S, ↑p ^ 2 ∣ z) (hsize : z.natAbs < squarePrimeSupportModulus S) : z = 0
```

### finite_support_nonzero_bound

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_support_nonzero_bound (S : Finset ℕ) (z : ℤ)
  (hs : ∀ p ∈ S, Nat.Prime p) (hlocal : ∀ p ∈ S, ↑p ^ 2 ∣ z) (hz : z ≠ 0) : squarePrimeSupportModulus S ≤ z.natAbs
```

### finite_defect_zero_certificate

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.finite_defect_zero_certificate (S : Finset ℕ) (a b c : ℕ)
  (hs : ∀ p ∈ S, Nat.Prime p) (hlocal : ∀ p ∈ S, ↑p ^ 2 ∣ focusedFermatDefect a b c)
  (hsize : (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus S) : Fermat7Equation a b c
```

### quadratic_prime_support

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_prime_support (a b : ℕ) (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
  {p : ℕ} (hp : p ∈ (a ^ 2 + a * b + b ^ 2).primeFactors) : Nat.Prime p ∧ p ∣ a ^ 2 + a * b + b ^ 2
```

### quadratic_modulus_dvd_square

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_dvd_square (a b : ℕ) :
  squarePrimeSupportModulus (a ^ 2 + a * b + b ^ 2).primeFactors ∣ (a ^ 2 + a * b + b ^ 2) ^ 2
```

### quadratic_modulus_le_square

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.quadratic_modulus_le_square (a b : ℕ)
  (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0) :
  squarePrimeSupportModulus (a ^ 2 + a * b + b ^ 2).primeFactors ≤ (a ^ 2 + a * b + b ^ 2) ^ 2
```

### full_quadratic_defect_zero_certificate

```lean
DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity.full_quadratic_defect_zero_certificate (a b c : ℕ)
  (hQ0 : a ^ 2 + a * b + b ^ 2 ≠ 0)
  (hsupport : ∀ p ∈ (a ^ 2 + a * b + b ^ 2).primeFactors, ↑p ^ 2 ∣ focusedFermatDefect a b c)
  (hsize : (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus (a ^ 2 + a * b + b ^ 2).primeFactors) :
  Fermat7Equation a b c
```

## Actual public axiom audit

| Declaration | #print axioms |
|---|---|
| squarePrimeSupportModulus | propext, Quot.sound |
| squarePrimeSupportModulus_pos | propext, Classical.choice, Quot.sound |
| squarePrimeSupportModulus_eq | propext, Quot.sound |
| squarePrimeSupportModulus_dvd_iff | propext, Classical.choice, Quot.sound |
| int_zero_of_modulus_size | propext |
| int_nonzero_modulus_bound | propext |
| finite_support_zero | propext, Classical.choice, Quot.sound |
| finite_support_nonzero_bound | propext, Classical.choice, Quot.sound |
| finite_defect_zero_certificate | propext, Classical.choice, Quot.sound |
| quadratic_prime_support | propext, Classical.choice, Quot.sound |
| quadratic_modulus_dvd_square | propext, Classical.choice, Quot.sound |
| quadratic_modulus_le_square | propext, Classical.choice, Quot.sound |
| full_quadratic_defect_zero_certificate | propext, Classical.choice, Quot.sound |

全13宣言は standard-only。非標準公理0。詳細は最終 test07 と audit.json。

## Actual compiler commands / intermediate repairs

cwd `lean/dk_math`。Lake builds は sequential、process-local LEAN_NUM_THREADS=2。
ログは `.lake/build/gtail-step040/NN-build.log`。

| Log | Actual command | Exit | Warnings | Seconds |
|---|---|---|---|---|
| 01 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 0 | 0 | 19.53 |
| 02 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 0 | 0 | 16.36 |
| 03 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 1 | 1 | 15.5 |
| 04 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 1 | 0 | 15.3 |
| 05 | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 0 | 0 | 15.9 |
| 06 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 1 | 0 | 18.32 |
| 07 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectGlobalCapacity` | 0 | 0 | 19.12 |
| 08 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedDefectSquareFirewall` | 0 | 0 | 8.5 |
| 09 | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedPrimeRoute` | 0 | 0 | 8.42 |

- 01: Gate1 finite support / coprimality / signed divisor iff を単独で成功。
- 02: Gate2 generic absolute threshold、nonzero bound、explicit-size Fermat certificate を追加して成功。
- 03: Q membership の generic simp only が第三 conjunct Q≠0 を除去せず type mismatch。
  p が implicit usage のみという style warning1 も発生した。
- 04: simp only の追加調整では同じ mismatch が残った。p := p の指定で warning は解消。
- 05: actual Nat.mem_primeFactors_of_ne_zero hQ0 を使う小さい repair で最終 source が Built。
  数学的仮定は変えず、exit0 / warning0。
- 06: raw decide が primeFactors / finite product の reduction で止まり、large primality checks は
  maximum recursion depth に達した。数値候補が false という結果ではない。
  primeFactors_zero/one は simp、実際の factors の primality は norm_num、
  actual support は primeFactors_mul / Prime.primeFactors と verified product equality で証明した。
  downstream modulus / membership / size tests はこの support certificate で rewrite して decide。
  global resource options や native_decide は使用していない。
- 07: 最終 test が Built、56 examples と公開13 declarations の #check / #print axioms が成功、warning0。
- 08/09: Step039/038 direct regression targets が成功、warning0。既存 target の cached replay を含む。
  source05/test07 の実際の Built と区別する。全 clean all-suite の結果ではない。

別途 actual API probes（すべて exit0 / warning0）:

```sh
LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step040/api-probe.lean > .lake/build/gtail-step040/api-probe.log 2>&1
LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step040/api-probe.lean > .lake/build/gtail-step040/api-probe-final.log 2>&1
LEAN_NUM_THREADS=2 lake env lean .lake/build/gtail-step040/api-probe.lean > .lake/build/gtail-step040/api-probe-all.log 2>&1
```

probes は順に nonzero membership / actual primeFactors composition APIs を追記して実行した。
最終 all log に source-inventory の全 library signatures がある。

## Lean 結果からの気づき・試した命題・実装提案

1. 試した finite aggregation は signed z 一般に成立し、Fermat / focus / primitive inputs を必要としない。
   Finset の distinctness だけでは不十分で、actual prime certificates が coprimality を供給する。
   nonprime overlapping factors4/8 の control でこの違いも確認した。
2. product-divisor iff の forward direction は単なる factor extraction、reverse direction は coprime induction。
   この非対称な proof route を明示できた。collective support を一素数の existential に縮めないことが重要。
3. absolute threshold と converse は既存 Int APIs でそのまま通った。
   m>0 自体は generic lemma の必須仮定ではなく、positive prime modulus usage が自然な application。
   negative Δ にも同じ proof を使え、signed z<m の誤った bound を避けられる。
4. canonical radical-square capacity は Q² の divisor で、Q≠0 のとき upper bound を持つ。
   Q=0 の empty-support convention は modulus1なので le-square に非零仮定が必要。
   この edge case を API と examples の両方で検証した。
5. actual radical defining expression との橋は support_factorization 一つで通った。
   新 general radical owner や ABC conjecture の仮定は不要だった。
   raw primeFactors reduction の失敗も、値を変えず既存 factor-product certificates で修正できた。
6. 二つの natural defect controls は all-prime support と strict size の両方を欠く。
   これらから「all-support certificate が false」と主張することはできない。
   他方 z=±36 は all support alone が zero を強制しない独立 control となった。
7. M_Q≤Q² はこの direct threshold strategy の容量上限であり、uniform ∣Δ∣ bound ではない。
   実際の二例では最大の potential M_Q=Q² より defect が大きいが、
   あらゆる non-Fermat data で size strategy が不可能だという theorem は得ていない。
8. 次の実装候補は、weak actual source assumptions から collective prime coverage を導く theorem と、
   independent magnitude bound を導く theorem を別契約で評価すること。
   どちらも Δ=0/hEq を仮定して trivial に供給しただけなら新情報にならない。
   今回その theorem は実装していない。higher q-adic assumptions や conjectural ABC inequality で
   modulus を勝手に強めることもしない。

## Scientific frontier / old reconstruction contract

[frontier-040.md](frontier-040.md) の表に selected support、collective support、capacity、extra size、
actual Tail receiver / Gap ratio と signed provider の境界を記載した。
この conditional zero criterion は独立 FLT7 impossibility theorem ではない。

AwayDescentClosureProvider の exact field は
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd`。
nextX/Y/Z、new CounterexamplePack、AwayValuationTransferPacket も必要。
RamifiedSignedRootDepthPacket は balanced signed roots、coprimality、gap/quotient identities、
7-unit guards と normalizedEquation を要求する。
modulus-size implication はこれらの recursive / signed fields を構成しない。

Outcome B として Step040 を停止する。new global source-derived support/magnitude restriction、
signed reconstruction、new primitive counterexample、away descent、unconditional FLT7 closure は得ていない。

## 最終依存・書式・履歴監査

- 公開13 declarations / examples56、standard-only axioms。final source05/test07/regression08/09 は exit0 / warning0。
- 新 source/test の comments/strings を除く forbidden-token scan は
  sorry / admit / axiom / unsafe / native_decide / set_option / False.elim 全件0。
  License header と import 後の file print / code style を検査した。
- production closure8955 modules（local175）、test closure8956（local176）、
  local union176 vertices の DAG cycle0。
  neutral GTailSevenRealTraceResidue closure1907（local20）の FLT reachability0、
  到達する27 neutral Lib owners の独立 closure でも FLT reachability0。
- ABC.Rad、Seven facade、SevenRamifiedFusionGlobalOrientedPrimeFactorization、
  Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge、
  SevenRamifiedFusionCyclotomicDegreeSixDomain、SevenRamifiedFusionOrientedCarrierValuationOwnership は closure にない。
  old signed modules は既存の推移的依存として残り、新 direct imports / packet references はない。
- saved Step039 module set との比較は新 owner 一つ追加、削除0。
  historical comparison であり old logs を今回の fresh build として数えない。
- proof-contract-audit は hsize / collective support の explicit signatures、equation-as-input0、
  packet / old conditional-route consumer0 と named ABC.Rad import0 を確認した。
- existing tracked owners / historical reports/reviews は変更0。ROADMAP は既存 HEAD bytes の保持と追記のみ。
  新5ファイルと追記の newline / tab / trailing whitespace、git diff --check は成功。

証拠: `.lake/build/gtail-step040/` の runs.json、build/probe logs、signatures.json、
proof-contract-audit.json、imports.json、audit.json、import-impact.json、workspace-audit.json。
