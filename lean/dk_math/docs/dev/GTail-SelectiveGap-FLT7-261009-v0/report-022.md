# Step 022 — exact six-root scalar ideal recovery

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `568d80ffb777f80f4409ef5d237b9be881f0fcbe`.
**Step022 COMPLETE / Outcome B**。mandatory intersection gate と optional product gate がともに成功。

## Checked result and proof gates

既存の actual degree-six ring `SevenCyclotomicDegreeSixInt.Ring` と additive equivalence
`coordinates : Ring ≃+ (Fin 6 → ℤ)` をそのまま使った。座標順序は
`(re.fst,re.snd,re.thd,im.fst,im.snd,im.thd)`。
新 carrier、ring equivalence、signed packet、Fermat equation の仮定は追加しない。

Phase1: instruction の M/N は target data として扱い、六係数 map とその逆 map の両合成を
任意 `CommRing A` について `fin_cases` / `ring` で証明した。
行列 determinant=−1 自体の宣言は作らず、未検証の determinant 値も使わない。
この inverse は整数係数なので、特徴数によらず residue coordinates を復元できる。
実際の RingHom 評価を、任意 signed coordinates から作った degree≤5 polynomial の評価と同一視。
`s⁻¹=s⁶` と非identity seventh root の七項和零を使う `linear_combination` が値等式を検証する。
外部 symbolic calculation は差の因子探索に限り、証明の前提には入れない。
Phase1-only build `04-build.log` が exit0。

Phase2: `sixSlotRoot_injective` と Mathlib の field polynomial root-count theorem により、
六根で評価零なら degree≤5 polynomial 自体が零。六係数を抽出し、証明済み integral inverse で
元の六座標の cast-zero を復元する。逆向きも actual polynomial/value identity から証明。
これは任意 z に対する iff であり、q43 の有限計算による代用ではない。

Phase3: additive coordinates の乗法互換性は仮定せず、actual quadratic / real-cubic multiplication
から `coordinates_natCast_mul` を別途証明。
各座標の整数商を `coordinates.symm` で actual ring element に戻し、
scalar principal ideal membership iff coordinate divisibility を任意 q,z に証明した。
cast-zero/divisibility iff と ideal extensionality により exact intersection=(q)。
この mandatory gate は `05-build.log`、exit0（16.42秒）で先に成功。

Phase4: 上記成功後だけ optional product を追加。
Step021 の pairwise sup=top を `Ideal.isCoprime_iff_sup_eq` で IsCoprime family にし、
`Ideal.prod_eq_iInf_of_pairwise_isCoprime` の有限 product theorem を適用。
`Finset.univ` bounded-iInf を `Finset.mem_univ` / `iInf_true` で橋渡しし、
既に検証した intersection equality に接続した。`06-build.log`、exit0。

結論は prime q と supplied `r≠0`, `r^7=1`, `r≠1` の下で
`(⨅ i : Fin 6, K_i) = (∏ i : Fin 6, K_i) = cyclotomicScalarIdeal q`。
Step021 の歴史的「未証明」は書き換えず、今回その欠落を閉じた。

## All new public signatures

Namespace `DkMath.FLT.Seven`。4 definitions、11 theorems、計15宣言。以下は実装から抽出。

```lean
def sixPowerCoefficients {A : Type*} [CommRing A] (v : Fin 6 → A) : Fin 6 → A
```

```lean
def sixPowerCoordinates {A : Type*} [CommRing A] (w : Fin 6 → A) : Fin 6 → A
```

```lean
theorem sixPowerCoordinates_coefficients {A : Type*} [CommRing A] (v : Fin 6 → A) :
    sixPowerCoordinates (sixPowerCoefficients v) = v
```

```lean
theorem sixPowerCoefficients_coordinates {A : Type*} [CommRing A] (w : Fin 6 → A) :
    sixPowerCoefficients (sixPowerCoordinates w) = w
```

```lean
theorem sixPowerCoefficients_intCast (q : ℕ) (v : Fin 6 → ℤ) (i : Fin 6) :
    ((sixPowerCoefficients v i : ℤ) : ZMod q) =
      sixPowerCoefficients (fun j => (v j : ZMod q)) i
```

```lean
noncomputable def sixPowerPolynomial (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) : Polynomial (ZMod q)
```

```lean
theorem sixPowerPolynomial_coeff (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) (j : Fin 6) :
    (sixPowerPolynomial q z).coeff j.val = ((sixPowerCoefficients (coordinates z) j : ℤ) : ZMod q)
```

```lean
theorem sixPowerPolynomial_natDegree_le (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) :
    (sixPowerPolynomial q z).natDegree ≤ 5
```

```lean
theorem evalCyclotomic_eq_sixPowerPolynomial {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 z = (sixPowerPolynomial q z).eval s
```

```lean
theorem mem_all_sixRootKernel_iff_coordinates_zero {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    (∀ i : Fin 6, z ∈ sixRootKernel r hr0 hr7 hr1 i) ↔
      ∀ j : Fin 6, (coordinates z j : ZMod q) = 0
```

```lean
def cyclotomicScalarIdeal (q : ℕ) : Ideal SevenCyclotomicDegreeSixInt.Ring
```

```lean
theorem coordinates_natCast_mul (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) (j : Fin 6) :
    coordinates ((q : SevenCyclotomicDegreeSixInt.Ring) * z) j = (q : ℤ) * coordinates z j
```

```lean
theorem mem_cyclotomicScalarIdeal_iff (q : ℕ) (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ cyclotomicScalarIdeal q ↔ ∀ j : Fin 6, (q : ℤ) ∣ coordinates z j
```

```lean
theorem iInf_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (⨅ i : Fin 6, sixRootKernel r hr0 hr7 hr1 i) = cyclotomicScalarIdeal q
```

```lean
theorem prod_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∏ i : Fin 6, sixRootKernel r hr0 hr7 hr1 i) = cyclotomicScalarIdeal q
```

## Source/API and overlap audit

[Source inventory](source-inventory-022.md) に実際の carrier、評価式、M/N、旧 packet owners、Mathlib API を記載。
主要 API は `Polynomial.finsetSum_coeff`, `Polynomial.coeff_monomial`, `Fin.val_inj`,
`Polynomial.natDegree_sum_le_of_forall_le`, `Polynomial.natDegree_monomial_le`,
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Ideal.mem_span_singleton`, `Ideal.mem_iInf`,
`Ideal.isCoprime_iff_sup_eq`, `Ideal.prod_eq_iInf_of_pairwise_isCoprime`。
root count は injective Fin6→field の全評価零と natDegree<cardFin6 を明示的に要求する。

旧 global oriented / prime-load / conjugate-pair owners は supplied signed address/support packet の別契約。
既存 `realPrimeFiberIdeal_eq_conjugateProduct` は packet-specific な二核積の証明済み theorem。
その結果を bare-root 六核積に読み替えず、今回の source には import しない。

## Numerical and negative calibration — 24 examples

- 整数の arbitrary vector と ZMod43 の arbitrary vector で inverse compositions を受信。
  production の両 inverse theorem は任意 CommRing を量化する。
- Signed z=`⟨⟨−2,3,−4⟩,⟨5,−6,7⟩⟩` の座標と六係数
  `[-5,13,2,5,-2,-6]`、integer-to-residue coefficient compatibility を検証。
  六根 `[11,35,41,21,16,4]` で polynomial values は `[17,29,11,18,34,21]`。
  別 example で六つすべての actual RingHom values と polynomial values の等式を検証。
- q43 の arbitrary z について all-six membership iff 六整数座標の43 divisibility。
  intersection/product equality は generic theorem の適用であり、数値 `decide` による ideal equality ではない。
- embedded scalar43 は `(43)` と全六核に所属。
  `W=ofReal(-43)+zeta*ofReal(86)` は signed literal carrier と等しく、
  六整数座標が43の倍数であり `(43)` と全六核に所属。
- `F(9,4)` は `K_i` に属する iff i=0。そのため all-six intersection、scalar(43)、six-ideal product のいずれにも属さない。
- q13 Gap support では Tail support がなく、ratio=1。
  q7 では非identity seventh root が存在しない。root-free splitting は結論しない。
- 別 example `¬ Fermat7Equation 5 8 9` が通り、q43 の局所分解を FLT counterexample と混同しない。

## Exact build evidence

cwd=`/home/deskuma/develop/lean/dkmath/lean/dk_math`。
各行の command は `LEAN_NUM_THREADS=2 lake build <target>`。逐次 incremental focused builds。
P=`DkMath.FLT.Seven.GTailCyclotomicSixRootInterpolation`、
T=`DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation`、
R21=`DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit`、
R20=`DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress`。
ログは workspace-local ignored `.lake/build/gtail-step022/`。
正確な commands / exits / elapsed times は同ディレクトリ `runs.json`。

| Log | Target | Exit | Seconds | Gate |
|---|---|---:|---:|---|
| 01-build.log | P | 1 | 15.5 | cast / polynomial construction repair |
| 02-build.log | P | 1 | 15.89 | coefficient simplification repair |
| 03-build.log | P | 1 | 15.9 | nonexistent API attempt removed |
| 04-build.log | P | 0 | 15.72 | Phase1 passed |
| 05-build.log | P | 0 | 16.42 | mandatory intersection passed |
| 06-build.log | P | 0 | 16.2 | optional product passed |
| 07-build.log | T | 1 | 15.7 | numeric normalization repair |
| 08-build.log | T | 1 | 14.43 | noncomputable direct decide rejected |
| 09-build.log | T | 1 | 17.15 | sum associativity repair |
| 10-build.log | T | 0 | 16.42 | 24 examples / all public axioms passed |
| 11-build.log | R21 | 0 | 7.97 | Step021 regression passed |
| 12-build.log | R20 | 0 | 8.25 | Step020 regression passed |

初期失敗は残して記録する。01: generic map の整数値を明示せず ZMod 型に推論された cast、
Polynomial noncomputable construction、monomial degree lemma の coefficient 引数を修正。
02: broad simp が monomial0 を polynomial intCast に変え、coefficient 抽出が停滞。
03: 推測した `Polynomial.C_intCast` は存在せず削除。
最終 proof はまず `finsetSum_coeff` / `coeff_monomial` だけを適用し、`Fin.val_inj` で delta sum を処理する。
07: numeric literal cast と cubic signed casts を明示、不要 binder を修正。
08: noncomputable polynomial evaluation への直接 `decide` は停止したので、computable 六項式を `decide` し
polynomial evaluation へ `simpa` で接続。09: Fin sum の右結合と六項式の左結合の不一致を
`add_assoc` で修正。最終06/10ログは warning0。証明を弱めず、recursion / heartbeat options を追加しない。

## All public axiom outputs

最終 test build の15件を下記に転記。標準論理公理以外、特に `sorryAx` はない。
新ファイルの検査とこの15件の依存公理結果は、既存全 repository の axiom-free 性を主張しない。

```text
sixPowerCoefficients: [propext]
sixPowerCoordinates: [propext]
sixPowerCoordinates_coefficients: [propext, Classical.choice, Quot.sound]
sixPowerCoefficients_coordinates: [propext, Classical.choice, Quot.sound]
sixPowerCoefficients_intCast: [propext, Classical.choice, Quot.sound]
sixPowerPolynomial: [propext, Classical.choice, Quot.sound]
sixPowerPolynomial_coeff: [propext, Classical.choice, Quot.sound]
sixPowerPolynomial_natDegree_le: [propext, Classical.choice, Quot.sound]
evalCyclotomic_eq_sixPowerPolynomial: [propext, Classical.choice, Quot.sound]
mem_all_sixRootKernel_iff_coordinates_zero: [propext, Classical.choice, Quot.sound]
cyclotomicScalarIdeal: [propext, Quot.sound]
coordinates_natCast_mul: [propext, Classical.choice, Quot.sound]
mem_cyclotomicScalarIdeal_iff: [propext, Classical.choice, Quot.sound]
iInf_sixRootKernel_eq_scalarIdeal: [propext, Classical.choice, Quot.sound]
prod_sixRootKernel_eq_scalarIdeal: [propext, Classical.choice, Quot.sound]
```

## Dependency, preservation and style checks

production の direct import は Step021 owner だけ、test は今回 owner だけ。
comment/string を除去した import graph を local sources / Mathlib sources で追跡。
neutral `GTailSevenRealTraceResidue` closure は1907 modules（local20）、FLT dependency0。
今回 production は8929（local149）、test は8930（local150）。local union150 vertices の DFS cycle0。
外部 source のない依存名は leaf として数え、この件数を package-wide cycle proof としない。
full `DkMath.FLT.Seven` facade と old global oriented factorization owner は新 owner/test closure に含まれない。
production は Step021 から今回 owner 一つの追加。test は旧 Step021 test の別 ramified calibration import を含めず、
closure が旧 test の8937/local157より小さい。これは dependency 件数の比較であり速度向上の証明ではない。

新二 Lean ファイルは既存の MIT2026 / authors header、import後 `#print "file: ..."`、namespace と2space styleを維持。
comment/string 除去後の whole-word `sorry/admit/axiom/unsafe/native_decide` と `False.elim` は0、`set_option` も0。
tracked changes は ROADMAP への post021 append のみ。source ring、旧 signed owners、root drivers、facades、historic ledger は変更なし。
`git diff --check` と新ファイルの no-index whitespace check を実施。

## Lean-derived observations and bounded proposals

1. **Confirmed:** M/N の両合成は任意 CommRing で成立するので、coordinate change のための q-unit/determinant premise は不要。
   root count 部分には prime q と六 distinct supplied roots が必要であり、この二層を混同しない。
2. **Confirmed:** scalar lattice iff 自体は prime や root を要求せず、任意 natural q と signed element を扱う。
   q=0 も署名上含む。今回 q=0 専用の追加 numeric example は実施していない。
3. **Confirmed:** selective Tail support は六核積への membership を意味しない。
   q43 の F は選択核には入るが scalar43 は割り切らない。scalar ideal equality は任意 z の
   all-six support を復元する theorem であり、single-slot support を強化する theorem ではない。
4. **Proposal only / unproved here:** 今回の all-six kernel equality と既存 surjective residues を使った
   actual quotient `R/(q)` から六 residue factors への CRT equivalence が次の独立 API 候補。
   その具体的 RingEquiv、全 prime-ideal 分類、個別 K_i の principalization は実装していない。

今回の結果は actual degree-six carrier の **conditional classical split-prime decomposition / Outcome B**。
degree-two Eisenstein scalar ideal、ℤ の(q)、degree-six の(q) は別型であり transfer は未証明。
exact ideal-adic valuations、unit-power/class extraction、signed-depth packet construction、
next primitive tuple、FLT7 descent / unconditional closure は結論しない。**STOP after Step022**。
