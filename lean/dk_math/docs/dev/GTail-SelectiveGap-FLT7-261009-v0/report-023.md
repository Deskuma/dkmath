# Step 023 — exact GTail six-factor reconstruction

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `400e6079a95a491605dcf798c86eadd74a20e24c`.
**Step023 COMPLETE / Outcome B**, including optional inverse-exponent incidence.

## Checked endpoint and proof method

既存 `R=SevenCyclotomicDegreeSixInt.Ring` で、新 factor は
`F_i(c,g)=(c+g:R)−ζ^(i.val+1)*(c:R)`。
`F_0=gtailCyclotomicLinearFactor` を actual natural cast / ofReal equality で証明。
任意 X,Y:R の homogeneous identity と、任意自然 c,g の endpoint

```text
∏ i:Fin6, F_i(c,g) = ((GTail 7 1 g c : ℕ) : R)
```

が Lean で成立。q、prime、root、positivity、g≠0、q-unit、Tail divisibility、Fermat equation は
この endpoint の前提にない。

Phase1: actual quadratic relation `ζ²−tζ+1=0` と cubic relation `t³+t²−2t−1=0`
(t=ofReal(alpha−1)) の explicit linear_combination が七項和零を証明。
private generic CommRing theorem で七項和零を仮定して六因子を Fin product として展開し、
27-term integer polynomial multiplier × 七項和零 により homogeneous shell と一致させる。
certificate の探索は Sympy の exact polynomial division、certificate の証明は Lean の
`linear_combination`。ζ−1 を非零とみなして消去する議論や、numerical field evaluations による代用はない。
Domain instance / fraction-field extension を追加 import する必要はなかった。

Phase2: 既存 `GTail_one_eq_GTailCyclotomicShell` は CommSemiring の recurrence identity。
自然数でこれを受信し、range7/Fin7 の有限和を展開して `ring` で逆順の shell に一致させる。
g の消去を行わないので g=0 も最初から含む。Nat casts を sum/mul/pow と交換して
Phase1 と接続する。**Primary gate は01-build.logで exit0**。その後にのみ optional incidence を追加した。

Phase3: actual RingHom sends F_i to `(c+g)−s^(i+1)*c`。
canonical r=(c+g)/c、q∤c、q∤g、q|GTail の下で nonzero c を正当に消去し、
`orderOf r=7` と `IsOfFinOrder.pow_inj_mod` により

```text
F_i ∈ K_j ↔ (i.val+1)*(j.val+1)%7=1 ↔ j=sixInverseSlot i
sixInverseSlot = [0,3,4,1,2,5]
```

を generic prime q について証明。36-case lookup は Fin6 exponent arithmetic だけであり q43 を仮定しない。
置換の involutivity も checked。各 factor は唯一の supplied kernel に属し、残り五つに属さない。
署名に q|Q、Fermat equation、signed packet はない。

## All new public signatures

Namespace `DkMath.FLT.Seven`。2 definitions、10 theorems、計12宣言。以下は actual source から抽出。
private algebraic certificate lemmas は public API 数に含めない。

```lean
def gtailCyclotomicFactor (c g : ℕ) (i : Fin 6) : SevenCyclotomicDegreeSixInt.Ring
```

```lean
theorem gtailCyclotomicFactor_zero (c g : ℕ) :
    gtailCyclotomicFactor c g 0 = gtailCyclotomicLinearFactor c g
```

```lean
theorem zeta_geom_sum :
    1 + zeta + zeta ^ 2 + zeta ^ 3 + zeta ^ 4 + zeta ^ 5 + zeta ^ 6 = 0
```

```lean
theorem prod_six_zeta_factors_eq_shell (X Y : SevenCyclotomicDegreeSixInt.Ring) :
    (∏ i : Fin 6, (X - zeta ^ (i.val + 1) * Y)) =
      ∑ j : Fin 7, X ^ (6 - j.val) * Y ^ j.val
```

```lean
theorem GTail_seven_one_eq_homogeneous_sum (c g : ℕ) :
    GTail 7 1 g c = ∑ j : Fin 7, (c + g) ^ (6 - j.val) * c ^ j.val
```

```lean
theorem prod_six_gtailCyclotomicFactor_eq_GTail (c g : ℕ) :
    (∏ i : Fin 6, gtailCyclotomicFactor c g i) =
      ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring)
```

```lean
theorem evalCyclotomic_gtailFactor {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (c g : ℕ) (i : Fin 6) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 (gtailCyclotomicFactor c g i) =
      ((c + g : ℕ) : ZMod q) - s ^ (i.val + 1) * (c : ZMod q)
```

```lean
def sixInverseSlot (i : Fin 6) : Fin 6
```

```lean
theorem sixInverseSlot_involutive : Function.Involutive sixInverseSlot
```

```lean
theorem six_inverse_exponents (i j : Fin 6) :
    (i.val + 1) * (j.val + 1) % 7 = 1 ↔ j = sixInverseSlot i
```

```lean
theorem gtailCyclotomicFactor_mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailCyclotomicFactor c g i ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) j ↔ (i.val + 1) * (j.val + 1) % 7 = 1
```

```lean
theorem gtailCyclotomicFactor_unique_slot {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailCyclotomicFactor c g i ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) j ↔ j = sixInverseSlot i
```

## Source overlap and exact APIs

[Source inventory](source-inventory-023.md) に actual carrier、sign/cast、domain と overlap を記録。
`GTailCyclotomicShell` の既存 theorem を再利用し、代用 polynomial の定義で original GTail を置き換えない。
QR bridge の `primitiveRoots_product_poly_eq_shell` は Field input の MvPolynomial factorization。
Mathlib `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots` は CommRing+IsDomain と primitive root の API。
actual `SevenRamifiedFusionCyclotomicDegreeSixDomain.ringIsDomain` は存在するが、新 owner はそれを import しない。
Kummer `linear_factor_mul_eq_sub_pow` は一因子×幾何和=冪差であって今回の六因子 shell とは別の契約。
これら重い owners の duplicate wrapper / signed packet adaptation を作らない。

今回使う names: `Fin.prod_univ_succ`, `Fin.sum_univ_succ`, `Finset.sum_range_succ`,
`GTail_one_eq_GTailCyclotomicShell`, `map_sub`, `map_mul`, `map_pow`, `map_natCast`,
`Nat.cast_sum`, `Nat.cast_mul`, `Nat.cast_pow`, `ZMod.natCast_eq_zero_iff`,
`div_mul_cancel₀`, `mul_left_inj'`, `pow_mul`, `orderOf_pos_iff`,
`IsOfFinOrder.pow_inj_mod`, `seventhRoot_orderOf`。

## Calibration and edge cases

31 examples（全36 cross-values を量化する一 example を含む）。

- 任意 X,Y の actual R equality と任意 c,g の natural endpoint を generic theorem として受信。
- q43,c9,g4: `GTail 7 1 4 9=14491387=43*337009`。
  actual ring の六 factor product は scalar14491387。
  `F_0=13−9ζ`、F0∈K0、F0∉K1。
- 六 receiver permutation `[0,3,4,1,2,5]`、unique j と remaining-five exclusion を実検証。
  以下の全36 entries は actual RingHom evaluation theorem から computable residue expression に戻して `decide`。
  columns は roots `[11,35,41,21,16,4]`、rows は factor indices0..5。

| Factor i | K0 root11 | K1 root35 | K2 root41 | K3 root21 | K4 root16 | K5 root4 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 42 | 31 | 39 | 41 | 20 |
| 1 | 42 | 39 | 20 | 0 | 31 | 41 |
| 2 | 31 | 20 | 42 | 41 | 0 | 39 |
| 3 | 39 | 0 | 41 | 42 | 20 | 31 |
| 4 | 41 | 31 | 0 | 20 | 39 | 42 |
| 5 | 20 | 41 | 39 | 31 | 42 | 0 |

scalar GTail は scalar ideal(43) と全六核に所属。一方 F0 は scalar ideal(43) に属さない。
別 example で `(∏ i,K_i)=cyclotomicScalarIdeal43` を Step022 generic theorem から受信。
これは element product と ideal product を別々に表示する検証であり、異なる型の有限積同士の等式ではない。
`¬ Fermat7Equation 5 8 9` も checked。

端点は arbitrary c に対して `GTail 7 1 0 c=7*c^6` と対応する factor product を検証。
(c,g)=(0,1) の product=1、(1,0) は7、(0,0) は0。
(0,0) の全 factor が0で、全 K_j に属するため、unit guard を外した unique support は false。
q13 Gap example は ratio1 で q∤Tail。q7 には非identity scalar seventh root がない。
それでも integral source の unconditional product theorem は (c,g)=(7,1) に適用できる。

## Exact build record and intermediate repair

cwd=`/home/deskuma/develop/lean/dkmath/lean/dk_math`。
process-local `LEAN_NUM_THREADS=2`、逐次 incremental focused builds。
全 clean build を行わず、追加 heartbeat/recursion/linter options は導入しない。
logs と exact command/exits は ignored workspace `.lake/build/gtail-step023/` の `runs.json`。

P=`DkMath.FLT.Seven.GTailCyclotomicTailFactorProduct`
T=`DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct`
R22=`DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation`
R21=`DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit`

各 command は `LEAN_NUM_THREADS=2 lake build <target>`。

| Log | Target | Exit | Seconds | Result |
|---|---|---:|---:|---|
| 01-build.log | P | 0 | 15.37 | mandatory exact element product passed |
| 02-build.log | P | 1 | 15.08 | incidence cancellation API direction repaired |
| 03-build.log | P | 0 | 15.65 | full source with incidence passed |
| 04-build.log | T | 0 | 18.5 | 31 examples / all12 public axioms passed |
| 05-build.log | R22 | 0 | 8.3 | Step022 regression passed |
| 06-build.log | R21 | 0 | 8.17 | Step021 regression passed |

02 の失敗は cancellation name の左右方向。
`mul_right_inj' hc0` は `c*a=c*b` を扱うが、target は `a*c=b*c`。
source の actual `mul_left_inj' hc0` に修正し03で成功。数学的仮定/結論の変更はない。
最初の Sympy certificate text を読みやすい multiline/spacing に整形し、03で再検証。
03/04 の final source/test logs は warning0。q43 table の草案転記は外部整数 modular calculation と照合し、
Lean test 実行前に末尾三行を訂正。最終36 entries はすべて Lean で再検証した。

## All public axiom outputs

04-build.log の全12 public declarations。標準公理だけで `sorryAx` / fresh assumptions はない。

```text
gtailCyclotomicFactor: [propext, Quot.sound]
gtailCyclotomicFactor_zero: [propext, Quot.sound]
zeta_geom_sum: [propext, Classical.choice, Quot.sound]
prod_six_zeta_factors_eq_shell: [propext, Classical.choice, Quot.sound]
GTail_seven_one_eq_homogeneous_sum: [propext, Classical.choice, Quot.sound]
prod_six_gtailCyclotomicFactor_eq_GTail: [propext, Classical.choice, Quot.sound]
evalCyclotomic_gtailFactor: [propext, Classical.choice, Quot.sound]
sixInverseSlot: [propext]
sixInverseSlot_involutive: [propext, Classical.choice, Quot.sound]
six_inverse_exponents: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_mem_sixRootKernel_iff: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_unique_slot: [propext, Classical.choice, Quot.sound]
```

## Import, source preservation and style audit

Direct imports は production: Step022 interpolation と GTailCyclotomic、test:今回 owner のみ。
comment/string 除去後の import graph を local/Mathlib sources で追跡。
neutral `GTailSevenRealTraceResidue`:1907 modules/local20、FLT dependencies0。
production:8931/local151、test:8932/local152。local union152 vertices の DFS cycle0。
外部 source のない依存名は leaf として数える。package-wide cycle-free claim ではない。
Step022 production closure からの local delta は今回 owner と既存 GTailCyclotomic の二つ。
full FLT.Seven facade、Domain、global oriented factorization、Kummer principalization、QR bridge の各 owner は
今回の owner/test closure に含まれない。既存 heavy degree-six dependencies 自体は残る。

新二 Lean ファイルの MIT2026/Authors header、import後 file print、namespace、2space style を維持。
comment/string 除去後 `sorry/admit/axiom/unsafe/native_decide` whole-word / `False.elim` / `set_option` は0。
tracked modifications は ROADMAP の post022 append のみ。旧 source ring / signed owners / drivers / facades / ledger は不変。
`git diff --check` と新四ファイルの no-index whitespace check を実施。
この audit と新 public declaration axiom outputs は repository 全体の axiom-free 性を主張しない。

## Lean-derived observations and bounded implementation proposals

1. **Confirmed:** 六因子恒等式のためには actual integral relations から得た七項和零で足りる。
   新 Domain import、ζ−1 の非零因子性、field evaluation reconstruction を必要としない。
   これは今回 private generic `product_of_geom` の証明で確認した限定的な algebraic fact。
2. **Confirmed:** element product は unconditional、kernel incidence は q-local guarded result。
   特に g=0 の factor product=7c⁶ と、r=1 が incidence 仮定を満たさないことは両立する。
   q7 の scalar-root不在も integral source factorization を妨げない。
3. **Confirmed:** inverse index permutation は involution。i=j の diagonal support は i=0,5 に限られ、
   i=1 などの diagonal cross-value は非零。signed packet の orientation とは独立の有限指数現象。
4. **Proposal only / unproved here:** 今回 factors の principal ideals の積=span{GTail} を一般 finite
   principal-product API で受信するのは小さい typed follow-up 候補。
   ただし各 span{F_i}=K_j や exact K-adic exponents は別の未証明事項。
5. **Proposal only / unproved here:** ζ↦ζ^k の actual integral automorphism を構成できれば、
   六 factor family の Galois covariance を source equality として検証できる。
   今回 root powers の permutation だけから integral automorphism を仮定しない。

**Outcome B**: original GTail と actual integral six-factor product の正確な再構成、および guarded inverse-index incidence。
exact valuations、individual factor/kernel principalization、class/unit-power extraction、integral Eisenstein→degree-six map、
signed packet reconstruction、next primitive counterexample、FLT7 descent / unconditional closure は結論しない。
**STOP after Step023**。
