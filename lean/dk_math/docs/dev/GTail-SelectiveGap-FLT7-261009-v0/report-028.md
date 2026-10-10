# Step028 — native GTail second Hensel digit

2026-10-10. **COMPLETE / Outcome B**.
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `126f7d2488fd405176a19e88bfb8fa2d71e8c388`。
review027/report027/source-inventory027 を確認。review は static inspection、独立 rebuild ではない。

## Verified native endpoint

prime q、natural c,g、q∤c、q∤g、q²∣GTail 7 1 g c のもとで、

```text
∃! t : Fin q, q³ ∣ GTail 7 1 (g+q²*t.val) c.
```

既存 `PolynomialHenselDigit.existsUnique_polynomial_powLift_digit` を
P=tailShellPoly(c:ℤ)、x=cast(c+g)、k=2 に instantiate した thin native adapter。
新しい一般 Hensel theorem、Taylor quotient、all-k induction は実装していない。
一意性の範囲は Fin q（0≤digit<q）、natural digits 全体では residue class が一意。

Optional strengthening も checked:

```text
q³ ∣ T_c(g+q²*d) ↔ (T_c(g)/q² : ZMod q)+(d:ZMod q)*D=0,
D=G_c'(c+g).
```

この iff は prime q と q²∣T のみで成立し、c/g unit guard は derivative非零と唯一性に使う。
別の δ₂ definition は導入していない。q43 residue characterization は同じ iff を使い、
Fin43 uniqueness theorem の witness と整合することを tests で確認。

## Carrier-correct transport and reuse

`gtail_second_shift_eval` は任意 natural q,c,g,d、zero endpointsを含む。
x+(q:ℤ)²*d を cast(c+(g+q²*d)) に ring で変換し、既存 `tailShellPoly_eval_nat` に接続。
q²|T は exact_mod_cast で integer polynomial supportにする。
q|T は `dvd_pow_self` と transitivity。prime assumption はこの二 support adapter には不要。

Integer derivative nondivisibility は `ZMod.intCast_zmod_eq_zero_iff_dvd` による仮定の zero cast、
Step027 `gtailDerivativeInt_cast`、`gtail_shell_derivative_ne_zero` の contradiction。
integer polynomial と ZMod polynomial を definally equal として扱わない。
q≠7 は以前の canonical nonidentity root の結果に含まれ、新 premise は追加しない。

Per-digit `gtail_second_lift_predicate` により integer eval divisibility と actual native GTail predicate を同値にする。
Existing ∃! の exponent 2+1 を typed intermediate statement の3へ固定し、
`simpa only` で **same native predicate** の existence/uniqueness を取得。

Optional linear iff は既存 `polynomial_powLift_iff (k:=2)` を直接使用。
`Int.natCast_ediv` と `Nat.cast_pow` により整数商 P.eval x/(q:ℤ)² を natural quotient T/q² に transport。
この nonnegative cast quotient identity 自体は hT2 なしでも正しいが、lift iff は既存 theorem の exact support premise を保持。
最後に integer divisibility を ZMod zero に変換し、Step027 derivative cast を適用。
ZMod(q³) の q²を unitとして除算する手順はない。

Second shift unit/ratio/derivative は Step027 APIs に d'=q*d を渡し、pow_two/mul_assoc だけで接続。
Actual K² receiver は concrete regression として保持。新しい K³ predicate/theorem は実装していない。

## Decisive q43 calibration

28 new examples と private checked calibration lemmas:

| Stage | Starting gap | Correction residue | New gap | Checked scalar support |
|---|---:|---:|---:|---|
| Step027 first digit | 4 | 27 mod43 | 1165 | 43²∣T(1165) |
| Step028 second digit | 1165 | 17 mod43 | 32598 | 43³∣T(32598), 43⁴∤T(32598) |

- T(1165)=2638461449052811747、43² support、T(1165)/43² mod43=40 を decide。
- derivative28 は Step026 generic derivative formula から取得。numeric quotient は div_eq_iff 後の multiplication check。
- 40+17*28=0 mod43 を decide。
- `lift17` は new native linear iff → generic polynomial_powLift_iff を通して 43³ support を証明。
  巨大 T(32598) の直接 decide だけで lift theorem を代用していない。
- `existsUnique_gtail_second_digit` から得た generic unique witness と lift17 を合わせ、
  全 d:Fin43 の lift predicate iff d=17 を証明。d=16、0 の exclusion はこの uniqueness proof による。
- 全 natural d の lift predicate iff cast(d)=17 を new linear iff と nonzero28 から検証。
  d=60 でも lift、同じ residue class17。natural digitそのものの一意性ではない。
- q∤32598、ratio11、derivative at32607=28 は generic shift adapters から取得。
- lift17 の 43³ supportから43² support、Tail supportを得て、Step025 generic theorem に入力。
  全六 actual F_i(9,32598)∈K_(sixInverseSlot i)²。
- 43⁴∤T(32598) は separate decide regression。これは **natural scalar** の exact depth3 の observation。
  これを individual ideal exact depth3 や K³ equalityに読み替えない。
- Step027 first residue27 / g1 second supportの chainを新 testでも検証。
- q=0,c=0,g=0 の raw eval bridges、q7 nonidentity seventh-root absence、q13 missing Tail support、
  zero gap unit failure、a5,b8,c9 の Fermat7Equation false をチェック。

## Lean-derived observations and implementation proposals

今回の bridge で、同じ mod43 ratio11 / derivative28 のまま二つの correction stages を進められることが明確になった。
各 stage の quotient residue は18→40に変わり、correction residue は27→17に変わる。
有限体の simple root data だけで correction digit を決めるのではなく、現在の scalar quotient residue も必要。

Natural d=17と60は違う shifted source elements を与えるが、同じ finite next-digit residue class。
Fin q の unique witness と unrestricted natural digit predicate を別の量化範囲で記述することが有用。

既存 neutral owner の generic finite-depth mechanism の再利用により、新しい証明は cast/guard/predicate adapters に限定できた。
新 mathematical discovery ではなく native sourceへの bounded connectionとして Outcome B。

実装提案（未実施）: Fin q witness を呼び出し側で具体化する必要が増えた場合、
既存 unique witnessから選択した代表元と linear iff の一致を示す小さい adapter を設けられる。
今回は separate δ₂ definition が不要なので追加しなかった。
将来 K³ 等へ進む際は scalar divisibility と actual degree-six ideal powers の別証明が必要。
今回の scalar exact depth3 regressionはその証明を提供しない。

## Public signatures (10 theorems)

Namespace `DkMath.FLT.Seven`。実装から抽出。

```lean
theorem gtail_second_shift_eval (q c g d : ℕ) :
    (tailShellPoly (c : ℤ)).eval (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) =
      ((GTail 7 1 (g + q ^ 2 * d) c : ℕ) : ℤ)
```

```lean
theorem gtail_support_of_square {q : ℕ} (c g : ℕ) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    q ∣ GTail 7 1 g c
```

```lean
theorem gtail_integer_square_support {q : ℕ} (c g : ℕ)
    (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    (q : ℤ) ^ 2 ∣ (tailShellPoly (c : ℤ)).eval ((c + g : ℕ) : ℤ)
```

```lean
theorem gtail_integer_derivative_not_dvd {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    ¬ (q : ℤ) ∣ (tailShellPoly (c : ℤ)).derivative.eval ((c + g : ℕ) : ℤ)
```

```lean
theorem gtail_second_lift_predicate (q c g d : ℕ) :
    (q : ℤ) ^ 3 ∣ (tailShellPoly (c : ℤ)).eval
      (((c + g : ℕ) : ℤ) + (q : ℤ) ^ 2 * (d : ℤ)) ↔
    q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * d) c
```

```lean
theorem existsUnique_gtail_second_digit {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    ∃! t : Fin q, q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * t.val) c
```

```lean
theorem gtail_second_lift_iff_linear {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hT2 : q ^ 2 ∣ GTail 7 1 g c) :
    q ^ 3 ∣ GTail 7 1 (g + q ^ 2 * d) c ↔
      ((GTail 7 1 g c / q ^ 2 : ℕ) : ZMod q) + (d : ZMod q) *
        (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0
```

```lean
theorem gtail_second_shift_gap_unit {q : ℕ} (g d : ℕ) (hg : ¬ q ∣ g) :
    ¬ q ∣ g + q ^ 2 * d
```

```lean
theorem gtail_second_shift_ratio {q : ℕ} [Fact (Nat.Prime q)] (c g d : ℕ) :
    gtailSevenTailRatio q c (g + q ^ 2 * d) = gtailSevenTailRatio q c g
```

```lean
theorem gtail_second_shift_derivative {q : ℕ} (c g d : ℕ) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + (g + q ^ 2 * d) : ℕ) : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q)
```

## Sequential focused build evidence

全 command は `lean/dk_math`、process-local LEAN_NUM_THREADS=2。
Ignored local logs `.lake/build/gtail-step028/`、exact commands/exits/time は runs.json。

| Log | Target after `LEAN_NUM_THREADS=2 lake build` | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 14.19 |
| 02-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit` | 1 | 13.79 |
| 03-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 14.37 |
| 04-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit` | 1 | 14.32 |
| 05-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 14.49 |
| 06-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit` | 1 | 15.14 |
| 07-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 16.15 |
| 08-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 8.15 |
| 09-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 8.2 |

Phase1 gate01成功、Phase2 native ∃! gate03成功、optional iff/source gate05成功。
Final new tests07、Step027 regression08、Step026 regression09 は exit0、final source/test warning0。

Intermediate repairs:
- 02: simp only の predicate matchingでは exponent 2+1 を3として認識しなかった。
  typed integer ∃! intermediateで exponent3を明示し03で解消。
- 04: change の型注釈が integer sum の後の castではなく ZMod operands に適用されていた。
  integer sum全体の explicit castに修正し05で解消。
- 06: concrete gap32598 に対する rewriteが arithmetic-expression pattern に一致しなかった。
  typed ratio equalityの transitivityで07に解消。

## Import cost, axioms, audits and preservation

10 public declarationsの #print axioms全件で standard propext/Classical.choice/Quot.sound のみ。
No new axiom / sorryAx。新 source/test comment/string除外 token scan:
sorry/admit/axiom/unsafe/native_decide/set_option/False.elim=0。
MIT2026 header、import後 file-print、既存2-space proof styleを維持。

Closure audit: neutral GTailSevenRealTraceResidue1907 modules/local20、new owner8937/local157、new test8938/local158。
Local union158 vertices、cycle0。Existing PolynomialHenselDigit standalone closure1409/local1、neutral→FLT0。
Step027 source closureとの差は new FLT ownerとexisting PolynomialHenselDigitの **2 local modulesのみ**。
追加 Mathlib modules0、削除0。Taylor/Div packagesは既存 source transitive closure内に既に存在した。
これは import graphの差であり build runtime改善を意味しない。

New source/test closureに full FLT.Seven facade、degree-six Domain、global oriented factorization、
oriented valuation ownership、Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge はない。
imports.json / import-impact.json / audit.json に検査結果。
最初の import scan は test file作成前だったためclosure1の provisional resultだった。
ファイル作成後に再検査し、上記 full closureへ更新。Axiom audit script の初回は誤ったsource log05を参照して失敗、
正しいtest log07を参照して全10件の検査を完了した。

git diff --check と新4files whitespace検査成功。ROADMAPはhistorical prefixを保持したpost027 append。
既存 generic neutral API、earlier GTail owners、ring/ideal definitions、facades、signed-depth files、reviews/ledger は変更なし。
No full build or global resource-limit change。Step028で停止。
No all-k ideal valuation, K³ claim, q-adic completion, integral carrier map, packets, principalization,
unit-class lifting, primitive Fermat descent or unconditional FLT7 closure。
