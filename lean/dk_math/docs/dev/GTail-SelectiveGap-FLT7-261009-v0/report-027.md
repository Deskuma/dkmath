# Step027 — native GTail one-step Taylor correction

2026-10-10. **COMPLETE / Outcome B**.
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `9e29c43f0e62443dd9ce32601c72e052cc85ee65`.
Prerequisite review026/report026/inventory026 を確認。review026 は static inspection、独立 rebuild ではない。

## Verified endpoint

Original GTail shell の integer derivative を `gtailDerivativeInt` として定義。
任意 natural q,c,g,d について（prime/unit/support premise なし）、

```text
(q:ℤ)^2 ∣ T_c(g+q*d) - T_c(g) - (q*d:ℤ)*Dint(c,g).
```

prime q、q∤c,g、q∣T_c(g) の canonical Tail contract のもとで、
m=T_c(g)/q、D=G_c'(c+g):ZMod q、δ=−m/D とおくと、

```text
q² ∣ T_c(g+q*d) ↔ (m:ZMod q)+(d:ZMod q)*D=0
                ↔ (d:ZMod q)=δ.
m+δ*D=0; δ is unique among all ZMod q residues.
q² ∣ T_c(g+q*δ.val).
```

第一の iff には q∣T と prime q だけで十分。第二の iff、一意性、代表元 lift は c/g unit guards を使う。
δ の定義自体には guard がないが、その一意補正としての意味は明示した guard 付き theorem に限る。
これは classical one-step correction の native GTail adapter。FLT7 impossibility/descent を意味しない。

## Integral proof and carrier transport

`tailShellPoly_integer_taylor` は signed c,x,h:ℤ について h² divisibility を証明。
七項 shell と formal derivative を展開し、整数 remainder quotient witness を `ring` で検証した。
witness の係数計算には SymPy を使用したが、証明の信頼性は出力 witness の Lean kernel recheck にのみ依存する。
任意整数係数多項式への一般化は今回実装していない。signed shell coefficients の example は確認済み。

x=c+g、h=q*d に specialization。`tailShellPoly_eval_nat` で native GTail に接続し、
h²=q²*d² の整数 witness により q² divisibility。q=0 / d=0 / c=0 / g=0 を含む。

整数 derivative の cast は polynomial と derivative を七項展開し、ring cast laws によって
`gtailDerivativeInt_cast` として ZMod q derivative に接続。両 polynomial を definally equal として扱っていない。
`Polynomial.derivative_map` も source確認したが、今回は有限 shell の明示的 cast proof を採用。

T=q*(T/q) は `Nat.mul_div_cancel' hT` を exact_mod_cast。
Taylor witness k により lifted T=q*(m+d*Dint+q*k)。
prime q≠0 を用いた `mul_dvd_mul_iff_left` と `dvd_add_left` で
q²∣lifted T iff q∣m+d*Dint を **整数で** 証明。
最後に `ZMod.intCast_zmod_eq_zero_iff_dvd` で field-linear equation にする。
ZMod(q²) において q を除算・unit として消去する処理はない。

D≠0 は Step026 actual selected cofactor と derivative の equality、および cofactor nonzero から取得。
新たな q≠7 premise は追加していない。division cancel は D≠0 の後。
一意性は二つの linear equations の差と `mul_right_cancel₀`。
`ZMod.natCast_zmod_val` で δ.val を natural representative に戻して lift を得る。

全 shift g+q*d は residue g、q∤g、q∣Tail を維持する。
ratio と derivative は scalar equality として public adapters を実装した。
依存証明を含む cofactor/ideal の equality adapter は追加していない。
cofactor residue の保持は Step026 の derivative/cofactor equality と今回の derivative invariance を組み合わせて解釈できる。
旧 ideal definitions を rewrite・再定義していない。

## Overlap comparison

既存 `DkMath.Lib.NumberTheory.PolynomialHenselDigit` を確認。
`polynomial_powLift_iff` と `existsUnique_polynomial_powLift_digit` は一般 integral polynomial の
有限 positive-depth next digit API。今回の補正機構はそれらと同じ classical Taylor mechanism。
新しい一般 Hensel theory として分類しない。

今回の追加は original natural GTail、integer shell derivative、Step026 field derivative、
canonical unit/support premises、Step025 actual degree-six ideal-square endpoint の bounded connection。
既存 all-depth owner の編集/import はせず、Step026 一つだけを direct import。
Mathlib Taylor `exists_mul_sq_add_linear_part_eq_eval_add` の exact signature/source も確認したが、
今回の narrow remainder proof に追加 Taylor import は不要だった。
分析的 real GN/Cosmic derivative はこの typed finite-field correction endpoint の代替ではない。

## Nonvacuous examples and observations

25 new examples:
- arbitrary q,c,g,d の integer theorem、d=0、q=0、c=0、g=0。
- signed c=−2,x=−5,h=3 の actual integral shell Taylor remainder。
- q43,c9,g4: T=14491387、43∣T、43²∤T、m mod43=18、D=28。
- 18+27*28=0 mod43、generic uniqueness theorem から δ=27、その val=27。
- 4+43*27=1165。**generic correction theorem** から 43²∣T(1165)。
- 全 natural d について 43²∣T(4+43*d) iff cast d=27。
  d=0、26 は false、d=70 は true。
- q∤9,1165、shift ratio equality と ratio11、shift derivative equality と derivative28。
- generic correction から得た square divisibility を Step025 の generic theorem に渡し、
  全六 actual factors F_i(9,1165)∈K_(sixInverseSlot i)² を証明。
- a5,b8,c9 は Fermat7Equation を満たさない。

Step026 regression は両 q43 samples の全六 cofactor residue28 と、それぞれの K² exclusion/inclusion を維持。
Step025 regression も exact second-power iff を維持。

気づき: 一意性は natural d の一意性ではなく、mod q residue の一意性。
d=27 と d=70 の両方が lift する example はこの区別を検証する。
また lift によって residue root / derivative は変化しないが、元の source element の square membership は変化する。
これは Step026 の simple mod-q root と deeper source divisibility が両立する現象を具体的補正式で説明する。

実装提案（未実施）: 既に q²∣T の starting input の correction residue は0になる薄い adapter を追加できる。
今回の iff に d=0 を適用すれば得られるが、これを高次 lift / exact depth theorem と混同しない。
将来 generic PolynomialHenselDigit と native shell の transport を統合する場合も、
今回の natural quotient、integer cancellation、canonical ratio の contracts を明示的に保持する必要がある。

## Public signatures (16: two definitions, fourteen theorems)

Namespace `DkMath.FLT.Seven`。実装から抽出。

```lean
noncomputable def gtailDerivativeInt (c g : ℕ) : ℤ
```

```lean
theorem tailShellPoly_integer_taylor (c x h : ℤ) :
    h ^ 2 ∣ (tailShellPoly c).eval (x + h) - (tailShellPoly c).eval x -
      h * (tailShellPoly c).derivative.eval x
```

```lean
theorem gtail_integer_taylor (q c g d : ℕ) :
    (q : ℤ) ^ 2 ∣ ((GTail 7 1 (g + q * d) c : ℕ) : ℤ) -
      ((GTail 7 1 g c : ℕ) : ℤ) - ((q * d : ℕ) : ℤ) * gtailDerivativeInt c g
```

```lean
theorem gtailDerivativeInt_cast {q : ℕ} (c g : ℕ) :
    (gtailDerivativeInt c g : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q)
```

```lean
theorem gtail_lift_sq_iff_linear {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * d) c ↔
      ((GTail 7 1 g c / q : ℕ) : ZMod q) + (d : ZMod q) *
        (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0
```

```lean
noncomputable def gtailFirstCorrection {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ) : ZMod q
```

```lean
theorem gtail_shell_derivative_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) ≠ 0
```

```lean
theorem gtailFirstCorrection_equation {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    ((GTail 7 1 g c / q : ℕ) : ZMod q) + gtailFirstCorrection c g *
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0
```

```lean
theorem gtailFirstCorrection_unique {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (d : ZMod q) (hd : ((GTail 7 1 g c / q : ℕ) : ZMod q) + d *
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) = 0) :
    d = gtailFirstCorrection c g
```

```lean
theorem gtail_lift_sq_iff_correction {q : ℕ} [Fact (Nat.Prime q)]
    (c g d : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * d) c ↔ (d : ZMod q) = gtailFirstCorrection c g
```

```lean
theorem gtail_first_correction_lifts {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    q ^ 2 ∣ GTail 7 1 (g + q * (gtailFirstCorrection (q
```

```lean
theorem gtail_shift_cast {q : ℕ} (g d : ℕ) :
    ((g + q * d : ℕ) : ZMod q) = (g : ZMod q)
```

```lean
theorem gtail_shift_gap_unit {q : ℕ} (g d : ℕ) (hg : ¬ q ∣ g) :
    ¬ q ∣ g + q * d
```

```lean
theorem gtail_shift_ratio {q : ℕ} [Fact (Nat.Prime q)] (c g d : ℕ) :
    gtailSevenTailRatio q c (g + q * d) = gtailSevenTailRatio q c g
```

```lean
theorem gtail_shift_derivative {q : ℕ} (c g d : ℕ) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + (g + q * d) : ℕ) : ZMod q) =
      (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q)
```

```lean
theorem gtail_shift_tail_support {q : ℕ} (c g d : ℕ) (hT : q ∣ GTail 7 1 g c) :
    q ∣ GTail 7 1 (g + q * d) c
```

## Focused build evidence and repairs

全 command は `lean/dk_math`、process-local LEAN_NUM_THREADS=2、sequential focused builds。
Local ignored logs: `.lake/build/gtail-step027/`、exact commands/exits/time は runs.json。

| Log | Target after `LEAN_NUM_THREADS=2 lake build` | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 15.07 |
| 02-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 15.8 |
| 03-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 15.03 |
| 04-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 15.95 |
| 05-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 15.42 |
| 06-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 15.73 |
| 07-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 16.73 |
| 08-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 13.97 |
| 09-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 1 | 14.1 |
| 10-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 14.44 |
| 11-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 8.32 |
| 12-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 14.71 |
| 13-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo` | 0 | 8.2 |

Phase1 final02、Phase2 final04、Phase3/source final07 は exit0。
New tests final12、Step026 regression11、Step025 regression13 は exit0。final source/test warning0。

Intermediate repairs:
01: broad dsimp unfolded GTail and cast expressions before integer witness rewrite; dsimp only に限定。
03: linear_combination で T=q*m の equation の符号を修正。
05: ratio namespace open を追加。
06: correction definition の broad simp で expression が展開され nonzero fact が一致しなくなるため、
dsimp only + explicit div_mul_cancel₀ に変更。ratio adapter に既存 ratio definition の prime Fact を明示。
08/09: numeric natural casts と ZMod literal の rewrite matching を typed equality に変更。
10 は成功したが unused/unreachable norm_num warning が残ったため exact に置換、12 で warning0。

## Audits and preservation

16 public #print axioms 全件確認。standard propext/Classical.choice/Quot.sound の範囲内。
gtail_shift_cast は propext/Quot.sound のみ。新 axioms / sorryAx なし。
comment/string 除外 scan で sorry/admit/axiom/unsafe/native_decide/set_option/False.elim=0。
MIT2026 license header、import後 file-print、既存2-space proof style を維持。

Source closure audit: neutral owner1907 modules/local20、新 source8935/local155、新 test8936/local156。
local union156 vertices の cycle0、neutral→FLT0。
full FLT.Seven facade、degree-six Domain、global oriented factorization、oriented valuation ownership、
Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge は新 source/test closure にない。
imports.json / audit.json に確認結果。git diff --check と新ファイル whitespace check 成功。

既存 Lean owners、ring/ideal definitions、facades、signed packets、drivers、reviews/theorem ledger は保持。
新 source/test/inventory/report と ROADMAP append のみ。Step027 で停止。
No all-k induction, q-adic completion, generalized Hensel implementation, K-adic valuation equality,
principalization, integer carrier transfer, unit/class powers, primitive Fermat tuple or descent.
