# Step 026 — GTail shell derivative / selected cofactor report

Date: 2026-10-10. **COMPLETE / Outcome B**.
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`; base HEAD `ef7ee2d424f1862fd4029f98d5f49e6ddd096247`.

## Result and exact mathematical boundary

Original GTail shell を actual `Polynomial A` として定義し、X に関する formal derivative を証明した。
c は定数。任意 CommRing で `(X-Cc)*G_c=X^7-C(c^7)` と
`G_c+(X-Cc)*G_c'=7*X^6` が成立する。natural evaluation は original `GTail 7 1 g c` の cast に等しい。

prime q、q∤c,g、q|T の canonical Tail contract のもとで、actual degree-six source ring R の
五因子 cofactor U_i の selected RingHom readout は、全 i:Fin6 について

```text
ev_selected(U_i) = G_c'(c+g) = 7*(c+g)^6/g ≠ 0  in ZMod q.
g*ev_selected(U_i) = 7*(c+g)^6.
```

q≠7 は追加仮定ではない。非identity seventh root から導出した。
この API は explanatory/readout bridge。FLT7 obstruction/descent、ideal-adic exact valuation、Hensel lift は証明していない。

## Carrier-correct proof and actual APIs

`tailShellPoly` は七項 homogeneous sum。Step023 の `GTail_seven_one_eq_homogeneous_sum` で natural shell と結合。
`Polynomial.eval_finsetSum`, `Fin.sum_univ_succ`, `C_pow`, `ring` で polynomial identity を証明。
`congrArg Polynomial.derivative`, `derivative_mul`, `derivative_pow`, `C_ofNat` により本物の形式微分を取得。
Tail divisibility と `ZMod.natCast_eq_zero_iff` で root evaluation zero を得て balance を specialization。
`eq_div_iff` は g≠0 の後だけ使用。

Step023 public factorization は actual R の value identity であり Polynomial(ZMod q) identity として直接 rewrite しない。
旧 owner の generic certificate が private のため、その finite algebraic certificate を新 owner の private helper として再検証。
A=Polynomial(coefficient ring)、z=C(s)、Y=C(c) と正しく instantiate し、genuine polynomial factorization を証明した。
旧 owner は変更していない。private certificate は新 axiom ではなく `linear_combination` で kernel checked。

selected root は s=sixSlotRoot r (sixInverseSlot i)。i を receiving slot と取り違えない。
`gtailCyclotomicFactor_unique_slot`, `mem_sixRootKernel_iff`, `evalCyclotomic_gtailFactor` で selected linear factor の eval zero。
`Finset.prod_erase_mul` で因子を分離し、`derivative_mul`, `derivative_X_sub_C`, `eval_prod` で derivative が他五因子の積になる。
actual R cofactor の `map_prod` は同じ五因子の値の積なので、typed derivative/cofactor bridge が得られる。
一般 erased-product derivative theorem 自体には root distinctness は不要で、selected linear factor zero だけを使う。
非零性は後段の canonical ratio guards で別途証明した。

`nontrivial_seventh_root_prime_ne_seven` は prime Fact も不要な signature。
ZMod7 の全 s に対する s^7=s を `decide` で検証し、r^7=1 と r≠1 の矛盾で q≠7。
prime q と q∣7 の divisor classification により 7≠0、c+g=r*c≠0、g≠0 から quotient 非零。
Step025 の prime-product nonmember proof を非零性の証明に流用していない。
新 tests では readout 非零と kernel membership iff により既存 cofactor nonmember を独立に再取得した。

## Public signatures (17: two definitions, fifteen theorems)

以下は実装から抽出した signature。namespace は `DkMath.FLT.Seven`。

```lean
noncomputable def tailShellPoly {A : Type*} [CommRing A] (c : A) : Polynomial A
```

```lean
theorem tailShellPoly_eval {A : Type*} [CommRing A] (c x : A) :
    (tailShellPoly c).eval x = ∑ j : Fin 7, x ^ (6 - j.val) * c ^ j.val
```

```lean
theorem tailShellPoly_eval_nat {A : Type*} [CommRing A] (c g : ℕ) :
    (tailShellPoly (c : A)).eval ((c + g : ℕ) : A) = ((GTail 7 1 g c : ℕ) : A)
```

```lean
theorem tailShellPoly_mul {A : Type*} [CommRing A] (c : A) :
    (X - C c) * tailShellPoly c = X ^ 7 - C (c ^ 7)
```

```lean
theorem tailShellPoly_derivative_identity {A : Type*} [CommRing A] (c : A) :
    tailShellPoly c + (X - C c) * (tailShellPoly c).derivative = 7 * X ^ 6
```

```lean
theorem tailShellPoly_derivative_at_zero {A : Type*} [CommRing A] (c x : A)
    (hx : (tailShellPoly c).eval x = 0) :
    (x - c) * (tailShellPoly c).derivative.eval x = 7 * x ^ 6
```

```lean
theorem gtail_shell_derivative_balance {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hT : q ∣ GTail 7 1 g c) :
    (g : ZMod q) * (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) =
      7 * ((c + g : ℕ) : ZMod q) ^ 6
```

```lean
theorem gtail_shell_derivative_formula {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) :
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q) =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 / (g : ZMod q)
```

```lean
theorem tailShellPoly_eq_root_product {A : Type*} [CommRing A] (s c : A)
    (hs : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 + s ^ 5 + s ^ 6 = 0) :
    tailShellPoly c = ∏ h : Fin 6, (X - C (s ^ (h.val + 1) * c))
```

```lean
theorem tailShellPoly_derivative_eq_erased_product {A : Type*} [CommRing A]
    (s c x : A) (hs : 1 + s + s ^ 2 + s ^ 3 + s ^ 4 + s ^ 5 + s ^ 6 = 0)
    (i : Fin 6) (hi : x - s ^ (i.val + 1) * c = 0) :
    (tailShellPoly c).derivative.eval x =
      ∏ h ∈ Finset.univ.erase i, (x - s ^ (h.val + 1) * c)
```

```lean
theorem eval_selected_cofactor_eq_tailShellPoly_derivative {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    evalCyclotomicFromSeventhRoot
      (sixSlotRoot (gtailSevenTailRatio q c g) (sixInverseSlot i))
      (sixSlotRoot_ne_zero _ (gtailSevenTailRatio_ne_zero hc hT) _)
      (sixSlotRoot_pow_seven _ (gtailSevenTailRatio_pow_seven hc hT) _)
      (sixSlotRoot_ne_one _ (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) _) (gtailCyclotomicCofactor c g i) =
    (tailShellPoly (c : ZMod q)).derivative.eval ((c + g : ℕ) : ZMod q)
```

```lean
theorem nontrivial_seventh_root_prime_ne_seven {q : ℕ} (r : ZMod q)
    (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : q ≠ 7
```

```lean
def gtailSelectedCofactorResidue {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) : ZMod q
```

```lean
theorem gtail_selected_cofactor_balance {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    (g : ZMod q) * gtailSelectedCofactorResidue c g hc hg hT i =
      7 * ((c + g : ℕ) : ZMod q) ^ 6
```

```lean
theorem gtail_selected_cofactor_formula {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailSelectedCofactorResidue c g hc hg hT i =
      7 * ((c + g : ℕ) : ZMod q) ^ 6 / (g : ZMod q)
```

```lean
theorem gtail_selected_cofactor_uniform {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i j : Fin 6) :
    gtailSelectedCofactorResidue c g hc hg hT i =
      gtailSelectedCofactorResidue c g hc hg hT j
```

```lean
theorem gtail_selected_cofactor_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) : gtailSelectedCofactorResidue c g hc hg hT i ≠ 0
```

## Calibration and Lean-derived observations

33 examples を検証。
- q43,c9,g4: T=14491387、43∣T、43²∤T。derivative=28、全六 selected cofactor=28、全六 selected factor∉K²。
- q43,c9,g1165: T=2638461449052811747、43²∣T。g≡4、c+g≡13、ratio=11。
  derivative=28、全六 selected cofactor=28、同時に全六 selected factor∈K²。
- quotient の numeric check は division の noncomputability を避け、`div_eq_iff` で field multiplication equality に変換し `decide`。
  derivative examples は generic formula の specialization を通して証明した。
- q7 では非identity seventh root が存在しない。c=1,x=1 の shell eval と derivative eval はともに0。
- c=0 / g=0 の formal identities と unconditional source product を保持。g=0 で quotient theorem の guard は成立しない。
- q13 Gap sample は q∣gap だが q∤Tail、ratio=1。q43 tuple a5,b8,c9 は Fermat7Equation を満たさない。

今回の二つの q43 examples は、mod-q の simple polynomial root が特定 source element の K² membership を禁止しないことを
同じ Lean test 内で明確に示す。cofactor が unit residue であることと selected factor の square depth は両立する。

追加の気づき: shell derivative quotient 自体は q∤c を必要とせず、q∤g と q∣T だけで成立する。
canonical source cofactor の意味づけには q∤c が必要なので、この二 API の guards を区別した。
formal identities は arbitrary CommRing、zero ring を含むため、このレポートは全 CommRing で exact degree=6 を主張しない。

実装提案（未実施）: 将来旧 owner を編集できる段階で generic homogeneous product certificate を neutral 共通 owner に公開すれば、
今回の private certificate の重複を解消できる。今回は旧 owner 編集禁止と小さい import を優先した。
Hensel lifting / discriminant の追加命題は別 proof contract が必要であり、今回の結果から実装済みとは扱わない。

## Sequential focused build evidence

全 command は `lean/dk_math` で process-local LEAN_NUM_THREADS=2。
ログは `.lake/build/gtail-step026/`（ignored local evidence）、exact commands/exits/timing は runs.json。

| Log | Command suffix after `LEAN_NUM_THREADS=2 lake build` | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDerivative` | 1 | 14.89 |
| 02-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 14.83 |
| 03-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 15.73 |
| 04-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDerivative` | 1 | 15.49 |
| 05-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 16.09 |
| 06-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative` | 1 | 16.43 |
| 07-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDerivative` | 0 | 17.13 |
| 08-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo` | 0 | 8.29 |
| 09-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne` | 0 | 8.5 |

02: Phase1 pass。03: Phase2 pass（unused eval_one warning は除去）。05: final Phase3/source pass、warning0。
07: final new test pass、warning0。08: Step025 regression pass。09: Step024 regression pass。
初回01では eval sum / C-power / polynomial numeral casts を修正。04では implicit proof arguments を伴う rewrite が
hc/hg/hT side-goals を生成したため、explicit typed theorem application に修正。
06では numeric ZMod division を直接 decide できず、また ZMod7 の literal7/21=0 が残った。
div_eq_iff と finite literal decide に修正し07で解消。

## Axioms, imports, preservation

17 public declarations 全件を新 test の `#print axioms` で確認。出力集合は standard
`propext`, `Classical.choice`, `Quot.sound` の範囲内。新 axiom / sorryAx はない。
新二 Lean files の comment/string 除外 token scan:
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `set_option`, `False.elim` は0。
MIT2026 header、import 後の file-print、既存 indentation を維持。

Source import closure audit: neutral GTailSevenRealTraceResidue 1907 modules / local20、new owner8934 / local154、
new test8935 / local155。local union155 vertices の cycle0、neutral→FLT0。
新 source/test closure に FLT.Seven facade、degree-six Domain、old global oriented factorization、
old oriented valuation ownership、Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge はない。
`imports.json` / `audit.json` に結果を保存。

既存 Lean owner、ring definitions、facades、signed packet files、drivers、historical reviews/ledger は変更していない。
変更は新 source/test/inventory/report と ROADMAP の post025 append のみ。
focused checks の範囲で完了。Step026 にて停止。
