# Step 019 — packet-free degree-six residue evaluation

Date: 2026-10-10. Base HEAD: `19c6e67080859ba71ef95a86c87c3f1fb9739956`.

## Result and scope

Outcome B。裸の非自明七乗根 r から β cubic、既存 real-cubic order の RingHom、
既存 degree-six carrier の RingHom と、自然数 Tail factor の実 kernel membership を実装。
新しい写像の署名は signed-depth packet を要求しない。整環の既存定義・packet owner は変更しない。

neutral owner は β の代数のみ。carrier に関わる二 RingHom は FLT owner に置く。
`gtailCyclotomicEval c g hc hg hT` は Step018 の r=(c+g)/c を実際に受け取り、
`gtailCyclotomicLinearFactor c g = ofReal(c+g)−ζ*ofReal(c)` を零に送る。
これは既存 source の実 RingHom.ker への membership であり、別 Eisenstein ideal との equality ではない。

## Public signatures

十四宣言（五 definitions、九 theorems）。以下は最終 source から抽出。

### DkMath/Lib/NumberTheory/GTailSevenRealTraceResidue.lean

```lean
def seventhRootBeta {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q) : ZMod q
```

```lean
theorem seventhRootBeta_cubic {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    seventhRootBeta r ^ 3 - 2 * seventhRootBeta r ^ 2 - seventhRootBeta r + 1 = 0
```

```lean
theorem seventhRootBeta_quadratic {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) : r ^ 2 = -1 + (seventhRootBeta r - 1) * r
```

### DkMath/FLT/Seven/GTailCyclotomicLocalEval.lean

```lean
def evalRealFromSeventhRoot {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    SevenRealCubicInt →+* ZMod q
```

```lean
@[simp] theorem evalRealFromSeventhRoot_alpha {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalRealFromSeventhRoot r hr0 hr7 hr1 SevenRealCubicInt.alpha = seventhRootBeta r
```

```lean
@[simp] theorem evalRealFromSeventhRoot_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (n : ℤ) :
    evalRealFromSeventhRoot r hr0 hr7 hr1 (n : SevenRealCubicInt) = (n : ZMod q)
```

```lean
def evalCyclotomicFromSeventhRoot {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) : SevenCyclotomicDegreeSixInt.Ring →+* ZMod q
```

```lean
@[simp] theorem evalCyclotomicFromSeventhRoot_zeta {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 zeta = r
```

```lean
@[simp] theorem evalCyclotomicFromSeventhRoot_ofReal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (x : SevenRealCubicInt) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal x) =
      evalRealFromSeventhRoot r hr0 hr7 hr1 x
```

```lean
@[simp] theorem evalCyclotomicFromSeventhRoot_alpha {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 (ofReal SevenRealCubicInt.alpha) =
      seventhRootBeta r
```

```lean
def gtailCyclotomicLinearFactor (c g : ℕ) : SevenCyclotomicDegreeSixInt.Ring
```

```lean
def gtailCyclotomicEval {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q
```

```lean
theorem gtailCyclotomicEval_linearFactor {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicEval c g hc hg hT (gtailCyclotomicLinearFactor c g) = 0
```

```lean
theorem gtailCyclotomicLinearFactor_mem_ker {q : ℕ} [Fact (Nat.Prime q)] (c g : ℕ)
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicLinearFactor c g ∈ RingHom.ker (gtailCyclotomicEval c g hc hg hT)
```

## Gate sequence and calibration

1. Neutral β cubic の focused build と八 examples：q43,r11 の inverse4、β16、cubic zero。
   r1→β3 は cubic value7≠0 in ZMod43。q7 の β3 は cubic root、非自明七乗根は不存在。
2. 実 signed-coordinate cubic RingHom の build/test：alpha16、integer−9、signed triple⟨−2,3,−4⟩ の評価、任意 x,y の multiplication law。
3. degree-six RingHom の build/test：ζ11、ofReal alpha16、ofReal compatibility、任意 x,y の multiplication law。
4. Tail factor receiver の build/test：q43、(5,8,9,4) の Q/T divisibility、t37、r11、F(9,4) と literal `ofReal13−ζ*ofReal9` の零評価・kernel membership。
   literal は13−11*9=0 in ZMod43。一般 receiver を適用し、有限算術だけで kernel membership を代用しない。

最終 FLT test は22 examples。`¬Fermat7Equation 5 8 9` を実定義の unfold/decide で確認。
同時に別 Eisenstein RingHom が α(5,8) を零に送ることも既存 theorem で検証。
q13 Gap の q|Q/g と q∤T、q3 repeated Eisenstein root、q5 inert quadratic case は分離して保持。
既存 degree-six `ramifiedEval_zeta` の q7 ζ↦1 を実 theorem でテストした。
q13 ratio1 と coordinate balance/coprime は Step018 regression にも記録されている。

## Formula / existing code comparison

既存 address の beta と今回 β はともに1+r+r⁻¹。
real map はともに x0+x1*β+x2*β² を ℤ signed coordinates 上に評価する。
degree-six map はともに evalReal(re)+r*evalReal(im) で、quadratic sign は `(-1, alpha−1)`。
今回 cubic law の証明は既存 packet proof の exact field_simp / linear_combination パターンを
neutral geometric sum と組み合わせ、packet-indexed private fact を呼ばない。
乗法は actual coordinate formulas と β cubic / r quadratic relation で再検証した。

既存 `QuotientPrimeMuSevenAddress` は p と q|p.quotientRoot、canonical signed-root ratio を持つ。
今回の natural ratio をその packet と一致させる theorem は追加しない。
共通 root が指定できる場合の extensional comparison は将来の薄い adapter 候補だが、今回未証明。
特に q43 の数値例から p を捏造していない。

## Lean 結果からの観察と提案

**確認済み:** quadratic compatibility は r≠0 と inverse cancellation だけで成り立つ。
cubic compatibility は別に非自明七乗根条件を要し、それが real-cubic multiplication を保証する。
linear factor の零評価は endpoint unit と ratio の定義による。T divisibility / gap unit は
その ratio で実際に RingHom を構成する段階に使う。この異なる依存段階を混同しない。

**確認済み:** 今回の bare-root / Tail receiver に q≠7 を追加する必要はなかった。
非自明性を要求したまま q7 へ適用できる instance はなく、既存 q7 map は別の ramified construction。
r1 を char43 で落とすと β cubic が偽になるが、r1 universally cannot define an evaluation とは結論しない。

**確認済み:** q43 calibration は実 RingHom と kernel membership を持ち、Fermat7Equation は偽。
従って typed representation / zero factor は新しい FLT7 obstruction や descent ではない。
両 source の共通 finite field に向かう二 hom は source rings 間の hom を供給しない。

**未実装の提案:** packet address と裸の root の一致が別途得られた場合、signed-coordinate ext による
`evalAlphaRoot` / `localEval` との equality adapter が候補。
integer residue lifts による surjectivity / kernel maximality も個別の追加候補で、今回の kernel 結論には不要。
principalization、exact ideal valuations、unit-power lifting、primitive next packet と descent は今回実装していない。

## Validation records

Cwd `/home/deskuma/develop/lean/dkmath/lean/dk_math`。各 build は sequential incremental、process-local LEAN_NUM_THREADS=2。
途中 gate builds はその時点の source の検証であり、最終全宣言の検証と区別する。
ローカル logs は ignored `.lake/build/gtail-step019/`、永続 archive ではない。

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenRealTraceResidue` | 0 | 4.37 | `.lake/build/gtail-step019/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRealTraceResidue` | 1 | 4.29 | `.lake/build/gtail-step019/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 18.22 | `.lake/build/gtail-step019/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRealTraceResidue` | 0 | 4.29 | `.lake/build/gtail-step019/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 17.11 | `.lake/build/gtail-step019/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 1 | 16.94 | `.lake/build/gtail-step019/06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 1 | 15.51 | `.lake/build/gtail-step019/07-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 1 | 15.83 | `.lake/build/gtail-step019/08-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 16.37 | `.lake/build/gtail-step019/09-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 16.01 | `.lake/build/gtail-step019/10-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 15.64 | `.lake/build/gtail-step019/11-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 17.68 | `.lake/build/gtail-step019/12-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 1 | 15.58 | `.lake/build/gtail-step019/13-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 1 | 15.84 | `.lake/build/gtail-step019/14-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 17.19 | `.lake/build/gtail-step019/15-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPairedResidue` | 0 | 7.82 | `.lake/build/gtail-step019/16-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 1.59 | `.lake/build/gtail-step019/17-build.log` |

試行中の失敗を隠していない：02 は存在しない inverse lemma 名と q7 numeral normalization を修正し04で成功。
06/07/08 は degree-six map_one の broad simp が進まない失敗。actual carrier type を明記し、
re_one/im_one と map_one/map_zero の targeted simp に直し09で成功。13/14 は literal numeric scalar の
real evaluation が simp / 定義展開だけでは簡約されなかったため、typed `map_natCast` facts を明示し15で成功した。
11 の unused simp argument は削除した。失敗時の elaborator recovery の sorry warning は成功した最終宣言とは区別する。

最終 focused exit0：neutral production01/test04、carrier production12/test15。
Step018 test16、Step017 test17 の regression も exit0。
十四 public axiom checks は04/15の名前別出力を照合。
`gtailCyclotomicLinearFactor` は `[propext, Quot.sound]`、残り十三件は
`[propext, Classical.choice, Quot.sound]`。sorryAx なし。
最終新規モジュールの warning なし。四新規 Lean sources の
sorry/admit/axiom/unsafe/native_decide/sorryAx/False.elim 検査は零。
License header、import 後の file print も確認。

Comment/string 除去後の import headers で source closure を取得し local DAG を検査。
neutral production1907 modules（local20）、neutral test1908（local21）、
carrier production8926（local146）、carrier test8935（local155）、local union156 vertices に循環なし。
neutral production closure に FLT は零。carrier closure に full `DkMath.FLT.Seven` facade はない。
これらは inspected source closure の件数で、今回新規 build 数ではない。
carrier test は q7 実評価検証用に ramified owner を追加 import。
既存 degree-six source 自体の closure が大きいことと、新 API の packet-free 署名は区別する。

既存 tracked source / historical reports / ledger / facade / root driver は HEAD と一致。
ROADMAP の旧 bytes を prefix として保存し、post018 entry のみ追記。
`git diff --check` と新規 untracked 六ファイルの whitespace check は通過。
ローカル検査記録 `audit.json` / `imports.json` / `runs.json`。

STOP: Step019 のみ。Eisenstein→cyclotomic integral RingHom、source ideals の equality、
unit/class theorem、FLT7 contradiction、descent は結論しない。
