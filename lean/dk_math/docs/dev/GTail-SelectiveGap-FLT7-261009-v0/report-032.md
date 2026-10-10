# Step032 — exact global balance and local-compatibility firewall

2026-10-11。**COMPLETE / Outcome B**。Step032 で停止。
Branch feature/GTail-SelectiveGap-FLT7-261009-v0。
Base HEAD `777f79eaaf63f42e96e7afc8424473dbb98ed2e5`。

加法 focus だけで Fermat7Equation ↔ exact natural GTail balance、および typed integer
norm balance の同値を証明した。指定の positive primitive q43 tuple
(1166,1857,1858,1165) は geometry、focus、units、doubled budget、actual E square と
actual R exact second-depth を満たすが、元 equation と exact global balance を満たさない。
これは **明示的に列挙した q43 local contract の非十分性**であって、全必要条件の充足や
新しい FLT7 descent / impossibility ではない。

## 指示書の数値に関する訂正

Instruction032 の「旧 (5,8,9,4) は additive focus さえ失敗する」という文は誤り。
実際に 5+8=9+4=13。旧 tuple の strict geometry も成立する。
最初の test build02でその否定を decide したところ `Tactic decide proved ... is false`
となり、正しい focus/geometry example に訂正して03が成功した。
新 tuple の強化点は focus/geometry ではなく **q43 doubled scalar budget と K² membership**。
最終04には旧 tuple の budget failure を新 abstract readout theorem から確認する example も追加。
指示書・過去 report/review は歴史記録として変更していない。

さらに new g1165 は 7∤g（Lean example）。既存 seven_dvd_focused_gap は hEq/hfocus から
7∣g を要求するので、new witness はその条件を満たさない。
したがって「全既知 local constraints が同時成立する反例」とは呼ばない。
今回は prime q43 に関する指定の条件・norm/ideal readouts の十分性を検証している。

## 実装と正確な全公開署名

新 production/test は既存 header、2-space indentation、import後 file-print を維持。
production の direct import は Step031 一つだけ。extra exact owners はその closure に存在。

NAT reverse は gtail_seven_shell a b c g hfocus に balance を代入し、自然数の addition
cancellation を omega で行う。positivity、coprimality、prime、valuation premise は不要。
INT forward は既存 focused_gtail_eq_norm_square、reverse は norm_gtailSevenNormCoord_sq
で norm(α²)=(Q²:ℤ) とし、exact_mod_cast による ℕ→ℤ injectivity を使用する。
E の α² を R の F_i と等置しない。

```lean
theorem fermat7Equation_iff_focused_scalar_balance {a b c g : ℕ}
    (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ g * GTail 7 1 g c =
      7 * a * b * (a + b) * (a ^ 2 + a * b + b ^ 2) ^ 2

theorem fermat7Equation_iff_focused_norm_balance {a b c g : ℕ}
    (hfocus : a + b = c + g) :
    Fermat7Equation a b c ↔ (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2)

```

namespace DkMath.FLT.Seven、open CosmicFormula / Lib.NumberTheory / TraceOneQuadratic。
両同値は exact hfocus のみで arbitrary natural inputs に成立。元 equation の cheap
reformulation/circularity firewall であり、reverse が独立の FLT obstruction になったわけではない。

## 最終38 examples と実際の同一 tuple 検証

| Checked contract | Kernel-checked value/result |
|---|---|
| positive primitive geometry | 0<a,b；max(a,b)<c<a+b；0<g<min(a,b)；Nat.Coprime1166 1857 |
| additive focus | a+b=c+g=3023 |
| Q | 6,973,267 |
| native T=GTail 7 1 1165 1858 | 1,914,732,507,483,487,090,603 |
| units | 43∤a,b,a+b,c,g |
| exact scalar support | 43∣Q,43²∤Q,43²∣T,43³∤T |
| actual valuations | v43(g)=0,v43(Q)=1,v43(T)=2 |
| budget/evenness | v43(g)+v43(T)=2v43(Q),43³∣T↔43⁴∣T |
| prime-order divisibility control | 3∣42,7∣42,21∣42；Fact prime43 |
| E root/norm | t=37、normα=6,973,267 |
| E actual ideals | α²∈P37*P37、α²∉P7、α²∉eisensteinScalarIdeal43 |
| R root | r=11、r⁷=1、r≠1、t≠r in ZMod43 |
| R actual ideals | all6 F_i∈K_(sixInverseSlot i)²、all6 F_i∉K_(sixInverseSlot i)³ |
| wrong slots | all i,j with j≠sixInverseSlot i exclude F_i∈K_j |
| inverse slot list | [0,3,4,1,2,5] unchanged |
| exact hEq | false, checked by decide after unfolding Fermat7Equation |
| exact NAT balance | false from new iff/not_hEq, and separately by direct decide |
| exact INT norm balance | false from new typed iff/not_hEq |

Existential example は geometry、Coprime、全5 units、exact Q/T support、同じ budget と
¬Fermat7Equation を一つの native tuple に束ねている。E/R examples も同じ tupleを使用。
条件付き Step031 full endpoints は hEq が false のため適用しない。
局所 norm identity、scalar budget/ideal conclusions が成立することと、full theorem の
integer norm **balance**を満たすことは区別する。

最初の3 universal examples は NAT iff、INT iff と hEqからの balance を検証。
fictional numeral Fermat equation は使っていない。
旧 (5,8,9,4) の focus/geometry/root coexistence は true、Tail depth1 と budget failureも確認。
旧 c9,g32598 の全6 K³\K⁴ は true だが、a5+b8=c9+g32598 は false。
q3 repeated-root、q7 nonidentity seventh-root absence、q13 gap-only、zero-coordinate equation
も正確な violated premise と共に保持。zero (0,3,3) は hEq true でも 0<a false。

exact valuations は padicValNat を巨大数で展開せず、既存 nonzero/prime
padicValNat_le_iff_dvd と実際の q-power divisibility upper/lower bounds を使って証明した。
native GTail 値・divisibility・negative equation は decide で検証し、native_decide や
resource-limit options は使用していない。最終新test の Lean compilation time は9.5秒。

## Reconstruction frontier

[source-inventory-032.md](source-inventory-032.md) にA–G necessary/sufficient table、
[frontier-032.md](frontier-032.md) に old provider/signed packet の exact obligations と
source/target maps の ledger を記録した。
AwayDescentClosureProvider の nextX/Y/Z、new CounterexamplePack、new route、
nextRoute.carrier=Int.natAbs p.normal.root.snd が実際の再構成義務。
RamifiedSignedRootDepthPacket は balanced whole packet、source-linked signed roots、
IsCoprime、signed gap=7⁴gapRoot、signed quotient=7quotientRoot、7-units、normalizedEquation
を要求する。oriented depth はその packet carrier と PrimeSupport family を対象にする。
q43 scalar tuple から同じ carrier/roots/ideals を作る API は今回なく、その必要dataを露出した。

Instruction の docs/STATUS.md は実パス DkMath/FLT/Seven/docs/STATUS.md で確認。
July2026 historical status は current theorem/signature と区別し、更新しない。
これは将来 bridge 構築が不可能という proof ではない。現契約が missing provider を
inhabit しないという source-grounded finding。候補 algebraic map の必要な source/target、
generator images、relation preservation、integrality、consumer obligation は frontier に列挙したが
map/packet/provider は実装していない。

## 実行証拠

全 build は lean/dk_math にて逐次、process-local LEAN_NUM_THREADS=2。
logs と runs.json は `.lake/build/gtail-step032/`。

| Log | Exact command | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailGlobalBalanceFirewall` | 0 | 14.3 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall` | 1 | 15.64 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall` | 0 | 17.33 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailGlobalBalanceFirewall` | 0 | 18.0 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 8.41 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 8.38 |
| 07-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailBridge` | 0 | 8.05 |

01=両 production iff、02=指示の false old-focus claim検出、03=修正後、
04=最終38例、05=Step031、06=Step030、07=GTailBridge direct regression。
最終source01/test04と3 regressionはexit0、warning0。
Lake Replayed を含む focused buildsであり、全-suite/clean compilation と主張しない。

新2 public declarations の実際の04 `#print axioms` 出力：

```text
'DkMath.FLT.Seven.fermat7Equation_iff_focused_scalar_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.fermat7Equation_iff_focused_norm_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

propext,Classical.choice,Quot.sound のみ。新 axiom なし。
Import closure: source8947/local167、test8948/local168、local union168cycle0。
Step031比 new owner1のみ、Mathlib追加0、削除0。neutral RealTrace1907/local20、FLT到達0。
到達可能な全27 neutral Lib owners からFLT到達0。
FLT.Seven façade、degree-six domain、global oriented factorization、oriented valuation ownership、
Kummer principalization、CyclotomicQRTraceOneBridge は source/test closure にない。
既存 carrier closure は広く、旧 signed/depth/descent modules の一部が transitiveに含まれる。
今回の2 proofは shell/cast/norm identities の明示chainのみであり、unconditional FLT closureを
使わない。新 signed/oriented owner import はない。

comment/string除外の新 Lean2ファイル forbidden scan は
sorry/admit/axiom/unsafe/native_decide/set_option/explicit False.elim 0。
header/file-print/style、および新5ファイルと ROADMAP append の whitespaceチェックは成功。
既存 ROADMAP3行目の Markdown hard-break末尾2空白は歴史prefixとして維持。
git diff --check と ROADMAP HEAD-prefix検査成功。tracked変更はROADMAP appendのみ、
以前の source/facades/reports/reviews/ledgers/status は変更していない。
imports.json/import-impact.json/audit.json に監査証拠。

## Lean結果からの気づき・試した命題・実装提案

1. full exact balance は hfocus 下で hEq と同値。必要な global information をそのまま
   balance premise に置き直しても、局所から大域へ進んだことにはならない。
2. strong candidateの全値が検証でき、abstract budgetだけでなく native focused positive
   primitive geometry と actual two-ring ideal readouts の同時充足を確認できた。
   これは局所 receiver 自体が偽の条件を導入していないことの有用な calibration。
3. decide が旧focus否定を拒否したことで、旧例の不足は additive focus ではなく budget と
   R平方depthであると特定できた。future comparison は不足した仮定を一つずつ実際に検証するとよい。
4. 試した追加命題 7∤1165 はtrue。global hEqは既存7-primary条件でも排除されるため、
   この countermodel を全既知necessary条件の充足と拡大解釈しない。
   将来より強い witness を調べるなら追加した条件を明示し、全素数のlocal-to-global theorem
   が存在するかは別問題として監査する。今回は新 witness探索やnew obstruction実装に進まない。
5. 次の proposal の評価は、exact NAT balanceへ至る新しい非循環 global inputか、
   providerのnew primitive pack / actual carrier_matchの構成を与えるかを基準にすべき。
   finite field共有やnorm値だけをroot/ideal/carrier同一性として扱わない。

STOP032。Outcome B は exact equivalence と bounded local sufficiency countermodel の完成。
FLT7 descent、integral E→R transport、signed packet、K⁵/all-k、unit/class extraction は追加していない。
