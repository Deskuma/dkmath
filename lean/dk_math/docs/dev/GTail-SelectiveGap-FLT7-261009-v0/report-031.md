# Step031 — conditional norm-scalar / ideal-depth compatibility

2026-10-10。**COMPLETE / Outcome B**。Step031 で停止。
Base HEAD: `ff652d916ccdb2986286d92cc92b8a70ecd937ec`。

新 owner は hypothetical positive primitive Fermat7 tuple の正確な仮定を保持し、
Eisenstein degree-two norm readout と degree-six cyclotomic ideal receivers を共通の
natural/integer scalar data で接続した。q∤g を導き、既存 Step010 予算から
v_q(T)=2v_q(Q)、q³∣T↔q⁴∣T、および各選択 F_i の K³↔K⁴ を得た。
**これは Step010 の付値予算の型付き適用・再包装であり、新しい FLT7 obstruction/descent ではない。**
E→R integral RingHom、P=K、α²=F_i、signed packet の再構成は含まない。

変更は新 Lean owner/test、source-inventory-031.md、本 report と ROADMAP の post030 append。
以前の ring/norm/carrier/GTail owners、facades、reports/reviews、constraint ledger は変更していない。

## 実装と仮定の導出

先に抽象 q,g,T,Q の明示的 budget と q∤g だけから doubled valuation を証明した。
整除 readouts には prime q と T,Q≠0 を明示。g≠0 は q∤g から従うため冗長な引数を省いた。
scalar_budget_tail_double 自体は単に budget 内の v_q(g)=0 を代入する lemma なので
prime/nonzero 前提を必要としない。Fermat 方程式を仮定しない satisfiable instance で先に検証。

FLT-facing では ha,hb,hcop,hEq,hsum,Fact prime q,hq7,hQ,hT を保持する。
既存 product-unit と endpoint-unit、support-exclusive を呼び、q∤a,b,a+b,c,g を導いた。
q≠3 は neutral prime_ne_three_of_gtail に導いた endpoint/gap units を渡す。
private focused_positive_nonzero は正の g*T の右辺から g,T≠0 と正の Q から Q≠0 を導く。
既存 private helper の生成名は参照していない。
付値は padicValNat_focused_quadratic_budget、q²∣T は prime_square_focused_allocation を再利用。

Eisenstein endpoint は normα=Q、α²∈P_t*P_t、conjugate/scalar exclusions、integer norm-square
balance を一つの定理に保持する。同じ full hypotheses の別 endpoint は実際の
F_i∈K²、F_i∈K³↔F_i∈K⁴、¬(F_i∈K³∧F_i∉K⁴)。receiver は Step025/029/030 の iff。
optional q⁴∣T↔(q:ℤ)²∣normα も Int/Nat cast と既存 norm equality で検証した。
ここで normα は Q であり norm(α²)=Q² と区別する。

## 全公開定理の正確な署名

以下は実装ソースから採録した7定理。namespace は DkMath.FLT.Seven、
open は CosmicFormula / Lib.NumberTheory / NumberTheory.TraceOneQuadratic。
E=TraceOneInt(-1)、R=SevenCyclotomicDegreeSixInt.Ring。dependent ideal の proof arguments
を含めて記載する。guards 定理は positivity が不要な stronger API；残りの FLT-facing
readout/endpoint/norm-divisibility 定理は同じ full positive primitive input を保持する。

```lean
theorem scalar_budget_tail_double (q g T Q : ℕ) (hgu : ¬ q ∣ g)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q) :
    padicValNat q T = 2 * padicValNat q Q
```

```lean
theorem scalar_budget_depth_readouts (q g T Q : ℕ) (hq : Nat.Prime q)
    (hT0 : T ≠ 0) (hQ0 : Q ≠ 0) (hgu : ¬ q ∣ g)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q) :
    (q ^ 2 ∣ T ↔ q ∣ Q) ∧ (q ^ 4 ∣ T ↔ q ^ 2 ∣ Q) ∧
      (q ^ 3 ∣ T ↔ q ^ 4 ∣ T) ∧ ¬ (q ^ 3 ∣ T ∧ ¬ q ^ 4 ∣ T)
```

```lean
theorem focused_norm_depth_guards {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    (¬ q ∣ a) ∧ (¬ q ∣ b) ∧ (¬ q ∣ a + b) ∧ (¬ q ∣ c) ∧ (¬ q ∣ g) ∧ q ≠ 3
```

```lean
theorem focused_norm_scalar_depth_readouts {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    padicValNat q (GTail 7 1 g c) = 2 * padicValNat q (a ^ 2 + a * b + b ^ 2) ∧
    q ^ 2 ∣ GTail 7 1 g c ∧
    (q ^ 4 ∣ GTail 7 1 g c ↔ q ^ 2 ∣ a ^ 2 + a * b + b ^ 2) ∧
    (q ^ 3 ∣ GTail 7 1 g c ↔ q ^ 4 ∣ GTail 7 1 g c)
```

```lean
theorem focused_eisenstein_norm_square_endpoint {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    let hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
    norm (gtailSevenNormCoord a b) = ((a ^ 2 + a * b + b ^ 2 : ℕ) : ℤ) ∧
    ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∈
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hu.2.1) *
      eisensteinResidueIdeal (gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_polynomial hQ hu.2.1) ∧
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉
      eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
        (gtailSevenResidueRoot_conjugate_polynomial hQ hu.2.1) ∧
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal q) ∧
    (g : ℤ) * ((GTail 7 1 g c : ℕ) : ℤ) =
      7 * (a : ℤ) * (b : ℤ) * ((a + b : ℕ) : ℤ) *
        norm ((gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2)
```

```lean
theorem focused_cyclotomic_depth_endpoint {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) (i : Fin 6) :
    let hu := focused_norm_depth_guards hcop hEq hsum hq7 hQ hT
    let K := sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hu.2.2.2.1 hT)
      (gtailSevenTailRatio_pow_seven hu.2.2.2.1 hT)
      (gtailSevenTailRatio_ne_one hu.2.2.2.1 hu.2.2.2.2.1) (sixInverseSlot i)
    gtailCyclotomicFactor c g i ∈ K ^ 2 ∧
      (gtailCyclotomicFactor c g i ∈ K ^ 3 ↔ gtailCyclotomicFactor c g i ∈ K ^ 4) ∧
      ¬ (gtailCyclotomicFactor c g i ∈ K ^ 3 ∧ gtailCyclotomicFactor c g i ∉ K ^ 4)
```

```lean
theorem focused_tail_fourth_iff_norm_square_dvd {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c) :
    q ^ 4 ∣ GTail 7 1 g c ↔ (q : ℤ) ^ 2 ∣ norm (gtailSevenNormCoord a b)
```

## 検証した example と数学的境界

新 test は26 examples（うち4件は full conditional theorem signatures の universal tests）。

| Control | Lean で確認した結果 | 意味 |
|---|---|---|
| abstract q43,g4,Q43,T43² | 実際の budget、gap unit、非零、doubled valuation と4つの bounded readouts | satisfiable な **抽象 scalar** instance。Q(5,8)/native GTail と同一視しない |
| abstract q43,g43,Q43,T43 | budget を満たすが Tail valuation1 | gap unit がないと偶数性は出ない |
| abstract q43,g43,Q43²,T43³ | budget1+3=2·2、q³∣T、q⁴∤T | exact scalar depth3 が gap-unit なしで可能 |
| (a,b,c,g)=(5,8,9,4), q43 | normα=129、q∣Q、t37、r11、q∣T、b,c,g units | 両 residue data は共存する |
| 同上 E | α²∈P37*P37、α²∉P7、α²∉scalar43 | Step017 actual ideal address |
| 同上 R | 全6 F_i∈assigned K、F_i∉assigned K² | E の square address だけから R の K² は出ない |
| 同上の scalar / equation | gT=7ab(a+b)Q² は false、Fermat7Equation は false | conditional endpoints を numeric tuple に適用できない |
| c9,g32598 | 全6 F_i∈K³\K⁴、5+8≠9+32598 | Step030 genuine third-depth control は focused tuple relation 外 |
| q3/q7/q13 | char3 repeated root、ZMod7 の nontrivial seventh root 不存在、13∣g だが13∤T | paired/selected assumptions の境界 |
| zero coordinates | Fermat7Equation 0 3 3 は true、0<a は false | positive primitive tuple の反例ではない |
| T0,Q1,g4,q43 | zero valuation budget は true、q²∣T↔q∣Q は false | T≠0 が必要 |
| T1,Q0,g4,q43 | zero valuation budget は true、q²∣T↔q∣Q は false | Q≠0 が必要 |

失敗した proof attempt は05-build.log の一件。test 内の local notation K が universal
signature 内の `let K` pattern と衝突し `Invalid pattern` になった。numeric notation を
K43 に改名し06で成功。非零条件の反例2件を追加した07も成功。
production の Phase1/2/3 proofs は01/03/04で各々成功し、意味や仮定の弱化で回避していない。

## 実行コマンド・終了コード・ログ

全 Lake 実行は作業ディレクトリ lean/dk_math、逐次、process-local LEAN_NUM_THREADS=2。
Lake の Replayed 表示は既存 artifact/log の再生を含む。この focused build 成功を、
全 module の clean recompilation や全 suite 成功とは記載しない。
ログと runs.json は `.lake/build/gtail-step031/`。

| Log | Command | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 14.32 |
| 02-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 16.27 |
| 03-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 16.48 |
| 04-build.log | `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 17.26 |
| 05-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 1 | 20.21 |
| 06-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 21.04 |
| 07-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` | 0 | 20.92 |
| 08-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 8.33 |
| 09-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeAllocationAudit` | 0 | 8.23 |
| 10-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailNormReadoutAudit` | 0 | 8.2 |
| 11-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenNormReadout` | 0 | 1.4 |
| 12-build.log | `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 1.58 |

01=abstract source、02=初期 scalar controls、03=derived guards/budget、04=typed endpoint source、
05=expanded test の記法衝突、06=修正後、07=最終26例と全公理。
08=Step030、09=Step010、10=Step012 FLT、11=Step012 neutral、12=Step017 regression。
最終 source04/test07 と5 regression gates の警告は0。

## 実際の公理出力と監査

07-build.log の `#print axioms` 出力（7/7 public theorems）：

```text
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:166:0: 'DkMath.Lib.NumberTheory.norm_eisensteinCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:167:0: 'DkMath.Lib.NumberTheory.eisensteinCoord_mul' depends on axioms: [propext]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:168:0: 'DkMath.Lib.NumberTheory.eisensteinCoord_sq' depends on axioms: [propext]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:169:0: 'DkMath.Lib.NumberTheory.eisensteinCoord_mul_sq' depends on axioms: [propext, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:170:0: 'DkMath.Lib.NumberTheory.norm_eisensteinCoord_mul_sq' depends on axioms: [propext, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:171:0: 'DkMath.Lib.NumberTheory.eisenstein_square_coefficient_coprime' depends on axioms: [propext]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:172:0: 'DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_fst' depends on axioms: [propext, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:173:0: 'DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:174:0: 'DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime' depends on axioms: [propext,
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:175:0: 'DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_norm' depends on axioms: [propext, Quot.sound]
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:176:0: 'DkMath.Lib.NumberTheory.eisenstein_mul_sq_eq_cubicCoord_polynomial_norm' depends on axioms: [propext,
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:201:0: 'DkMath.Lib.NumberTheory.traceOne_mul_conj_fst' depends on axioms: [propext]
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:202:0: 'DkMath.Lib.NumberTheory.traceOne_mul_conj_snd' depends on axioms: [propext]
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:203:0: 'DkMath.Lib.NumberTheory.traceOne_norm_conj' depends on axioms: [propext]
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:204:0: 'DkMath.Lib.NumberTheory.traceOne_mul_right_cancel_of_norm_ne_zero' depends on axioms: [propext,
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:205:0: 'DkMath.Lib.NumberTheory.traceOne_dvd_iff_norm_dvd_mul_conj_coordinates' depends on axioms: [propext,
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:206:0: 'DkMath.Lib.NumberTheory.traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates' depends on axioms: [propext,
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:207:0: 'DkMath.Lib.NumberTheory.traceOne_dvd_imp_norm_dvd_norm' depends on axioms: [propext, Quot.sound]
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean:208:0: 'DkMath.Lib.NumberTheory.traceOne_zero_norm_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.scalar_budget_tail_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.scalar_budget_depth_readouts' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.focused_norm_depth_guards' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.focused_norm_scalar_depth_readouts' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.focused_eisenstein_norm_square_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.focused_cyclotomic_depth_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.focused_tail_fourth_iff_norm_square_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

すべて propext, Classical.choice, Quot.sound のみ。新 axioms はない。
comment/string を除外した新 Lean2ファイルの禁止 token scan は
sorry/admit/axiom/unsafe/native_decide/set_option/explicit False.elim が0。
MIT2026 header、imports 後の正確な file print と既存書式を確認。

Source closure8946/local166、test8947/local167、local union167cycle0。
Step030 比7 local additions / Mathlib additions0 / removals0。
neutral RealTrace root1907/local20 は FLT到達0；さらに新sourceの到達範囲の
全27 neutral Lib owners から FLT 到達0。詳細は imports.json/import-impact.json/audit.json。
FLT.Seven façade、degree-six domain、global oriented factorization、oriented carrier valuation
ownership、Kummer principalization、CyclotomicQRTraceOneBridge は source/test closure にない。
Step030 由来の carrier closure は広く、旧 DescentClosureAudit 等は依然含む；
それは unconditional impossibility を供給する新 dependency ではない。新 proofs は既存
budget/square allocation/norm/root/ideal receivers の明示的 chain を使用し、closureProvider や
unconditional FLT contradiction を使っていない。ソース比較は source-inventory-031.md。

tracked diff は ROADMAP append のみで、以前の tracked files の内容を保持。
新4ファイルと ROADMAP 追加部分の trailing whitespace / tabs / final newline チェックと
git diff --check は成功。最初の全 ROADMAP scan は既存3行目の Markdown hard-break
（末尾2空白）を検出したため、その歴史部分を保持し追加範囲に限定して再確認した。
ROADMAP の HEAD 版を prefix とすることを検証。

## Lean 結果からの気づき・今後の実装提案

1. exact-depth-three exclusion は新しい arithmetic obstruction ではない。
   budget と gap-unit による scalar evenness に、既存の actual K³/K⁴ iff を接続した結果。
   同じ proof を ideal 側で独立の descent と数えるべきではない。
2. mixed q43 calibration は、norm-square の選択 E ideal support と R の ideal depth が
   独立であることを具体的に示す。両側 q-support と finite-field roots の存在だけでは
   scalar balance は成立しない。future transport はこの不足を別の source theorem で埋める必要がある。
3. 新たに試した zero controls は padicValNat の0規約に由来する2つの具体的な readout failure。
   今後 helper を再利用する際、T,Q≠0 を削除しないための calibration として維持するとよい。
4. hgu の必要性は abstract exact-depth-three control で独立に確認できる。
   positive Fermat tuple を探す代わりに、satisfiable scalar contract と full universal signature
   tests を併用すると、numeric missing-premise と条件付き theorem の論理を混同しにくい。
5. 次の検討は source-typed frontier の棚卸しが適切。E/R の共通 scalar data が捨てる
   coordinates / slot / integral lift を特定し、新しい restriction が本当に Step010 を超えるか
   先に確認する。本 Step で integral RingHom、signed packet、K⁵/all-k を実装する根拠は得られていない。

STOP031。Outcome B は条件付き readout compatibility の完成を意味する。
FLT7 の新 descent/closure、旧 signed quotientExponent の偶奇・再構成は得ていない。
