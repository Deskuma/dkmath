# Step 021 — six supplied seventh-root prime slots

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `5945b33ec83eaecbc7d8f7c1d06476191f0dbe71`.
Outcome **B**。Step021 のみ完了。

## Checked result

`GTailCyclotomicSixRootOrbit` は supplied nonidentity seventh root r の1..6乗を Fin6 で添字付ける。
orderOf r=7 と order 未満の power injectivity により、六根の非identity・相違を証明した。
七乗一と非零も別 theorem。q-prime が不要な pure monoid 部分にはそれを前提に追加しない。

既存 actual degree-six ring の各 `sixRootKernel` は Step020 の `seventhRootKernel` を特殊化。
maximal/prime、integer contraction(q)、quotient cardinal q は既存 receiver を再利用。
異なる根の kernel-ne は既存 integral separating-element theorem を経由し、
Mathlib の distinct-maximal theorem により pairwise sup=top を示す。

natural Tail r=(c+g)/c に対して `F(c,g)∈K_i ↔ i=0` を証明。
slot0 membership と remaining-five exclusion も別受信 theorem にした。
署名に q|Q、Fermat equation、positivity、signed-root packet はない。
根の分類、全 prime ideals の分類、intersection=(q)、six-ideal product=(q) を結論しない。

## All new public signatures

Namespace `DkMath.FLT.Seven`。二 definitions と十六 theorems。実ソースから抽出。

```lean
def sixSlotRoot {q : ℕ} (r : ZMod q) (i : Fin 6) : ZMod q
```

```lean
theorem seventhRoot_orderOf {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    orderOf r = 7
```

```lean
@[simp] theorem sixSlotRoot_zero {q : ℕ} (r : ZMod q) : sixSlotRoot r 0 = r
```

```lean
theorem sixSlotRoot_pow_seven {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (i : Fin 6) :
    sixSlotRoot r i ^ 7 = 1
```

```lean
theorem sixSlotRoot_ne_zero {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (i : Fin 6) : sixSlotRoot r i ≠ 0
```

```lean
theorem sixSlotRoot_ne_one {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i : Fin 6) : sixSlotRoot r i ≠ 1
```

```lean
theorem sixSlotRoot_injective {q : ℕ} (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Function.Injective (sixSlotRoot r)
```

```lean
def sixRootKernel {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Ideal SevenCyclotomicDegreeSixInt.Ring
```

```lean
@[simp] theorem mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ sixRootKernel r hr0 hr7 hr1 i ↔
      evalCyclotomicFromSeventhRoot (sixSlotRoot r i) (sixSlotRoot_ne_zero r hr0 i)
        (sixSlotRoot_pow_seven r hr7 i) (sixSlotRoot_ne_one r hr7 hr1 i) z = 0
```

```lean
theorem sixRootKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    (sixRootKernel r hr0 hr7 hr1 i).IsMaximal
```

```lean
theorem sixRootKernel_isPrime {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    (sixRootKernel r hr0 hr7 hr1 i).IsPrime
```

```lean
theorem sixRootKernel_comap_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
      (sixRootKernel r hr0 hr7 hr1 i) = Ideal.span ({(q : ℤ)} : Set ℤ)
```

```lean
theorem sixRootKernel_cardQuot {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (i : Fin 6) :
    Submodule.cardQuot (sixRootKernel r hr0 hr7 hr1 i) = q
```

```lean
theorem sixRootKernel_ne {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i j : Fin 6) (hij : i ≠ j) :
    sixRootKernel r hr0 hr7 hr1 i ≠ sixRootKernel r hr0 hr7 hr1 j
```

```lean
theorem sixRootKernel_sup_eq_top {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (i j : Fin 6) (hij : i ≠ j) :
    sixRootKernel r hr0 hr7 hr1 i ⊔ sixRootKernel r hr0 hr7 hr1 j = ⊤
```

```lean
theorem gtailCyclotomicLinearFactor_mem_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicLinearFactor c g ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) i ↔ i = 0
```

```lean
theorem gtailCyclotomicLinearFactor_mem_sixRootKernel_zero {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) :
    gtailCyclotomicLinearFactor c g ∈ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) 0
```

```lean
theorem gtailCyclotomicLinearFactor_not_mem_sixRootKernel {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) (i : Fin 6) (hi : i ≠ 0) :
    gtailCyclotomicLinearFactor c g ∉ sixRootKernel (gtailSevenTailRatio q c g)
      (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
      (gtailSevenTailRatio_ne_one hc hg) i
```

## Twenty-four kernel-checked examples

q43,r11 の ascending powered roots は `[11,35,41,21,16,4]`。
全六根の七乗一・非零・非identity と injectivity は一般定理で検証。
全六 kernel の maximal/prime、integer contraction と cardinal43 を一般 receiver で適用。
全異なる添字対の kernel-ne と comaximality も一般 theorem の適用で検証した。

q43,c9,g4 の actual F の六評価値は `[0,42,31,39,41,20]`。
評価値テストは actual RingHom を展開し、有限算術で各 residual expression を確認する。
`13−35*9=42≠0` も直接確認。
全 Fin6 の membership iff index0、slot0 membership、全 other indices の exclusion、
`∃! i : Fin6, F∈K_i` は一般 selective theorem を適用して確認。
canonical ratio11 への rewriting に伴う root proof terms は Prop certificates の proof irrelevance で揃う。

元の q43 Q/T divisibility と `¬Fermat7Equation 5 8 9` を保持。
q13 Gap は q|Q/g、q∤T、ratio1 で hr1 を供給しない。
q7 の非自明七乗根不存在と、別の existing ramified ζ↦1 theorem をともに確認。
q3 repeated / q5 inert は別 Eisenstein quadratic polynomial の finite examples のみ。
F(0,0)=0 は全六 kernel に属するので c-unit を取り除いた exactly-one support は偽。

## Lean 結果からの観察・今後の候補

**確認済み:** 六根の相違は i+1 と j+1 が order7 未満であることから従う。
root0 は r¹=r であり、old Fin3 Galois phase index と同一視しない。
非零 / nonidentity / seventh-power hypotheses を供給した root にのみ actual kernel API を使う。
q7 や Gap ratio1 に偽の certificate を強制しない。

**確認済み:** F(9,4) の support は explicit six-slot set 内で一つだけ。
この tuple の Fermat equation は偽なので、新たな FLT7 obstruction ではない。
支持の有無は exact ideal-adic exponent や principalization を意味しない。
同じ integer contraction と cardinality を持つ six kernels が pairwise distinct / comaximal になり得る。

**未実装の提案:** 任意 nonidentity seventh root s の orbit completeness には別の root-classification / polynomial-bound theorem が必要。
今回その optional theorem は試行せず、全 admissible roots を網羅したとは報告しない。
Galois covariance は source-inspect のみで defer。ζ↦ζ² や starζ=zetaInv の generator image だけから
whole RingHom equality を推論しない。real-cubic base rotation / beta の整合性も必要。

**未実装の境界:** six-ideal product を示すには、全六 kernels の intersection と scalar(q) の equality を別途検証する必要がある。
coordinate interpolation / CRT が将来の方法候補だが、今回その equality や product を試行していない。
Eisenstein→cyclotomic integral hom、ideal transport、unit/class extraction、primitive next tuple と descent は未実装。

## Commands, repairs and audits

Cwd `/home/deskuma/develop/lean/dkmath/lean/dk_math`。sequential incremental focused targets、process-local LEAN_NUM_THREADS=2。
log files は ignored `.lake/build/gtail-step021/`、永続 archive ではない。

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit` | 1 | 15.39 | `.lake/build/gtail-step021/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit` | 0 | 15.66 | `.lake/build/gtail-step021/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicSixRootOrbit` | 0 | 21.84 | `.lake/build/gtail-step021/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 0 | 9.3 | `.lake/build/gtail-step021/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 9.24 | `.lake/build/gtail-step021/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRealTraceResidue` | 0 | 2.18 | `.lake/build/gtail-step021/06-build.log` |

01 は selective iff の `rw [← root0=r]` が root_i の base r まで書き換え、別式にした elaboration failure。
両辺の root index を明示した injectivity iff を `simpa only [sixSlotRoot_zero]` で受け取り、数学的 contract を変えず修正。
最終 new production02 / test03 は exit0。Step020 test04、Step019 carrier05 / neutral06 の regressions も exit0。
新規 final modules に warning なし。

十八件の `#print axioms` は test03 log の public names 別に照合。
`sixSlotRoot`, `sixSlotRoot_zero`, `sixSlotRoot_pow_seven` は `[propext, Quot.sound]`、
残り十五件は `[propext, Classical.choice, Quot.sound]`。sorryAx なし。
新規二 Lean files の sorry/admit/axiom/unsafe/native_decide/sorryAx/False.elim 検査は零。
MIT License / Authors header と import 後の file print も保持。

Comment/string 除去後の import headers による source closure は
既存 neutral trace1907（local20）、新 production8928（local148）、新 test8937（local157）。
Step020 と比較し production は一新 owner、test は新 owner / test の追加分のみ。
local union157 vertices の DAG に循環なし。neutral trace closure に FLT は零。
新 production は full Seven facade / old global-oriented factorization を closure に含まない。
これらは inspected source closure の件数で、今回新規 build 数ではない。

既存 tracked sources / packet owners / ring definitions / facade / root driver / historical reports / ledger は HEAD と同一。
ROADMAP の旧 bytes は prefix として保存し post020 entry のみ追記。
`git diff --check` と新規 untracked 四ファイルの whitespace check は通過。
ローカル検査記録 `runs.json` / `imports.json` / `audit.json`。

STOP after Step021。六 ideal product、new valuations、source-ring transport、signed packet fabrication、
class/unit powers、primitive next Fermat tuple と unconditional FLT7 conclusion は主張しない。
