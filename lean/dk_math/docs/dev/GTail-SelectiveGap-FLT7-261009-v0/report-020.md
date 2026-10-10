# Step 020 — packet-free maximal kernels and unique Tail address

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `43ecfd6e4f575e376166d7e0195a4f7c625bfd72`.

## Result

Outcome B。既存 degree-six carrier 上の裸の七乗根評価に対して、actual kernel、
全射性、maximality / primality、整数と real-cubic への contraction、quotient cardinality を検証。
Tail factor の根 slot 一意性と distinct root kernels の分離も実装した。
新規 production は Step019 owner のみ import し、旧 packet owners / ring definitions は変更していない。

Kernel は `RingHom.ker` で定義。surjectivity は各 ZMod residue z の natural representative z.val を
`ofReal (z.val : SevenRealCubicInt)` に持ち上げる。field codomain への全射から maximal、さらに prime。
integer contraction は `(q:ℤ)` の principal ideal、real-cubic contraction は Step019 trace-evaluation の kernel。
optional `Submodule.cardQuot K_r=q` も実 quotient equivalence を使って証明した。

`eval_s F(c,g)=0 ↔ s=(c+g)/c` は q∤c のみで cancellation する。
q|T、q∤g は canonical ratio を admissible root として用いる別の段階に必要。
Thin `gtailCyclotomicLinearFactor_unique_address` は canonical membership と distinct admissible-root nonmembership を結合。
root kernel の inequality は `w=ζ−ofReal(r.val)` の membership / nonmembership を明示して証明。
「二つの hom が ζ を違う値へ送る」だけを根拠にしない。

## All new public signatures

Namespace `DkMath.FLT.Seven`。一定義と十一定理。以下は実ソースから抽出。

```lean
def seventhRootKernel {q : ℕ} [Fact (Nat.Prime q)] (r : ZMod q)
    (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal SevenCyclotomicDegreeSixInt.Ring
```

```lean
@[simp] theorem mem_seventhRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (z : SevenCyclotomicDegreeSixInt.Ring) :
    z ∈ seventhRootKernel r hr0 hr7 hr1 ↔ evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 z = 0
```

```lean
theorem evalCyclotomicFromSeventhRoot_surjective {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Function.Surjective (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1)
```

```lean
theorem seventhRootKernel_isMaximal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (seventhRootKernel r hr0 hr7 hr1).IsMaximal
```

```lean
theorem seventhRootKernel_isPrime {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (seventhRootKernel r hr0 hr7 hr1).IsPrime
```

```lean
theorem seventhRootKernel_comap_ofReal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal.comap ofReal (seventhRootKernel r hr0 hr7 hr1) =
      RingHom.ker (evalRealFromSeventhRoot r hr0 hr7 hr1)
```

```lean
theorem seventhRootKernel_comap_intCast {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring)
      (seventhRootKernel r hr0 hr7 hr1) = Ideal.span ({(q : ℤ)} : Set ℤ)
```

```lean
theorem seventhRootKernel_cardQuot {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Submodule.cardQuot (seventhRootKernel r hr0 hr7 hr1) = q
```

```lean
theorem evalCyclotomic_linearFactor_eq_zero_iff {q : ℕ} [Fact (Nat.Prime q)]
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (c g : ℕ) (hc : ¬ q ∣ c) :
    evalCyclotomicFromSeventhRoot s hs0 hs7 hs1 (gtailCyclotomicLinearFactor c g) = 0 ↔
      s = gtailSevenTailRatio q c g
```

```lean
theorem seventhRootKernel_separating_element {q : ℕ} [Fact (Nat.Prime q)]
    (r s : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1) (hrs : r ≠ s) :
    zeta - ofReal (r.val : SevenRealCubicInt) ∈ seventhRootKernel r hr0 hr7 hr1 ∧
      zeta - ofReal (r.val : SevenRealCubicInt) ∉ seventhRootKernel s hs0 hs7 hs1
```

```lean
theorem seventhRootKernel_ne {q : ℕ} [Fact (Nat.Prime q)]
    (r s : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1) (hrs : r ≠ s) :
    seventhRootKernel r hr0 hr7 hr1 ≠ seventhRootKernel s hs0 hs7 hs1
```

```lean
theorem gtailCyclotomicLinearFactor_unique_address {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c)
    (s : ZMod q) (hs0 : s ≠ 0) (hs7 : s ^ 7 = 1) (hs1 : s ≠ 1)
    (hsr : s ≠ gtailSevenTailRatio q c g) :
    gtailCyclotomicLinearFactor c g ∈ seventhRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) ∧
      gtailCyclotomicLinearFactor c g ∉ seventhRootKernel s hs0 hs7 hs1
```

## Numeric and generic examples

新 test は23 examples。q43 で r11、s35=11²、両根の七乗一・非零・非 identity・相違を有限計算で確認。
両 degree-six evaluations は ζ をそれぞれ11/35へ送る。
K11/K35 の maximal / prime、整数と real-cubic contraction、quotient cardinal43 を一般定理で適用した。
F(9,4)=ofReal13−ζ*ofReal9 は K11 に属し K35 に属さない。
13−35*9≠0 は finite check と actual RingHom evaluation の両方で検証。
ζ−ofReal11 は K11 に属し K35 に属さず、一般 separating-element theorem から K11≠K35 を確認。
canonical Tail ratio の root proof terms を用いた unique-address theorem の適用も検証。
proof arguments は Prop の certificate であり、同じ root / hom の比較に phantom packet を持ち込まない。

元の q43 Q/T divisibility、t37、`¬Fermat7Equation 5 8 9` を再確認。
q13 gap の q|g、q∤T、ratio1、および既存 q7 `ramifiedEval_zeta` を保持。
q43 の coordinate balance/coprime と q13 q|Q は Step018 regression にも保存される。
追加 false-branch control：c=g=0 の F=0 は K11 と K35 の両方に入る。
これは c-unit を除いた一意性が偽であるという explicit witness。

Optional Phase4 は public adapter を増やさず test の一般 extensional equality example として検証。
実際に supplied `a : CyclotomicLinearPrimeAddress p q` とその canonical scalar ratio の root certificates を引数とし、
新 RingHom = a.eval を signed-coordinate formulas で確認する。
β の展開は unit inverse / scalar inverse の coercion を含め定義的に一致。
実 scalar root を同じものに指定する contract であり、自然数 q43 tuple から a/p を構成しない。
old evalKernel equality は追加 public theorem としては証明していない。

## Lean 結果からの観察・提案

**確認済み:** Tail factor の向きは c の可逆性で一意になる。
q|Q はこの uniqueness theorem に使わず、Eisenstein 側の別 root receiver の前提としてのみ残る。
今回の uniqueness は supplied nontrivial seventh-root kernels の範囲であり、degree-six ring の全 prime ideals の分類ではない。

**確認済み:** distinct kernels は同じ rational prime `(q)` に contract し、同じ quotient cardinal q を持ち得る。
q43 の K11 と K35 が実例。整数側の contraction / residue field の同型だけで ideal identity は決まらない。
共通 ZMod codomain を持つ Eisenstein kernel との equality / transport も導かない。

**確認済み:** w=ζ−ofReal(r.val) は integral degree-six source に存在する実 witness。
q43 で F が一つの root kernel に属し他には属さないことは genuine ideal membership fact だが、
Fermat equation が偽な satisfiable sample でも成立するため、新 FLT7 obstruction ではない。

**未実装の提案:** supplied old packet address 上の今回の map equality を薄い public compatibility lemma に昇格する場合は、
old/new kernel equality を actual map equality から導く形が候補。
自然数 Tail ratio が任意の旧 signed packet の canonical ratio に一致する命題は別途証明が必要。
optional `q|T ↔ r⁷=1` converse は今回試行しない。既存 shell identity と gap-unit cancellation に基づく将来候補だが、
今回の kernel / uniqueness には不要。六 kernel product、exact ideal exponents、unit class、primitive next tuple と descent は未実装。

## Validation and repairs

Cwd `/home/deskuma/develop/lean/dkmath/lean/dk_math`。sequential incremental focused builds、process-local LEAN_NUM_THREADS=2。
logs は ignored `.lake/build/gtail-step020/`、永続 archive ではない。

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicPrimeAddress` | 1 | 14.51 | `.lake/build/gtail-step020/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailCyclotomicPrimeAddress` | 0 | 15.19 | `.lake/build/gtail-step020/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 1 | 15.98 | `.lake/build/gtail-step020/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 0 | 19.76 | `.lake/build/gtail-step020/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 1 | 17.56 | `.lake/build/gtail-step020/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 1 | 18.35 | `.lake/build/gtail-step020/06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicPrimeAddress` | 0 | 20.14 | `.lake/build/gtail-step020/07-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRealTraceResidue` | 0 | 2.02 | `.lake/build/gtail-step020/08-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailCyclotomicLocalEval` | 0 | 8.72 | `.lake/build/gtail-step020/09-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPairedResidue` | 0 | 8.01 | `.lake/build/gtail-step020/10-build.log` |

途中失敗01：real contraction の RHS kernel membership を `change` の明示的な zero evaluation に揃えて02で成功。
unused simp argument も削除した。03：local notation K11/K35 に dot-property notation を直接付けたため解析が失敗。
`(K11).IsMaximal/IsPrime` に直し04で required numeric tests が成功。
05：optional comparison の broad simp が maxRecDepth。coordinate expression への explicit change に修正。
06：β 展開で既に goal が解けた後の inverse rewrite が不要だった。削除して final comparison を検証。
定理の意味を変えず、placeholder / maxRecDepth 引き上げで隠す処理はしていない。

最終 focused production02 / test07 は exit0。Step019 neutral test08、carrier test09、Step018 test10 も exit0。
新規 public 十二宣言の `#print axioms` は test07 log に記録、名前別照合で全件
`[propext, Classical.choice, Quot.sound]`。sorryAx なし。
最終新規 production/test に warning なし。禁止構文検査は新規二 Lean ファイルの
sorry/admit/axiom/unsafe/native_decide/sorryAx/False.elim が零。
MIT License / Authors header と import 後の file print を確認。

Comment / string を除いて import header を読んだ source closure：
既存 neutral trace1907 modules（local20）、新 production8927（local147）、新 test8936（local156）。
local union156 vertices の DAG に循環なし。neutral trace closure に FLT は零。
full `DkMath.FLT.Seven` facade は新 production closure に含まれない。
source closure count は今回新規 build した modules の数ではない。
旧 linear-address import は optional comparison test のみ直接追加され、production direct import は一つ。

既存 tracked sources / packet owners / facade / root driver / historical reports / ledger は HEAD と同一。
ROADMAP の旧 bytes は prefix として完全保存し、post019 entry のみ追記。
`git diff --check` と新規 untracked 四ファイルの whitespace check は通過。
ローカル evidence は `runs.json` / `imports.json` / `audit.json`。

STOP after Step020。six-kernel product / ideal valuation hierarchy、source-ring embedding、class group、
unit extraction、primitive tuple、unconditional FLT7 closure と descent は主張しない。
