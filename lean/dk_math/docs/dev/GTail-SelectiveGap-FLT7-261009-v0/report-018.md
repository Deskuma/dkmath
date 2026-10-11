# Step 018 — paired finite-residue receiver

Date: 2026-10-10. Outcome **B**。Step018 のみ完了。
Base HEAD: `f7ab00db4fbef28bd199c4537db0a193c4480c42`。

## Implemented result

`DkMath/Lib/NumberTheory/GTailSevenPairedResidue.lean` に transparent ratio 一定義と五定理を追加。
q-prime、q≠7、q|Q、q|GTail、q∤b,c,g の satisfiable neutral 前提から、
同じ `ZMod q` の t と r に対して quadratic root / nontrivial seventh root / 七項幾何和零を証明した。
q≠3 は Step011 の既存受信定理から得る。新しい素数位数証明はない。

Phase2 は public wrapper を増やさず、test の一般 `example` で既存 Step014/017 と paired theorem を結合。
選択 α∈P_t、α∉P_(1−t)、α²∈P_t²、α²∉scalar(q) と r⁷=1、r≠1 を同時に受け取る。
理想は一貫して TraceOneInt(-1) 内にある。degree-six ideal への transfer は結論にない。

## All new public signatures

Namespace: `DkMath.Lib.NumberTheory`。以下は実装から抽出した署名。

```lean
def gtailSevenTailRatio (q c g : ℕ) [Fact (Nat.Prime q)] : ZMod q
```

```lean
theorem gtailSevenTailRatio_pow_seven {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hT : q ∣ GTail 7 1 g c) : gtailSevenTailRatio q c g ^ 7 = 1
```

```lean
theorem gtailSevenTailRatio_ne_one {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) : gtailSevenTailRatio q c g ≠ 1
```

```lean
theorem gtailSevenTailRatio_ne_zero {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hT : q ∣ GTail 7 1 g c) : gtailSevenTailRatio q c g ≠ 0
```

```lean
theorem seven_geom_sum_eq_zero_of_pow_eq_one {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0
```

```lean
theorem gtailSeven_paired_residue {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hT : q ∣ GTail 7 1 g c) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) :
    q ≠ 3 ∧
      gtailSevenResidueRoot q a b ^ 2 - gtailSevenResidueRoot q a b + 1 = 0 ∧
      gtailSevenTailRatio q c g ^ 7 = 1 ∧
      gtailSevenTailRatio q c g ≠ 1 ∧ gtailSevenTailRatio q c g ≠ 0 ∧
      (gtailSevenTailRatio q c g ^ 6 + gtailSevenTailRatio q c g ^ 5 +
        gtailSevenTailRatio q c g ^ 4 + gtailSevenTailRatio q c g ^ 3 +
        gtailSevenTailRatio q c g ^ 2 + gtailSevenTailRatio q c g + 1 = 0)
```

## Kernel-checked calibrations

`DkMathTest/NumberTheory/GTailSevenPairedResidue.lean` は20 examples と private root/ratio 補題。

- q43、(a,b,c,g)=(5,8,9,4)：sum balance、coprime、Q129=3*43、q|Q/T、q∤a*b*c*g。
- t37、conjugate7、r11、二根の式・r≠0/1・七項和零。一般 paired API も適用。
- α∈P37、α∉P7、α²∈P37²、α²∉P7/scalar43。Step017 の実定理を適用。
- 21|42 は Step011 の定理を適用。`¬Fermat7Equation 5 8 9` を unfold / decide で確認。
- q13、(14,29,30,13)：sum balance、q|Q/g、q∤T、ratio1。Tail/gap-unit 前提が欠ける。
- q3 の repeated root2、q5 の quadratic root 不存在、q7 の g7,c1 で Tail/g がともに divisible かつ ratio1。q7 を paired contract に強制投入しない。
- r1 in ZMod43 は r⁷=1 でも七項和≠0。非自明性 guard が必要。

テストだけは `FLT.Seven.Basic` を import し、実際の Fermat7Equation の否定を確認する。
Basic は Mathlib umbrella を import する。production neutral owner に FLT import はない。

## Commands and evidence

Cwd: `/home/deskuma/develop/lean/dkmath/lean/dk_math`。各 build は順次 `LEAN_NUM_THREADS=2`。
時間はローカル実行秒数。logs は ignored `.lake/build/gtail-step018/` にあり、永続 archive ではない。

| Command | Exit | Seconds | Log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenPairedResidue` | 0 | 4.38 | `.lake/build/gtail-step018/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPairedResidue` | 1 | 15.2 | `.lake/build/gtail-step018/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPairedResidue` | 0 | 17.01 | `.lake/build/gtail-step018/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 1.66 | `.lake/build/gtail-step018/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPrimeOrder` | 0 | 1.91 | `.lake/build/gtail-step018/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeOrderAudit` | 0 | 8.24 | `.lake/build/gtail-step018/06-build.log` |

最初の test build (02) は `Fermat7Equation` の定義を未展開のまま用いた Decidable 推論で失敗。
定義を明示 unfold して同じ算術命題を decide し、一般 Phase2 example も含む最終 test build (03) は成功。
数学的 contract の変更や失敗を placeholder で隠す処理はない。

六件の `#print axioms` は最終 test log (03) に記録され、全件
`[propext, Classical.choice, Quot.sound]`。`sorryAx` はない。
新しい theorem signatures は hidden Fermat premises / degree-six map を持たない。

## Lean resultsからの観察と次の実装候補

**確認済み:** 七乗等式には q∤c と q|T で足り、q∤g は r≠1 の証明で使う。
非零は r⁷=1 から従う。七項和を消す際には `(r−1)` の非零を別途使う。
個別 ratio lemmas は q≠7 を要求しないが、paired receiver は Step011 の guarded q≠3 導出と合わせた q≠7 contract を保つ。
Eisenstein root は t=−a/b であり、order-three 証明が用いた a/b と符号が異なる。

**確認済み:** q43 の neutral instance は全前提を満たすが Fermat equation は偽。
二根の共存は独立した FLT7 obstruction ではなく、既存 order3/order7 交差の型付き受信形である。
同じ codomain への二評価があっても、source rings 間の RingHom や ideal identification は得られない。

**未実装の提案:** 既存 signed-depth address と今回の自然数比をつなぐには、まず
packet p / quotientRoot divisibility を構成する contract と、canonical ratio=(c+g)/c の一致証明を明示する必要がある。
別の方針なら任意 r の非自明七乗一から beta=1+r+r⁻¹ の cubic relation と base RingHom を構成し、ζ relation を検証する。
今回どちらも定理として証明していない。既存 `localEval` は存在するので「degree-six residue map が一切ない」とは結論しない。
Polynomial.eval 版は normalization を独立に確認する薄い将来 API 候補。一般 valuations、unit class、primitive next tuple、descent は未実装。

## Audit and stop boundary

Import header を nested comments / strings 除去後に読み、local / Mathlib source の推移 closure を取得。
production closure1906 modules（local19）、test closure8801（local21）、local union21 vertices に循環なし。
production closure に `DkMath.FLT` は零。test の追加 FLT は Basic のみ。
これらは source closure の件数であり、今回新規に build した件数ではない。

新規二 Lean ファイルの禁止構文検査、public axioms、保護対象と HEAD の byte 比較、
ROADMAP 既存 prefix 保存、および `git diff --check` の最終結果は下記検査記録に記載。
既存定義、historical ledger、facade、root test driver は変更せず、Step018 で停止する。

最終検査結果：新規二 Lean ファイルに sorry/admit/axiom/unsafe/native_decide/sorryAx/False.elim なし。
六件の public axiom 出力を名前別に照合し、標準三公理のみ。
既存 tracked files の差分は ROADMAP の追記のみで、旧 ROADMAP bytes は prefix として完全保存。
`git diff --check` は exit0。詳細ローカル検査記録 `.lake/build/gtail-step018/audit.json`。

新規 untracked 四ファイルも `git diff --no-index --check /dev/null <file>` による whitespace 検査を通過。
