# Report 016 — ramified three: principal kernel and P²=(3)

Date: 2026-10-10 (JST). **Step016 COMPLETE / Outcome B.** Initial clean HEAD `b4543fe0c6383899be70ecb3d05f0b2542fedabe`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 結果と変更対象

既存の integral ring TraceOneInt(-1) で π=1+τ、normπ=3、ππ=ofInt(-1)3*τ、τ(1-τ)=1 を確認した。root2の kernel Pについて、任意のsigned integral z に対する membership⇔π∣z を既存格子判定から証明し、**P=span{π} と P*P=eisensteinScalarIdeal3** を証明した。

P∩P=P≠(3) の過去の反例は保持され、P²=(3) と並べて検査できた。product proof は実際の principal generators と単元の逆元を使い、split-case comaximality を使用していない。class-number/UFD、cyclotomic移送、FLT7閉包・下降は主張しない。

変更対象は `DkMath/Lib/NumberTheory/GTailSevenRamifiedThreeIdeal.lean`、`DkMathTest/NumberTheory/GTailSevenRamifiedThreeIdeal.lean`、source-inventory-016、report-016、ROADMAP追記。２定義・15公開定理、26 examples。既存の MIT header、import後の file print、namespace/indent スタイルを維持した。

## 全公開署名

namespace `DkMath.Lib.NumberTheory`、open `DkMath.NumberTheory.TraceOneQuadratic`。

```lean
theorem eisensteinThreeRoot : (2 : ZMod 3) ^ 2 - 2 + 1 = 0

def eisensteinThreeGenerator : TraceOneInt (-1)

theorem eisensteinThreeGenerator_eq :
    eisensteinThreeGenerator = (⟨1, 1⟩ : TraceOneInt (-1))

theorem norm_eisensteinThreeGenerator : norm eisensteinThreeGenerator = 3

theorem eisensteinThreeGenerator_mul_self :
    eisensteinThreeGenerator * eisensteinThreeGenerator = ofInt (-1) 3 * tau (-1)

theorem eisenstein_tau_mul_inverse : tau (-1) * (1 - tau (-1)) = 1

theorem scalar_three_dvd_eisensteinThreeGenerator_square :
    ofInt (-1) 3 ∣ eisensteinThreeGenerator * eisensteinThreeGenerator

theorem eisensteinThreeGenerator_square_dvd_scalar_three :
    eisensteinThreeGenerator * eisensteinThreeGenerator ∣ ofInt (-1) 3

def eisensteinThreeRamifiedIdeal : Ideal (TraceOneInt (-1))

theorem mem_eisensteinThreeRamifiedIdeal_iff_coordinates (z : TraceOneInt (-1)) :
    z ∈ eisensteinThreeRamifiedIdeal ↔ (3 : ℤ) ∣ z.fst - z.snd

theorem eisensteinThreeGenerator_dvd_iff_coordinates (z : TraceOneInt (-1)) :
    eisensteinThreeGenerator ∣ z ↔ (3 : ℤ) ∣ z.fst - z.snd

theorem mem_eisensteinThreeRamifiedIdeal_iff_dvd (z : TraceOneInt (-1)) :
    z ∈ eisensteinThreeRamifiedIdeal ↔ eisensteinThreeGenerator ∣ z

theorem eisensteinThreeRamifiedIdeal_eq_span :
    eisensteinThreeRamifiedIdeal =
      Ideal.span ({eisensteinThreeGenerator} : Set (TraceOneInt (-1)))

theorem eisensteinThreeGenerator_mem_ramifiedIdeal :
    eisensteinThreeGenerator ∈ eisensteinThreeRamifiedIdeal

theorem eisensteinThreeGenerator_square_mem_scalarIdeal :
    eisensteinThreeGenerator * eisensteinThreeGenerator ∈ eisensteinScalarIdeal 3

theorem eisensteinThreeGenerator_square_span_eq_scalarIdeal :
    Ideal.span ({eisensteinThreeGenerator * eisensteinThreeGenerator} : Set (TraceOneInt (-1))) =
      eisensteinScalarIdeal 3

theorem eisensteinThreeRamifiedIdeal_mul_self :
    eisensteinThreeRamifiedIdeal * eisensteinThreeRamifiedIdeal = eisensteinScalarIdeal 3
```

generator の定義本体は `1 + tau (-1)`、ramifiedIdeal は `eisensteinResidueIdeal (2 : ZMod 3) eisensteinThreeRoot`。P² の Lean署名は actual ideal multiplication P*P。

## 証明経路と前提

πとτの有限な座標等式は既存 ring operations の small decide で確認した。これは元レベルの等式であり、norm値からunitを仮定する方法ではない。scalar3∣ππ の witness はτ、ππ∣scalar3の witness は1-τ。後者は actual product equality と inverse identity を結合して証明した。

kernel membership は root2=-1 のもとで fst_cast-snd_cast=0 と同値、integer cast iff から3∣fst-sndに接続した。π-divisibilityには既存 `traceOne_dvd_iff_norm_dvd_mul_conj_coordinates` を **normπ≠0** の明示証明とともに適用した。conjπ=⟨2,-1⟩ による両座標の3整除を、差fst-sndの3整除へ正確に変換した。任意signed z の iff なので、ideal extensionality と Ideal.mem_span_singleton で kernel全体の principal equality を得た。

principal-kernel equality が02で通ってから、03で product stage を追加した。Ideal.span_singleton_mul_span_singletonでP*P=span{ππ}、両 integral generator divisibility とspan_singleton_le_span_singletonの２方向からspan{ππ}=(scalar3)を証明した。追加 IsDomain/IsUnit instance、surrogate axiom、PとPのcoprimality仮定は不要だった。scalar3は同じ TraceOneInt(-1) の `ofInt(-1)3` であり、integer norm ideal ではない。

## API inventory と import

詳細は [source-inventory-016.md](source-inventory-016.md)。new production は Step015 neutral module（scalar idealを再利用）とTraceOneLatticeLandingのみ、testはnew productionのみを直接import。既存 ring、lattice、Step010–015 statements は変更していない。

EisensteinCoordinates の第二座標の符号と、τ²=τ-1の convention を確認した。ππのliteral pairは⟨0,3⟩であり、3τと一致する。別generator convention の符号を持ち込まない。

## Sequential incremental focused builds

cwd=`lean/dk_math`、process-local `LEAN_NUM_THREADS=2`。全実行履歴:

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal` | 1 | 3.88 | `.lake/build/gtail-step016/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal` | 0 | 3.91 | `.lake/build/gtail-step016/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal` | 0 | 3.81 | `.lake/build/gtail-step016/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal` | 1 | 4.02 | `.lake/build/gtail-step016/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal` | 0 | 4.38 | `.lake/build/gtail-step016/05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal` | 0 | 1.62 | `.lake/build/gtail-step016/06-build.log` |

最終版の新production/new test/Step015 regression はすべてexit0。Full clean/all-test buildは実行していない。

01はinteger literal3とCharP lemmaのnatural-cast3のrewrite不一致。明示的に型を指定したhcast iffを `simpa` で作り、その逆方向をrewriteする形に修正した。convertのunnecessarySeqFocus lintにも従って単一goalのsequenceにした。02はprincipal equalityまで成功したが unused Int.cast_sub simp argumentのlintが残ったため除去し、03でproductを含むfinal productionがwarningなしで成功。

04はtestの `inf_idem` が∀aという明示引数を持ち、単独のtermではgoal型に合わなかった。`inf_idem _`として05で26 examplesが成功。数学的命題・仮定の変更はしていない。06でStep015 targetを変更せずreplayした。

## Public #print axioms

05の全17新公開シンボルを（折返し行を含め）抽出した。noneはaxiom依存なし、その他は標準基礎のみ。import元の旧 lattice / Eisenstein axiom printsを新規数へ加算していない。

| Symbol | Axioms |
|---|---|
| `eisensteinThreeRoot` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinThreeGenerator` | `none` |
| `eisensteinThreeGenerator_eq` | `none` |
| `norm_eisensteinThreeGenerator` | `[propext]` |
| `eisensteinThreeGenerator_mul_self` | `none` |
| `eisenstein_tau_mul_inverse` | `none` |
| `scalar_three_dvd_eisensteinThreeGenerator_square` | `[propext]` |
| `eisensteinThreeGenerator_square_dvd_scalar_three` | `[propext]` |
| `eisensteinThreeRamifiedIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `mem_eisensteinThreeRamifiedIdeal_iff_coordinates` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinThreeGenerator_dvd_iff_coordinates` | `[propext, Classical.choice, Quot.sound]` |
| `mem_eisensteinThreeRamifiedIdeal_iff_dvd` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinThreeRamifiedIdeal_eq_span` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinThreeGenerator_mem_ramifiedIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinThreeGenerator_square_mem_scalarIdeal` | `[propext, Quot.sound]` |
| `eisensteinThreeGenerator_square_span_eq_scalarIdeal` | `[propext, Quot.sound]` |
| `eisensteinThreeRamifiedIdeal_mul_self` | `[propext, Classical.choice, Quot.sound]` |

## Leanで検査したexampleと観察

- π=⟨1,1⟩、normπ=3、conjπ=⟨2,-1⟩、ππ=3τ、τ(1-τ)=1。逆順の積とliteral pair⟨0,3⟩/⟨1,-1⟩による独立 finite checkも通った。
- π∈P、π∉I3、ππ∈I3、P=span{π}、P*P=I3。generic principal theoremと両generator divisor endpointsを実際に適用した。
- P*P=I3 と P⊓P≠I3 を同じexampleで確認した。πの membership/nonmembership witnessでinf inequalityを証明した。P⊓P=P、P⊔P≠⊤も確認し、product=infを適用できない状況であることを検査した。
- z=⟨-2,1⟩はfst-snd=-3なのでPに属し、new arbitrary-element iffからπ∣zを導いた。独立のliteral quotient z=π*⟨-1,1⟩も確認した。
- z=⟨-43,86⟩の差=-129についてもnew generic coordinate/divisibility receiversから membershipとπ整除を確認した。z=⟨1,0⟩はPに属さない。
- 任意signed integral zの `z∈P↔π∣z` の汎用署名をtestで適用した。
- Step015 targetをそのままreplayし、q43 split inf/product/sup、q3 failed intersection、q5 no-root の既存境界を保った。新しいq-general decomposition classificationは追加していない。

normπ=3だけではkernelをprincipalと同定できない。今回の同定はkernelの線形合同と、非零normを使う両conjugate-product座標判定を一致させた結果である。またππのscalar3との関係にはτというunit因子が残るが、explicit inverseで主イデアルの両包含を証明できた。元の等式とideal equalityで必要な正規化を混同しないことが重要である。

## 次に試す命題・実装提案（未実施）

1. 利用先が必要なら、Pの元 z=⟨f,s⟩ のπ-quotientを `⟨(2*f+s)/3,(-f+s)/3⟩` と明示する adapter を検討できる。今回のnorm/lattice criterionはその両分子のdivisibilityを証明するが、整数除算formulaをpublic APIとしてはまだ実装していない。signed exampleのliteral quotientは確認済み。
2. scalar/eval normalizationの再利用として、τのunitをbundled Unitsにすることも候補。今回はexplicit integral inverseで必要な比較が済み、追加unit hierarchyを作っていない。
3. q3でのprincipal square equalityは局所的なdegree-two結果であり、ideal valuation、任意norm-squareから元のsquare/unit-squareの復元、cyclotomic ideal class/unit-power classやFermat packetへの移送には別のtyped contractが必要。今回は実装していない。

Step015時点のramified product候補は今回、別の正しい証明経路で成立すると確定した。歴史的intersection counterexampleを取り消す必要はない。classical ramified identityとしてOutcomeB、独立の新FLT7obstruction/closureではない。Step016で停止。

## Final source/graph audit

新規２ Lean source に sorry/admit/new axiom/unsafe/False.elim/exfalso/native_decide/FLT impossibility endpoint の禁止構文なし。新productionにmul_eq_inf_of_coprimeの呼出しなし。末尾改行・行末空白検査成功。最終production/test/Step015 regressionログにwarning/errorなし。新規文書とROADMAP追記も空白検査に成功し、旧本文を保存した。

Comment-stripped import-header closure: production1367 source names/15 local modules、test1368/16。local union16 verticesのDFSにcycleなし、neutral closureにFLT moduleなし。結果 `.lake/build/gtail-step016/imports.json`。external terminalsを含むsource countsであり、build jobsや全依存のhole/axiom auditではない。

HEADとbyte比較した既存59ファイル（存在するroot/test driver、Lake/toolchain/facade、ring/residue/lattice/coordinate owners、GTail neutral/FLT ownersと対応tests、歴史的ledgerと直前reports/review）は変更なし。tracked diffは `git diff --check`、新規source/docの空白は別検査で確認した。
