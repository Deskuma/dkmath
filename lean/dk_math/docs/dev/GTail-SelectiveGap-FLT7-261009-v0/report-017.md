# Report 017 — selected-element ideal-square support

Date: 2026-10-10 (JST). **Step017 COMPLETE / Outcome B.** Initial clean HEAD `d51ce5d48ccf06eaeee84d4bc9bed40caf4e1f5b`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 結果と範囲

任意の signed integral z に対し、integer norm の3整除を repeated-root kernel membershipに同定し、actual ideal multiplication と P²=(3) から **embedded scalar3∣z*z** を証明した。自然数 α(a,b) の actual squareへの adapterも追加した。scalar3∣z自体は結論していない。

split側は、supplied rootとその分離、baseのmembership/共役側exclusionのもと、z*z∈P_t²、z*z∉P_bar、z*z∉(q)を証明した。canonical α adapterも既存のzero/nonzero orientationから取得した。これは理想平方のsupportであり、exact P-adic exponentや(z²)=P²の主張ではない。Fermat前提はすべての新定理で不要。

変更対象は `DkMath/Lib/NumberTheory/GTailSevenIdealSquareAddress.lean`、`DkMathTest/NumberTheory/GTailSevenIdealSquareAddress.lean`、source-inventory-017、report-017、ROADMAP追記。７公開定理、新definitionなし、22 examples。既存MIT header、import後のfile print、namespace/indentスタイルを維持した。

## Exact public signatures

namespace `DkMath.Lib.NumberTheory`、open `DkMath.NumberTheory.TraceOneQuadratic`。

```lean
theorem three_dvd_norm_iff_mem_ramifiedIdeal (z : TraceOneInt (-1)) :
    (3 : ℤ) ∣ norm z ↔ z ∈ eisensteinThreeRamifiedIdeal

theorem scalar_three_dvd_square_of_dvd_norm (z : TraceOneInt (-1))
    (hnorm : (3 : ℤ) ∣ norm z) : ofInt (-1) 3 ∣ z * z

theorem scalar_three_dvd_gtailSevenNormCoord_sq {a b : ℕ}
    (hQ : 3 ∣ a ^ 2 + a * b + b ^ 2) :
    ofInt (-1) 3 ∣ (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2

theorem square_mem_eisensteinResidueIdeal_mul_self {q : ℕ} (t : ZMod q)
    (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal t ht) :
    z * z ∈ eisensteinResidueIdeal t ht * eisensteinResidueIdeal t ht

theorem square_not_mem_conjugate_eisensteinResidueIdeal {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (z : TraceOneInt (-1))
    (hnot : z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)) :
    z * z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)

theorem split_eisenstein_square_address {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t)
    (z : TraceOneInt (-1)) (hz : z ∈ eisensteinResidueIdeal t ht)
    (hnot : z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)) :
    z * z ∈ eisensteinResidueIdeal t ht * eisensteinResidueIdeal t ht ∧
      z * z ∉ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) ∧
      z * z ∉ eisensteinScalarIdeal q

theorem gtailSevenNormCoord_split_square_address {q a b : ℕ} [Fact (Nat.Prime q)]
    (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hb : ¬ q ∣ b) :
    (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∈
        eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb) *
          eisensteinResidueIdeal (gtailSevenResidueRoot q a b) (gtailSevenResidueRoot_polynomial hQ hb) ∧
      (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉
        eisensteinResidueIdeal (1 - gtailSevenResidueRoot q a b)
          (gtailSevenResidueRoot_conjugate_polynomial hQ hb) ∧
      (gtailSevenNormCoord a b : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal q
```

## Proof dependencies and scope audit

norm3 iffはStep014のprime norm-divisor disjunctionをq3,t2へ適用し、kernel membership iffを先にevalへrewriteしてから1-2=2とor_selfを使う。root proofに依存するidealの型へ直接rewriteしていない。実際のP=Step016 repeated-root kernelへ接続した。

ramified square liftはz∈PからIdeal.mul_mem_mulでz*z∈P*Pを得て、Step016 P*P=(3)をrewriteし、Ideal.mem_span_singletonでembedded3のring-element divisibilityを取得した。norm-only converseやcoordinate positivityを仮定していない。natural adapterはStep012のnorm-divisor iffとpow_twoを使う。

splitのsquare membershipは実際のideal product APIから出る。conjugate exclusionはchecked maximalityを設置してIsPrimeを取得し、squareがkernelに入ればbaseが入るというmem_or_memを使用した。scalar exclusionはStep015 separated intersection equalityをrewriteし、conjugate membershipに反することから証明した。q∣norm zだけで向きを仮定していない。

canonical adapterは既存の自然数α orientationを消費し、α²のpow記法に合わせた。selected Bodyのnorm squareに登場する選ばれたactual element α²が対象で、同じnorm Q²を持つ任意の別βへ移していない。

## Existing API comparison and optional owner

詳細な型・依存・４種のsupportの区別は [source-inventory-017.md](source-inventory-017.md)。new productionの唯一の直接importはStep016 neutral module、testはnew productionのみ。新しい環、素イデアル型、ideal valuation hierarchyを作っていない。

Step010/011 FLT receiversをsource-onlyで比較した。Step011のq=3 routingはpositive primitive exact Fermat/sum条件などのもと9∣gを与える既存receiverとして読める。今回のneutral scalar3∣α²との単なるconjunctionはtyped carrier transportを追加しないため、optional FLT ownerは作成しなかった。新しいFLTequation整合性/矛盾を検査したとは主張しない。

## Sequential incremental focused builds

cwd=`lean/dk_math`、process-local `LEAN_NUM_THREADS=2`。実行履歴:

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 3.83 | `.lake/build/gtail-step017/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 4.59 | `.lake/build/gtail-step017/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal` | 0 | 1.62 | `.lake/build/gtail-step017/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal` | 0 | 1.73 | `.lake/build/gtail-step017/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenIdealSquareAddress` | 0 | 4.49 | `.lake/build/gtail-step017/05-build.log` |

01はproduction、02はinitial tests、03/04はunchanged Step016/015 regression、05は両signed square coordinatesの43非整除を明示的に追加したfinal tests。すべてexit0。Leanの失敗/修正試行なし。Full clean/all-test buildは実行していない。

## Public #print axioms

05の新公開７定理を折返し行も含め抽出・確認した。標準基礎のみ。import元の既存Eisenstein/lattice axiom printsを新規数と混同しない。

| Symbol | Axioms |
|---|---|
| `three_dvd_norm_iff_mem_ramifiedIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `scalar_three_dvd_square_of_dvd_norm` | `[propext, Classical.choice, Quot.sound]` |
| `scalar_three_dvd_gtailSevenNormCoord_sq` | `[propext, Classical.choice, Quot.sound]` |
| `square_mem_eisensteinResidueIdeal_mul_self` | `[propext, Classical.choice, Quot.sound]` |
| `square_not_mem_conjugate_eisensteinResidueIdeal` | `[propext, Classical.choice, Quot.sound]` |
| `split_eisenstein_square_address` | `[propext, Classical.choice, Quot.sound]` |
| `gtailSevenNormCoord_split_square_address` | `[propext, Classical.choice, Quot.sound]` |

## Kernel-checked examples と観察

- π=⟨1,1⟩: normπ=3、embedded3∤π、π∈P3、π∉(3)。新generic square liftからembedded3∣ππを取得し、ππ∈P3*P3=(3)も検査した。
- signed z=⟨-2,1⟩: norm z=3をfinite computationで確認し、新generic theoremからscalar3∣z*zを取得。actual square=⟨3,-3⟩も確認した。generic resultをliteral checkのみで代替していない。
- α=⟨5,8⟩: normα=129=3*43、α²=⟨-39,144⟩、normα²=129²。existing multiplicative norm-square theoremも使用した。
- α∈P37、α∉P7。新split receiverからαα∈P37²、αα∉P7、αα∉(43)を取得。canonical ratioのpow-square adapterも適用した。
- integer norm上は43∣normα、43²∣normα²。一方、embedded43∤α²であり、signed coordinates -39/144のどちらにも43整除がないことを別のfinite exampleで確認した。これはunqualified q∣norm z⇒embedded q∣z²のsplit-prime反例。
- 同じα²にはembedded3整除が成立する。ramified3のreceiverとsplit43のcountercheckを同じactual elementで比較でき、norm-prime supportを全qへ一律にscalar-square supportと扱えないことが見えた。
- q3のrepeated root、q5のno-rootをsmall finite checksで再確認した。Step016/015のunchanged regressionも通り、ramifiedproductとsplit/inert境界を維持した。
- 任意signed integral zに対するnew ramified theoremの汎用署名適用も検査した。

新split square membershipは少なくともP²に入るというsupportを与えるが、P³に入らないことを与えない。norm value、element scalar divisibility、ideal-square membership、exact ideal orderを同一視しない。

## 次に試す命題・実装提案（未実施）

1. Optional converse `embedded3∣z²⇒3∣norm z` は将来の小さなAPI候補。scalar ideal membershipをP²へrewriteし、そのP包含とPのprimalityからz∈Pを得てnew norm iffへ戻す経路を検討できる。今回はrequired forward liftだけを実装し、このconverseを検証済みとは記載しない。
2. 同じsplit square-addressの任意signed z版を別のexplicit root calibrationへ適用できるが、exact exponentを言うには次のideal power exclusionを別途証明する必要がある。今回その理論を作っていない。
3. selected GTail scalar productとこのdegree-two ideal supportをcyclotomic carrierへ移すには、具体的なring/ideal map、単元・符号のnormalizationと既存packetとの互換性が必要。positive primitive next tuple、Fermat equation保存と下降は依然未実装。

OutcomeB: nonvacuous ramified scalar square-liftとoriented split ideal-square support。独立の新FLT7obstruction/closureではない。Step017で停止。

## Final source/graph audit

新規２ Lean source に sorry/admit/new axiom/unsafe/False.elim/exfalso/native_decide/FLT impossibility endpoint の禁止構文なし。末尾改行・行末空白検査成功。最終production/testと両regressionログにwarning/errorなし。新規文書とROADMAP追記の空白検査も成功し、旧ROADMAP本文を保存した。

Comment-stripped import-header closure: production1368 source names/16 local modules、test1369/17。local union17 verticesのDFSにcycleなし、neutral closureにFLT moduleなし。結果 `.lake/build/gtail-step017/imports.json`。external terminalsを含むsource countsであり、build jobsや全依存のhole/axiom auditではない。

HEADとbyte比較した既存60ファイル（存在するroot/test driver、Lake/toolchain/facade、ring/residue/lattice/coordinate owners、GTail neutral/FLT ownersと対応tests、歴史的ledgerと直前reports/review）は変更なし。tracked diffは `git diff --check`、新規source/docの空白は別検査で確認した。
