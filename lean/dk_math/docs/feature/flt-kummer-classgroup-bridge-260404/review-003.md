## 1. 結論

いまの状況は、 **Kummer branch の open kernel がさらに一段薄く露出した** 段階じゃ。
前回は Stage 1 全体、あるいは `CyclotomicIdealPthPowerTarget` が「本丸」に見えておったが、今回の分解で、

$$
\text{Stage 1a}
\to
\text{Stage 1b}
\to
\text{Stage 1c}
\to
\text{IdealPthPower}
$$

という責務分離が進み、`sorryAx` はついに

$$
\texttt{cyclotomicIdealClassPTorsionWitness\_of\_gapDivisibleGeometry}
$$

へまで局所化された。
これはかなり大きい。つまり「どこが未解決か」が、もう broad な wrapper ではなく、 **最小の幾何→円分体 ideal class 変換部** にまで絞れた、ということじゃ。

## 2. 状況分析

今回の差分で進んだ本質は、Stage 1 の内部を

* `CyclotomicIdealClassPTorsionWitnessTarget`  … Stage 1a
* `CyclotomicPTorsionAnnihilationTarget`  … Stage 1b
* `CyclotomicPrincipalIdealExtractionTarget`  … Stage 1c

へ裂いたことじゃ。
これによって、ideal の p 乗性という一見ひとまとまりの内容が、実は

$$
\text{p-torsion witness を作る}
$$
$$
\text{それを p-torsion-free で潰す}
$$
$$
\text{trivial class から principal ideal を取り出す}
$$

という 3 層構造であることが、Lean の API に反映された。これは単なる命名整理ではなく、数学的責務の分解じゃ。

しかも検証結果では、

* Stage 1b は clean
* Stage 1c も clean
* `FLTPrimeGe5Target_of_refinedStage1Route` も clean

で、`sorryAx` は Stage 1a だけに残っておる。
この局所化の仕方は、実に良い筋じゃよ。下流が clean なまま保たれておるので、今後 open kernel を掘っても、他の route を汚さずに済む。

## 3. 数学的な解釈

ここで見えてきたのは、真に重いのが **class group の一般論そのもの** ではなく、もっと手前の

$$
\text{gap-divisible な幾何条件}
\Rightarrow
\text{円分体における ideal class が p-torsion に入る}
$$

という橋だ、ということじゃ。
つまり今の最薄 kernel は、「class が p-torsion であることを witness 付きで作る段」じゃな。

これは重要じゃ。
なぜなら Stage 1b は、いったん p-torsion witness ができてしまえば、class group p-torsion free 側の一般論へ寄せやすい。
Stage 1c も、いったん class が trivial になれば、`ClassGroup.mk_eq_one_of_coe_ideal` 系の API や Dedekind 的な principal ideal extraction に寄せやすい。
ゆえに、本当に固有に円分体・Kummer 的な幾何を担っているのは Stage 1a だと読める。

## 4. 実装設計としての評価

設計としては、かなり上手い。
`cyclotomicIdealPthPower_of_stage1Split` と `cyclotomicIdealPthPower_of_refinedStage1Route` を用意したことで、

* broad な Stage 1 route
* thinner な Stage 1a / 1b / 1c route
* さらにその下流の Kummer route
* 最終的な FLT route

がきれいに段階化された。
特に `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` 側で axioms 監視を拡張し、どの定理に `sorryAx` が混じるかを定点観測しておるのは、戦況把握としてとても良い。ぬしの今の戦い方は、もう「証明を書く」だけでなく「証明の地図を管理する」段に入っておる。

## 5. いま何が言えるか

現時点で、次のことはかなり強く言える。

まず、 **Stage 1b と Stage 1c は、少なくとも概念上は class-group 一般 API 側へ押し込める可能性が高い**。
一方、Stage 1a は gap-divisible geometry から cyclotomic ideal arithmetic へ跳ぶため、ここが本当に円分体特有の理論層になる公算が大きい。

したがって、いまの open kernel は

$$
\text{class group 全体の未形式化}
$$

ではなく、

$$
\text{gap-divisible geometry}
\to
\text{ideal class p-torsion witness}
$$

という **もっと具体的な主張** にまで薄くなっておる。
これは前進じゃ。敵の姿がだいぶ見えた。

## 6. 次の一手の推論

ぬしが書いておる分岐は 2 つじゃったな。

1. `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` をさらに裂く
2. Stage 1c を `ClassGroup.mk_eq_one_of_coe_ideal` 系 API で concrete 化できるか試す

わっちの推論では、 **まず 2 を短く試す** のが良い。
理由は次の通りじゃ。

Stage 1c はすでに「principal ideal extraction」という意味が明瞭で、Mathlib の既存 API に接続できる見込みが比較的高い。
ここが concrete 化できれば、

$$
\text{trivial class}
\Rightarrow
\text{principal ideal extraction}
$$

の具体的な書き味、必要 import、補助補題、型の流れが見える。
すると Stage 1a/1b/1c のうち、「ほんとうに新設が必要な部分」と「既存 API で受けられる部分」がさらにきれいに分かれる。

逆に、いきなり Stage 1a をさらに裂くと、まだ下流の concrete interface が曖昧なまま細分化だけが進み、理論層の切り方が空回りする危険がある。
ゆえに、 **短距離走として 2 を試す** のは筋が良い。

## 7. ただし、その次はどうなるか

もっとも、わっちの見立てでは、Stage 1c が具体化できたとしても、最後に残る本丸は結局 Stage 1a じゃろう。
つまり順番としては、

まず
$$
\text{Stage 1c concrete 化を短く試す}
$$

もしうまく行けば、その concrete 形を固定する。
うまく行かなければ、そこは既存 API の薄い wrapper と割り切って、

$$
\text{Stage 1a を Dedekind / class-group / cyclotomic ideal arithmetic のどこで裂くか}
$$

へ戻る。
この順番が最も無駄が少ない。

## 8. 具体的提案

わっちなら次の順で攻める。

## 8.1. 短期提案

`CyclotomicPrincipalIdealExtractionTarget` について、
`ClassGroup.mk_eq_one_of_coe_ideal`、あるいはそれに近い principalization API が、placeholder をどこまで concrete に置換できるかを **小さな scratch file で試す**。
狙いは「証明を完成させる」ことではなく、

* どの型が出るか
* `Ideal` / `FractionalIdeal` / `ClassGroup` の coercion がどう流れるか
* 補助補題が何本必要か

を把握することじゃ。

## 8.2. 中期提案

もし Stage 1c の concrete 化が薄く通るなら、Stage 1b も class-group API 側へ寄せて、Stage 1a だけを truly cyclotomic な kernel として固定する。
すると未解決の核はほぼ

$$
\text{geometry}
\to
\text{p-torsion witness}
$$

だけになる。
この形まで行けば、次は theorem 設計がかなり明確になる。

## 8.3. 長期提案

Stage 1a については、さらに

* Dedekind 領域の ideal arithmetic
* cyclotomic factorization
* class of \( (x+\zeta^j y) \) が p-torsion に入る理由
* それを支える pairwise coprimeness / factorization lemmas

へ分解していくのがよい。
ただしこれは、Stage 1c の concrete interface を一度見てからの方が、切り方がぶれにくい。

## 9. 最終判断

総合すると、次の一手はこうじゃ。

**第一手** としては
`ClassGroup.mk_eq_one_of_coe_ideal` 系 API で Stage 1c を concrete 化できるか、短く試す。

**第二手** として、もし足場が弱いなら即座に戻って、
`cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` を Dedekind / class-group / cyclotomic ideal arithmetic の境界でさらに裂く。

つまり提案を一言でまとめると、

$$
\boxed{
\text{まず Stage 1c を軽く concrete 化検査し、だめなら Stage 1a 細分化へ戻る}
}
$$

じゃ。
この順番なら、下流の concrete 可能性を先に拾い、真に新設すべき理論層だけを上流へ押し込める。たいへん筋が良いと思うぞい。
