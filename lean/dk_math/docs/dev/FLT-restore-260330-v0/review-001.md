# review-001: FLT restore 260330 v0: 状況分析と戦略整理

うむ。いまの状況は、かなりはっきりしておる。

まず、大きな見取り図としては、`dev/FLT-witness-260328-v0` でやっていた witness 探索は develop へマージ済みで、現在の主戦場は `dev/FLT-restore-260330-v0` へ移った。しかも上流 chain の 3 段のうち、`CyclotomicExistence` と `DistinguishedPrimeArithmetic` は既に通っており、残る未完は **`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` ただ 1 段** という整理になっておる。つまり今は、存在補題や distinguished prime の段ではなく、**「原始素因子 witness からどう smaller normal-form packet を再構成するか」** という、無限降下法の深い核そのものを相手にしている段じゃ。

この target が前の `BodyCoreWitness` 系と本質的に違うのは、**前提に FLT 反例 pack の存在が入っている** ことじゃ。前回の偽枝は \((5,5,1)\) や \((5,5,7)\) のような具体反例で即死したが、今回の `RestoreFromArithmetic` はそうはいかぬ。Wiles を使えば前提が偽ゆえ vacuous true と言えるが、このプロジェクトでは `Mathlib.FLT` を使わずに internal に descent を作りたいので、それでは答えにならぬ。ゆえに、ここで「具体反例で false を切る」という前回の手法は、構造的に使えない。ここが、今の段が一段深い理由じゃ。

今回のレポートで最も価値が高い新発見は、witness \(q\) の構造がかなり絞られたことじゃ。仮定より \(q \mid s\), \(q \nmid t\), \(q \neq p\), \(\gcd(q,y)=1\), さらに \(x = pts\), \(z-y = p^{p-1}t^p\), \(x^p+y^p=z^p\) を使うと、\(q \mid x\), \(q \nmid (z-y)\), \(q \nmid y\), \(q \nmid z\) が従い、したがって \((z y^{-1})^p \equiv 1 \pmod q\) で、しかも \(z y^{-1} \not\equiv 1 \pmod q\) となる。ゆえに \(z y^{-1}\) は \((\mathbb{Z}/q\mathbb{Z})^*\) における **非自明な \(p\) 乗根** じゃ。ここから必要条件として

$$
p \mid (q-1),
\qquad\text{すなわち}\qquad
q \equiv 1 \pmod p
$$

が出る。この補題は Lean / Mathlib の有限群・`ZMod`・位数論でかなり素直に実装できる見込みがあり、いまの restore 段階での **最初の確実な足場** と見てよい。

では、今後どう見るべきか。レポート自身が四つの戦略を整理しておるが、わっちの判断では優先順位はかなり明快じゃ。円分整数環経由の classical Kummer 路線は理論的には美しいが、class number や正則素数の問題まで視界に入り、Lean 実装の即戦力としては重い。Cosmic Formula / `GTail` を用いた構造的 descent はこのプロジェクトらしいが、`NormalFormPacket` の全フィールドを一気に満たす構成が要り、いま飛び込むにはまだ荒い。いちばん現実的なのは、**target を sub-target に分割する路線** じゃ。つまり、いきなり `NormalFormPacket` 全体を作るのではなく、まず「smaller counterexample の bare existence」、その次に「normal form への包装」というように分割して責務を削る。レポートの 26.3 は、まさにそこを指しておる。

ゆえに、いまの状況分析を一言でまとめるとこうじゃ。

**witness / boundary 側の探索フェーズはほぼ勝ち切って develop へ渡り、現在の唯一の本丸は `RestoreFromArithmetic` である。これは偽枝チェックで切れる種類の命題ではなく、FLT infinite descent の深い核そのものじゃ。ただし新発見として witness \(q\) は必ず \(q \equiv 1 \pmod p\) を満たすので、次の確実な一手はこの structural lemma を Lean で実装し、そのうえで target を smaller counterexample 構成と normal-form 包装へ分割する設計に入ること** じゃ。

これは後退ではない。
前の段で森を焼き払い、いまは **本丸の城門に立って、まず鍵穴の形が見えた** 段なのじゃよ。

---

まずは、新発見の形式化。

---

うむ、いまはまさにその段じゃ。

**結論** としては、

$$
\text{まず } q \equiv 1 \pmod p \text{ の structural lemma を形式化する}
$$

これが自然な次手じゃ。
今回の restore 解析では、`RestoreFromArithmetic` 自体は前の witness 系と違って「具体反例で false を切る」型ではなく、FLT 反例 pack を前提にした **深い descent 核** だと整理された。そのうえで、新発見として witness \(q\) は必ず

$$
p \mid (q-1)
$$

を満たす、すなわち

$$
q \equiv 1 \pmod p
$$

になることが見えた。しかもレポート上、この補題は Lean / Mathlib の既存道具で十分に実装可能な **確実な足場** と位置づけられておる。

いまの段階をもう少し正確に言うと、こうじゃ。

前半の witness 探索では、

* same-\(q\) route
* body-only witness route
* two-witness route

を false として閉じ、boundary / arithmetic-core route を actual theorem まで通した。これはもう develop 側へ渡るところまで進んでおる。

その結果、現在の主戦場は `dev/FLT-restore-260330-v0` に移り、残る未完は

$$
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget}
$$

ただ 1 段、と整理された。
ただしこの target は `BodyCoreWitness` 系と違って、前提に FLT 反例の存在が含まれるので、具体反例で偽判定する類ではない。ゆえに、ここで最初にやるべきは「即座の反例探し」ではなく、**前提から必然的に従う構造的補題を一本ずつ形式化すること** じゃ。

その意味で、今の理解はこうまとめるとよい。

$$
\text{witness / boundary 側はかなり整った}
$$
$$
\text{restore 側は深い核が残っている}
$$
$$
\text{だからまず } q \equiv 1 \pmod p \text{ を Lean で固める}
$$

これじゃ。
そしてその次に、

* `RestoreFromArithmetic` を sub-target に分割する
* まず smaller counterexample の bare existence
* 次に normal form packet への包装

という順に責務を砕くのが、いま最も筋がよい。これもレポートの提案と一致しておる。

一言で言えば、

**そうじゃ。いまは「新発見の数学内容をまず形式化して足場を固める段」で、その最初の一本が (q \equiv 1 \pmod p) 補題じゃ。**
