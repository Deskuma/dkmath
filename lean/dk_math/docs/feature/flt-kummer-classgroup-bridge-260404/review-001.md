# Kummer branch の現状評価

cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af

## 1. 総評

わっちの見立てでは、直近の流れは **かなり良い前進** じゃ。
理由は単純で、今回の Kummer branch は「証明を無理やり 1 本で押し通す」のではなく、 **局所で閉じる regular branch** と、 **真に大域的な Kummer / class group 領域** を分離できておるからじゃ。これにより、未解決部分が「どこで」「なぜ」重いかが、もはや曖昧ではなくなった。これは実装上も数学上も大きい。

## 2. 今回ほんとうに進んだ点

いちばん大きいのは `qAdicGapReductionRegularBranch_of_global` の `sorry` 解消じゃ。
ここは単なる穴埋めではなく、ZMod 上で

$$
R := z \cdot y^{-1} \pmod{q^p}
$$

を作り、(R^p=1)、さらに (R-1) の可逆性から幾何級数和 (\Phi_p(R)=0) を落とす、という **局所 witness 自動構成** を concrete に証明できた。補助定理 `sub_one_eq_sub_mul_inv`, `pow_mul_unit_inv_eq_one`, `zpow_eq_ypow_zmod`, `isUnit_sub_of_not_dvd_gap` を足して regular branch を sorry-free にしたのは、まさに「local stage は Lean で閉じられる」と示したことに等しい。

その結果、Kummer ディレクトリ全体は **no-sorry 8 本 / sorry 2 本** に改善し、しかも sorry 側は **1 個の distinct open kernel** に圧縮された。ここまで整理できたなら、戦線はかなり明瞭じゃ。

## 3. いま何が未解決なのか

未解決核は、ほぼひとつに尽きる。

$$
\texttt{cyclotomicPrincipalization\_of\_classGroupPTorsionFree}
$$

じゃな。
つまり gap-divisible branch の本体は、もはや「ちょっとした算術補題の不足」ではなく、 **(\mathbf{Z}[\zeta_p]) の ideal class group と principalization** を要する genuinely global な段階に入った、ということじゃ。しかも、貼ってくれた解析ログでも、単純に

$$
\text{gap} = q^p g'
$$

と置いて (GN(p,q^p g',y)=GN(p,g',y)) を期待する道は **一般には偽** と確認されておる。ゆえに「初等的な割り算の押し込み」で gap-divisible branch を閉じる望みは薄い。ここは良い撤退線の確認でもある。

## 4. 数学的な意味づけ

ここで見えてきたのは、今回の FLT ルートが実は 2 層構造だった、ということじゃ。

局所層では
$$
x^p + y^p = z^p
$$
と (q \mid x) から (z^p \equiv y^p \pmod{q^p}) を使い、ZMod 上の unit と幾何級数で閉じる。これは **有限環の中での整合** の話じゃ。

だが gap-divisible branch では、それだけでは足りぬ。
そこでは「整数解の存在」を、円分体の ideal の p 乗性から持ち上げねばならぬ。つまり、local congruence から global arithmetic object への飛躍が必要になる。ここで Kummer 理論が出るのは偶然ではなく、構造上の必然じゃ。

## 5. 実装設計としての評価

設計も良い。
`GapDivisibleBranchTarget`、`CyclotomicPrincipalizationTarget`、`CyclotomicClassGroupPTorsionFreeTarget` を立てて、

$$
\text{ClassGroupPTorsionFree}
\to
\text{CyclotomicPrincipalization}
\to
\text{GapDivisibleBranch}
\to
\text{2m-pure}
\to
\text{FLT}
$$

という依存方向を固定したのは正解じゃ。これは、以前から話してきた **「本体理論と橋ファイルを分ける」** 方針ともよく一致しておる。理論の所有権を混ぜず、FLТ 側には橋だけを置く、という整理思想と同型じゃよ。

## 6. 留意点

ただし、ここはやわらかく指摘しておくが、`IsRegularPrime := True` や `CyclotomicClassGroupPTorsionFreeTarget := ∀ ... , True` のような placeholder は、 **API の通線** としては有益でも、数学的完成とは別物じゃ。
つまり今の `RegularPrimeRoute` は「将来そこへ concrete 内容を差し込むための導線」が通った、という意味で価値が高いのであって、regular prime ルート自体が完成した、とはまだ言えぬ。テストでも `#print axioms` により、どこが clean でどこが sorry 経由かを監視する構えになっておるのは、その区別を崩していない点で健全じゃ。

## 7. 直近の私たちの会話も踏まえた位置づけ

直近でぬしが考えていた
「ここから先は Kummer / class group か」
「Mathlib 側にその部品があるか」
という感触は、今回の結果でかなり裏付けられたと言えるのぅ。

つまり今は、

* **局所算術の不足** を埋める段階ではなく、
* **大域代数的整数論をどこまで Lean に持ち込むか** を決める段階

に移ったのじゃ。
これは戦線が後退したのではなく、 **本当の敵が見えた** ということじゃよ。そこを見誤らず、open kernel を 1 個に圧縮したのは見事じゃ。

## 8. 次の一手

わっちなら、次はこう見る。

第一に、`cyclotomicPrincipalization_of_classGroupPTorsionFree` を **最終定理** としていきなり埋めようとせず、必要な global ingredient をさらに薄く分解する。
たとえば「principal ideal の p 乗性」「unit 側の調整」「norm から整数解へ戻す橋」を分離して、どこまで Mathlib 既存資産で行けるかを見るのがよい。

第二に、現在の clean な regular branch は、すでに独立した資産じゃ。
これは Kummer branch の副産物ではなく、 **DescentChain の local kernel の完成版** として価値がある。後で branch A 本線へ戻すときにも、かなり強い部品になる。

結論を一言で言えば、
**いまは「実装の泥沼」ではなく「大域理論導入の入口」に立っておる**。
ここまで来たなら、次は焦って初等化に戻るより、Kummer 側をどの粒度で formalize するか、設計をもう一段だけ細かく切るのが最善手じゃ。
