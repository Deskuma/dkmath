# Report 015 — conditional split scalar-prime ideal factorization

Date: 2026-10-10 (JST). **Step015 COMPLETE / Outcome B; optional product gate PASSED.** Initial clean HEAD `ecbb96c9dfbb086f17bbc4eac94e6fda2d435836`, branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.

## 結果と数学的範囲

既存 TraceOneInt(-1) の中で、prime q と実際の root t、t≠1-t のもと、２共役 kernel の交わりと積がスカラー主イデアル `(ofInt(-1)(q:ℤ))` に等しいと証明した。２ kernel が distinct maximal であり、和が⊤になることも証明した。これは次数２の既存環における条件付き split-prime ideal 分解である。

任意の integral element z の２座標を復元する iff により ideal equality を証明しており、自然数 α(a,b) の数値例だけに限定されない。root existence は明示仮定のまま。q≠3 から任意の supplied root の separation を導く adapter もチェックした。cyclotomic 側の分解、class-number/UFD、元の平方復元、Fermat下降は追加していない。

変更対象: `DkMath/Lib/NumberTheory/GTailSevenSplitIdeal.lean`、`DkMathTest/NumberTheory/GTailSevenSplitIdeal.lean`、source-inventory-015、report-015、ROADMAP追記。１定義・９公開定理、19 examples。既存の MIT ヘッダ、import後の file print、namespace/indent を維持した。

## Exact public signatures

全シンボルは `DkMath.Lib.NumberTheory`、open `DkMath.NumberTheory.TraceOneQuadratic`。

```lean
theorem eisensteinResidue_root_ne_conjugate {q : ℕ} (hq : Nat.Prime q)
    (hq3 : q ≠ 3) (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) : t ≠ 1 - t

theorem scalar_dvd_traceOne_neg_one_iff (n : ℤ) (z : TraceOneInt (-1)) :
    ofInt (-1) n ∣ z ↔ n ∣ z.fst ∧ n ∣ z.snd

def eisensteinScalarIdeal (q : ℕ) : Ideal (TraceOneInt (-1))

theorem mem_eisensteinScalarIdeal_iff (q : ℕ) (z : TraceOneInt (-1)) :
    z ∈ eisensteinScalarIdeal q ↔ (q : ℤ) ∣ z.fst ∧ (q : ℤ) ∣ z.snd

theorem mem_eisensteinResidueIdeals_iff_coordinates {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t)
    (z : TraceOneInt (-1)) :
    (z ∈ eisensteinResidueIdeal t ht ∧
      z ∈ eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)) ↔
      (q : ℤ) ∣ z.fst ∧ (q : ℤ) ∣ z.snd

theorem eisensteinResidueIdeals_inf_eq_scalar {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t) :
    eisensteinResidueIdeal t ht ⊓
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) =
        eisensteinScalarIdeal q

theorem eisensteinResidueIdeals_ne_of_root_ne_conjugate {q : ℕ}
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t) :
    eisensteinResidueIdeal t ht ≠
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht)

theorem eisensteinResidueIdeals_sup_eq_top {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t) :
    eisensteinResidueIdeal t ht ⊔
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) = ⊤

theorem eisensteinResidueIdeals_mul_eq_scalar {q : ℕ} (hq : Nat.Prime q)
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) (htdiff : t ≠ 1 - t) :
    eisensteinResidueIdeal t ht *
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) =
        eisensteinScalarIdeal q

theorem eisensteinResidueIdeals_mul_eq_scalar_of_ne_three {q : ℕ} (hq : Nat.Prime q)
    (hq3 : q ≠ 3) (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    eisensteinResidueIdeal t ht *
      eisensteinResidueIdeal (1 - t) (eisensteinResidue_conjugate_root t ht) =
        eisensteinScalarIdeal q
```

scalar ideal の本体は `Ideal.span ({ofInt (-1) (q : ℤ)} : Set (TraceOneInt (-1)))`。main product/inf の RHS はこの実際の Ideal。

## 証明経路・仮定監査

root separation は 4(t²-t+1)=(2t-1)²+3 を ring で確認し、t=1-t と ht から3=0 in ZMod q、q∣3、prime q⇒q=3 を導いた。q≠3 の矛盾で separation を得る。q≠7、oddness、Fermat 方程式は仮定していない。

両 membership を Step014 iff で zero evaluation に替え、引き算から snd_cast*(t-(1-t))=0 を得る。prime-field instance と htdiff により snd_cast=0、first equation から fst_cast=0。整数キャスト iff の逆方向 rewrite により両 ℤ 座標の q 整除に接続した。逆方向は両 cast が0なら evaluation が0という直接計算。n:ℤ による scalar ring element divisibility iff は quotient witness を２座標へ投影し、逆に整数商のペアを構成する。ゼロ/負 n も含み、旧自然数 α の iff を代用していない。

principal ideal membership は Mathlib Ideal.mem_span_singleton で scalar divisibility に替えた。交わりは ideal extensionality を用い、すべての integral z についてこの membership と coordinate iff を一致させた。01でここまで build を通してから product gate に進んだ。

distinct kernels の証明は根 t の integer representative n を取り、tau(-1)-ofInt(-1)n という実際の witness を使う。first homではt-t=0、other homでは(1-t)-t≠0。単に tau の像が違うから kernel が違うと推論していない。この distinctness theorem 自体には prime は不要。

Step014 の checked maximality を両 ideal に設置し、Ideal.isCoprime_of_isMaximal と `.sup_eq` で comaximality を得る。Ideal.mul_eq_inf_of_coprime の product=inf と今回の inf=scalar を連結した。よって product gate は追加 axiom なしで成功した。

## API inventory and imports

詳しい型・重複比較は [source-inventory-015.md](source-inventory-015.md)。既存 lattice iff は一般 beta の非零ノルム/非零元と両 conjugate-product coordinate を要求する。Step013 scalar iff は自然数 α 専用であり、今回の signed arbitrary z にはそのまま使えない。既存 residueMap は２座標 QuadraticAlgebra reduction で、今回の integral ideal 分解とは異なる。

直接 import は新 production が Step014 module と Mathlib.RingTheory.Ideal.Operations の２本、test は production の１本。既存 ring/lattice kernels や earlier statement を変更していない。Neutral→FLT import はない。

## 実行した focused Lean checks

cwd=`lean/dk_math`。process-local `LEAN_NUM_THREADS=2`、逐次 incremental。

| Command (cwd: `lean/dk_math`) | Exit | Seconds | Log |
|---|---:|---:|---|
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenSplitIdeal` | 0 | 4.08 | `.lake/build/gtail-step015/01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenSplitIdeal` | 0 | 3.78 | `.lake/build/gtail-step015/02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal` | 0 | 4.6 | `.lake/build/gtail-step015/03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal` | 0 | 4.51 | `.lake/build/gtail-step015/04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal` | 0 | 1.6 | `.lake/build/gtail-step015/05-build.log` |

01 は intersection までの intermediate production を検査し成功。02 は product gate を加えた最終 production を検査し成功。03 は initial tests、04 は Q(5,8)=129=3*43 を明示した最終 tests、05 は Step014 regression。すべて exit0。Lean の失敗・修正試行は今回なかった。full clean/all-test build は実行していない。

## Public axiom output

04の全10新公開シンボルを折返し行も含め抽出・検査した。標準基礎のみ。

| Symbol | Axioms |
|---|---|
| `eisensteinResidue_root_ne_conjugate` | `[propext, Classical.choice, Quot.sound]` |
| `scalar_dvd_traceOne_neg_one_iff` | `[propext]` |
| `eisensteinScalarIdeal` | `[propext, Quot.sound]` |
| `mem_eisensteinScalarIdeal_iff` | `[propext, Quot.sound]` |
| `mem_eisensteinResidueIdeals_iff_coordinates` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueIdeals_inf_eq_scalar` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueIdeals_ne_of_root_ne_conjugate` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueIdeals_sup_eq_top` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueIdeals_mul_eq_scalar` | `[propext, Classical.choice, Quot.sound]` |
| `eisensteinResidueIdeals_mul_eq_scalar_of_ne_three` | `[propext, Classical.choice, Quot.sound]` |

## Kernel-checked examples と観察

- q=43: roots37/7の関係とseparation、P37⊓P7=I43、P37*P7=I43、P37⊔P7=⊤を新 generic endpoints から確認した。root proof に依存する ideal を直接 rewrite せず、membership extensionality を経由した共役 ideal の equality を使用した。
- α(5,8) の norm=129=3*43、α∈P37、α∉P7、α∉I43。normのq整除から両 kernel membership を得られないことが、実際の split ideals の上で確認できた。
- embedded43 は両 kernel と I43 に入り、43を scalar ring element として α に割り込ませることはできない。ideal membership と element divisibility の型を維持して検査した。
- z=⟨-43,86⟩ の両 kernel membership は新 generic reconstruction iff から取得した。I43 membership と scalar43 divisibilityも確認した。負座標を排除すると ideal全体の equality にならないため、generic integer input が必要だった。
- scalar criterion の n=-43 と n=0 を実際に適用した。natural q専用 criterion の不要な正値仮定は持ち込んでいない。
- q=3,t=2=1-t: coincident kernels、z=⟨1,1⟩ の common membership、norm z=3、scalar3∤z、両 kernel の交わり≠I3 を確認した。
- q=5: ∄t:ZMod5,t²-t+1=0 を小さい finite decide で確認した。root引数は定理適用上の実質的な仮定であり、すべてのprimeのsplitを主張していない。
- 任意prime/root の q≠3 adapter による product theorem の汎用署名適用も検査した。

## q=3 の境界に関する指示書の解釈修正

指示書 Phase4 は q=3 の例を intersection/product formula の distinctness 除去に対する反例としてまとめている。しかし今回の z の membership と scalar nondivisibility が直接反証するのは **intersection formula** である。これは comaximal な split の証明経路を ramified境界へそのまま適用できないことを示すが、**standalone product equality の否定は導かない**。P²=(3) の真偽は今回証明・反証していない。未検証の ramified decomposition を事実として記載しない。

この区別は main contract の失敗ではない。sup/productの今回の定理には checked separation を保持しており、OutcomeB/COMPLETEと分類する。

## 次に試す命題・実装提案（未実施）

1. 必要になれば、今回の reconstruction theorem を用いた quotient/CRT adapter を検討できる。kernel交わりの equality と checked comaximality が利用可能になったので、どの quotient 型・map が既存APIと一致するかを source比較してから作る。今回は新CRT hierarchyを導入していない。
2. characteristic3 の principal ideal product を研究する場合、common kernel の generator とその元の積の関係を別途証明する必要がある。split-case product=intersection のルートを使うことはできず、今回の intersection countercheck から productの否定を推論しない。
3. この次数２の ideal 分解を seventh cyclotomic carrier や ramified-root packet に移すには、carrierを結ぶ具体的な ring map と ideal の image/comap 契約が必要。scalar GTail q-support と新P_tを同一視する API、unit-power class、次の正の原始 Fermat packet は未実装。

局所的な degree-two split identity は検査済みになったが、独立の新 FLT7 arithmetic obstruction / descent / closure は得ていない。Step015で停止。

## Final source/graph audit

新規２ Lean source に sorry/admit/new axiom/unsafe/False.elim/exfalso/native_decide/FLT impossibility endpoint の禁止構文なし。末尾改行と行末空白チェック成功。最終 production/test/Step014 regression ログに warning/error なし。新規文書と ROADMAP 追記の空白チェックも成功し、旧 ROADMAP 本文を保存した。

コメント除去後の import-header closure は production1365 names/13 local modules、test1366/14。local union14 vertices の DFS に cycle なし、neutral closureに FLT moduleなし。結果 `.lake/build/gtail-step015/imports.json`。external terminals を含む source counts であり、build jobs や全依存の hole/axiom audit ではない。

HEAD と byte比較した既存56ファイル（存在する root/test driver、Lake/toolchain/facade、ring/residue/lattice/coordinate owners、GTail neutral/FLT owners と対応 tests、歴史的 ledger と直前 reports/review）は変更なし。tracked diff は `git diff --check`、新規ファイルの空白は上記の別検査で確認した。
