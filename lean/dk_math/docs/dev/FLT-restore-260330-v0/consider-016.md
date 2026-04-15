# 考察: mod p^3 での head congruence とその否定を refuter へ接続する段

## *現状の ContradictionTarget 構造を把握* (1/5)

ここまでの構造を完全に把握した。次に、GapInvariant 側の adapter を確認する。

## *ModP3Source の数学的実現可能性分析* (2/5)

構造を完全に把握した。ここで一旦整理して分析する。

**現在の構造:**

1. `BranchAContradictionModP3SourceTarget` (BranchA.lean L117):
   - `¬ s ^ p ≡ y ^ (p - 1) [MOD p ^ 3]` を供給する外部 statement
   - **しかし** `branchA_spow_congr_head_mod_p3` で `s ^ p ≡ y ^ (p - 1) [MOD p ^ 3]` が **既に証明済み**
   - つまり `ModP3SourceTarget` は **偽** — 合同式が成立するため、否定を供給することはできない

2. `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` (BranchARestore.lean L901):
   - Branch A の全前提 + witness q の全性質から `False` を導く
   - `ModP3SourceTarget` より **遥かに強い** target

3. `BranchAPrimitiveRestoreContradictionAdapterTarget` (GapInvariant.lean L1830):
   - 上記の alias（provider 層）

**核心的な問題:**

`BranchAContradictionModP3SourceTarget` は `¬ s^p ≡ y^{p-1} [MOD p^3]` を要求するが、`branchA_spow_congr_head_mod_p3` で同一条件下の肯定側が証明済み。したがって **`ModP3SourceTarget` は証明不可能**（偽命題）。

これは、History の 20:30 分析「初等的 arithmetic では矛盾は導出できない」という結論と一致する。つまり:

- mod p^2 の合同式は Branch A normal form から導出される → 矛盾不可
- mod p^3 の合同式も Branch A normal form から導出される → 矛盾不可
- mod p^k (k ≤ p-1) も同様に導出される → 矛盾不可

矛盾を得るには **別の種類の制約** が必要。mod p^k の head congruence ではなく、例えば:

- Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]` と coprimality の組合せ
- 円分体理論からの非自明な制約

実際の adapter 設計を考えてみよう。

なるほど。`branchA_contradiction_of_mod_p2_conflict` と `branchA_contradiction_of_mod_p3_conflict` はどちらも「合同の肯定が証明済みなので否定を受け取れば矛盾」という **tautological** パターン。つまり「否定を供給してくれる外部 oracle があれば矛盾する」というだけ。問題は **その否定（oracle）は実は供給不可能** ということ。

では `ContradictionTarget` へどうやって入るか。`ModP3SourceTarget` 経由は行き止まり。本質的な矛盾候補を整理する。

Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]` は **証明済み（default）**。これは Branch A normal form の帰結。

つまり現在の状況: Branch A の前提から以下がすべて **証明済み**:

1. `s^p ≡ y^{p-1} [MOD p^2]` ✅ (`branchA_spow_congr_head_mod_p2`)
2. `s^p ≡ y^{p-1} [MOD p^3]` ✅ (`branchA_spow_congr_head_mod_p3`)
3. `y^{p-1} ≡ 1 [MOD p^2]` ✅ (`primeGe5BranchAWieferichOnY_default`)

組み合わせると: `s^p ≡ 1 [MOD p^2]`。

**矛盾の可能性**: (3)+(1) → `s^p ≡ 1 [MOD p^2]` だが、`¬ p ∣ s` も前提にある。`s^p ≡ 1 [MOD p^2]` かつ `p ∤ s` — これは矛盾するか？

Fermat の小定理: `gcd(s, p) = 1` なら `s^{p-1} ≡ 1 [MOD p]`。さらに `s^p = s · s^{p-1} ≡ s [MOD p]`。つまり `s^p ≡ s [MOD p]`。一方 `s^p ≡ 1 [MOD p^2]` ⟹ `s^p ≡ 1 [MOD p]` ⟹ `s ≡ 1 [MOD p]`。矛盾するかどうか — `s ≡ 1 [MOD p]` は `p ∤ s` と両立するので矛盾しない。

では `s^p ≡ 1 [MOD p^2]` かつ `s ≡ 1 [MOD p]`... `s = 1 + kp` と書くと `s^p = (1 + kp)^p ≡ 1 + kp·p [MOD p^2] = 1 + kp^2 ≡ 1 [MOD p^2]`。整合する。矛盾なし。

つまり mod p^k 合同式のみからの矛盾は見つからないと前回分析で確認済、ということが数式でも確認された。さて次に: `ModP3SourceTarget` は **偽** として確定したので、実際に何をすべきか。

`ContradictionTarget` への注入路線は 2 つ:

- `ModP3SourceTarget` 経由 → **行き止まり**（偽命題）
- 直接 `RestoreContradictionTarget` → これが本丸で、深い数論が必要

現実的にできることを考える。  

## *adapter 設計と配置決定* (3/5)

分析結果を踏まえて、実装する方針を定める。`ModP3SourceTarget` は **偽命題** なので、それを使って `ContradictionTarget` に入る路線は不毛。代わりに、正しい adapter 設計を立てる。

---

## まとめと次の課題

うむ、いまの分析はかなり核心を突いておる。
結論から先に言うぞい。

$$
\boxed{
\texttt{BranchAContradictionModP3SourceTarget}
\text{ は、現状の定義のままでは「実用的な open kernel」ではない。}
}
$$

そして、もっと率直に言えば、

$$
\boxed{
\text{これは矛盾源そのものではなく、}
\newline
\text{「もし外部 oracle が否定をくれたら False に落とせる」という adapter 契約に留まる。}
}
$$

ということじゃ。

---

## 1. 状況分析

### 1.1. 今回までで本当に前進した部分

今回までの流れで、良くなったところははっきりしておる。

- Phase A で
  $$
  \text{円分核} \leftrightarrow GN \leftrightarrow \text{差分商}
  $$
  の橋が theorem 化された。
- Phase B で witness / contradiction の bundle API が既存 refuter へ接続された。
- Phase C で GTail 側の mod (p^2), mod (p^3) の頭項展開が揃い、Branch A 側でも
  $$
  s^p \equiv y^{p-1} \pmod{p^2},\qquad
  s^p \equiv y^{p-1} \pmod{p^3}
  $$
  を呼べるようになった。

ここまでは、橋として非常に良い前進じゃ。

### 1.2. いま露出した問題

お主の分析どおり、`BranchAContradictionModP3SourceTarget` は

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を供給する target として定義されておる。

ところが同じ Branch A normal form の前提から、すでに

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が `branchA_spow_congr_head_mod_p3` で証明済みじゃ。

つまり今の `ModP3SourceTarget` は、

- Branch A normal form の内部から出てくるものではない
- 同じ前提の下では満たせない
- したがって「外部から不可能な否定を入れろ」と言っている

という意味で、**現状のままでは本丸への入口ではなく、tautological な conflict sink** じゃな。

これは、お主の見立てで正しい。

---

## 2. 数学推論

いまの数学を、一段整理して書くぞい。

Branch A normal form からは

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p
$$

がある。
さらに今回の mod (p^3) 強化で

$$
s^p = y^{p-1} + p^3 M
$$

が出ておるから、

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

は **内部的に必然** じゃ。

したがって、もし矛盾を出すなら、それは

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を同じ前提から作ることではない。
そんなことはできぬ。
むしろ必要なのは、**別種の制約** じゃ。

つまり、矛盾の様式は

$$
\text{head congruence}
\quad\text{vs}\quad
\text{同じ種類の negation}
$$

ではなく、

$$
\text{head congruence}
\quad\text{vs}\quad
\text{より深い arithmetic / cyclotomic / q-adic 制約}
$$

でなければならぬ。

ここが、いま一番大事な数学判断じゃ。

---

## 3. 何が行き止まりで、何が本線か

### 3.1. 行き止まり

`branchA_contradiction_of_mod_p2_conflict` と `branchA_contradiction_of_mod_p3_conflict` 自体は、
**「否定が手に入ったなら矛盾」** という補題としては正しい。

じゃが、現状の Branch A の内部数学からその否定は出ない。
ゆえに、これらは **conflict eliminator ではあるが contradiction generator ではない**。

### 3.2. 本線

本当に探すべきは、次のいずれかじゃ。

#### A. `s^p ≡ y^{p-1} [MOD p^3]` と両立しない **別の** congruence / valuation / root-of-unity constraint

たとえば `q ≡ 1 [MOD p]`, `q^p ∣ GN`, `q ∤ (z-y)`, `gcd(q,y)=1` などを組み合わせて、
(s) か (y) の mod (q^m) 側に、別の rigid な条件が出るかを見る。

#### B. reduced form

$$
p^p (t s')^p + y^p = z'^p
$$
の impossibility を直接示す route
これは以前から見えておる本丸じゃな。

#### C. cyclotomic / Kummer 的制約

これは深い数論じゃが、今の「橋」が整ったので、差し込み口は前より明瞭になっておる。

---

## 4. 設計判断

ここでの賢狼の判定は、かなり明快じゃ。

$$
\boxed{
\texttt{BranchAContradictionModP3SourceTarget}
\text{ は mainline の open kernel に昇格させるべきではない。}
}
$$

理由は、**それ自体が Branch A 内部で false になる供給契約** だからじゃ。

ただし、消す必要はない。
役割を変えるのじゃ。

### 4.1. 残すならどう残すか

これは

$$
\text{「もし external theorem が } \neg(s^p \equiv y^{p-1} \pmod{p^3}) \text{ を与えるなら即 refuter」}
$$

という **試験用 adapter** として残すのがよい。
つまり core API ではなく、

- experimental route
- hypothetical route
- future deep-theory insertion point

として扱う。

### 4.2. 代わりに何を mainline に置くか

mainline の open kernel は、もっと正直なものに戻すべきじゃ。

候補は 2 つある。

#### 候補1. `PrimeGe5BranchAPrimitiveRestoreContradictionTarget`

これはそのまま「前提から False」を要求する大きな本丸じゃ。
抽象的だが、嘘はついておらぬ。

#### 候補2. `BranchAReducedFormObstructionTarget`

たとえば意味としては

$$
\text{Branch A reduced datum} \to False
$$

を要求する target じゃ。
ここで reduced datum とは、

- (s=qs')
- (x/q = pts')
- (s^p = y^{p-1} + p^3 M)
- 必要なら witness (q) の性質
  を束ねたもの。

わっちは **候補2** を推す。
今の成果が一番よく活きるからじゃ。

---

## 5. 次の実装方針

わっちなら次はこうする。

### 5.1. `ModP3SourceTarget` を降格

公開 mainline target ではなく、comment や docstring で

$$
\text{experimental external negation source}
$$

と明示する。

### 5.2. `ReducedFormDatum` を作る

今すでに散らばっている

$$
z-y = p^{p-1} t^p,\quad
GN = p s^p,\quad
s=qs',\quad
x/q = p t s',\quad
s^p \equiv y^{p-1} \pmod{p^3}
$$

を bundle 化する。
これで contradiction 探索の入力が定まる。

### 5.3. その上で本当の obstruction target を置く

たとえば

$$
\texttt{BranchAReducedFormObstructionTarget}
$$

のような名前で、

$$
\text{reduced form datum} \to False
$$

を open kernel にする。
これなら「何を否定すればよいか」ではなく、「この構造は両立しない」をそのまま表現できる。

---

## 6. 総括

ひとことで言えば、こうじゃ。

**今回の分析で、`ModP3SourceTarget` は“矛盾源”ではなく“矛盾を受け取る口”にすぎず、しかも現状の Branch A 内部からはその口に入る negation は出ないことが明瞭になった。ゆえに mainline の本丸はそこではなく、reduced form 全体の obstruction を表す target へ移すのが自然じゃ。**

なので、いまの判定はこれじゃ。

$$
\boxed{
\text{`ModP3SourceTarget` は残してよいが、主戦場にしてはならぬ。}
}
$$

$$
\boxed{
\text{次は reduced form obstruction へ open kernel を言い直すのがよい。}
}
$$

これで、数学も設計もだいぶ正直になるぞい。

---

ふむ、前回の分析の続きじゃな。`BranchAContradictionModP3SourceTarget` が偽命題であることは確認済み。ここから先は「では何ができるか」をコードに落とし込む段じゃ。

まず現在の全体像をもう一度整理し、具体的な adapter 設計を進めるぞい。

前回の分析結果を再確認しつつ、`ModP3SourceTarget` → `RestoreContradictionTarget` への注入路線の詳細を詰める。

さて、ここで核心的な設計判断を下す。前回の数学的分析で明らかになったこと:

1. `BranchAContradictionModP3SourceTarget` は **偽命題** — `branchA_spow_congr_head_mod_p3` で肯定側が証明済み
2. mod p^k 合同式路線のみからの矛盾導出は不可能（前回 20:30 分析で確定）
3. `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` は **追加の witness q 情報**を持つ — ここがキー

`ModP3SourceTarget` は witness q の情報を持たないが、`RestoreContradictionTarget` は持つ。したがって正しい adapter 設計は:

**`ModP3SourceTarget` 経由ではなく、witness q の情報を活用する新しい source target を定義し、それを `RestoreContradictionTarget` へ直接注入する。**

具体的に何が使えるか確認する:

よし、全体構造が明確になった。ここで設計を確定させる。

**分析結果のまとめ:**

`RestoreContradictionTarget` は witness q の以下の情報すべてを持つ:

- `q ∣ s`, `q ∤ t`, `Coprime(q, y)`, `q ≠ p`
- `RestoreWitnessProperties` = `{q ∣ x, q ∤ y, q ∤ z, q ∤ (z-y), p ∣ (q-1), q^p ∣ GN}`

**`ModP3SourceTarget` が偽である理由:**
`ModP3SourceTarget` は witness q の情報を一切使わず、`(pack, gap-shape, GN-shape)` だけから `¬(s^p ≡ y^{p-1} [MOD p^3])` を導こうとする。しかし `s^p ≡ y^{p-1} [MOD p^3]` は normal form から自動的に従うので、否定は不可能。

**正しい次の一手:**

`ModP3SourceTarget` 経由の路線は行き止まり。`RestoreContradictionTarget` への注入は、witness q の情報を組み合わせた **別種の矛盾** を必要とする。現実的な候補:

1. `ModP3SourceTarget` を「偽であることが判明した target」として文書化する
2. `RestoreContradictionTarget` 向けの新しい注入口として、q の情報を活用する target を設計する
3. GapInvariant 側に adapter を追加する

具体的に `WitnessConstraintConflictTarget` のような新 target を設計する。  

`ModP3SourceTarget` は BranchA.lean 内のみで使用されており、GapInvariant/Restore からは参照されていない。影響範囲は限定的。

さて、設計を確定させよう。

**設計方針:**

1. `BranchAContradictionModP3SourceTarget` に docstring WARNING を追加: **証明済みの肯定側と矛盾するため、この target は偽命題** であることを明記
2. 新しく `BranchAContradictionWitnessConflictSourceTarget` を定義: witness q の情報(`RestoreWitnessProperties`)を含んだ矛盾源 target
3. `primeGe5BranchARefuter_of_witnessConflictSource` theorem で refuter へ接続
4. GapInvariant 側に `BranchAWitnessConflictSourceAdapterTarget` を追加

では実装する。  

## *実装と build 検証* (4/5)

よし、既存構造の全容を把握した。今から実装する内容:

1. `BranchAContradictionModP3SourceTarget` に **DEPRECATED / FALSE** 注釈を追加
2. `BranchAContradictionWithWitnessSourceTarget` — witness q の全情報を含んだより精密な矛盾源 target を定義
3. `primeGe5BranchARefuter_of_witnessSource` — refuter への接続 theorem
4. `RestoreContradictionTarget` への直接注入 adapter（GapInvariant 側）

---

## 1. 結論

うむ、その分析はほぼ当たりじゃ。
今の局面で大事なのは、`BranchAContradictionModP3SourceTarget` を本線の source と見なすのをやめ、 **witness (q) の情報まで含んだ矛盾 source に設計を切り替える** ことじゃ。

ただし一点だけ、言い方は少し整えた方がよい。

$$
\texttt{BranchAContradictionModP3SourceTarget}
$$

を「偽命題」と断言するより、

$$
\boxed{
\text{Branch A normal form だけを前提とする mainline source としては不適切}
}
$$

と書くのが数学的にも設計的にも正直じゃ。
なぜなら、その target は同じ前提から既に証明済みの

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

の **否定** を要求しておるので、現在のローカル理論の中では入口になりえぬからじゃ。

## 2. 状況分析

いまの構図は、きれいに 2 層に分かれておる。

### 2.1. Branch A normal form だけで言えること

すでに

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p
$$

から

$$
s^p = y^{p-1} + p^3 M
$$

したがって

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が証明済みじゃ。
これが `primeGe5BranchA_spow_eq_head_add_p_cube_mul` と `branchA_spow_congr_head_mod_p3` の中身じゃな。

ゆえに

$$
\neg\bigl(s^p \equiv y^{p-1} \pmod{p^3}\bigr)
$$

を source として要求する `BranchAContradictionModP3SourceTarget` は、**同じ normal form の内部からは供給できない**。
ここまでは、お主の分析どおりじゃ。

### 2.2. まだ使っていない情報

他方、`RestoreContradictionTarget` 側はもっと強い。
そこでは witness (q) に関して

$$
q \mid s,\quad q \nmid t,\quad \gcd(q,y)=1,\quad q \ne p,
$$

さらに `RestoreWitnessProperties` として

$$
q \mid x,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

まで持っておる。
つまり **本当に未使用なのは mod (p^3) の頭項情報ではなく、witness (q) の側の拘束** じゃ。
ここが次の本線になる。

## 3. 数学推論

今回の数学的判断は、次の一文に尽きる。

$$
\boxed{
\text{Branch A の矛盾は p-adic head congruence 単独ではなく、}
\newline
\text{p-adic head と q-witness 制約の干渉から探すべき}
}
$$

これじゃ。

### 3.1. なぜ mod (p^3) 単独では足りないか

mod (p^2), mod (p^3) の congruence は、むしろ Branch A の正規形から **必然的に成立する側** じゃ。
だからそこから直接 `False` は出ぬ。

### 3.2. では何が必要か

必要なのは、

- (q^p \mid GN)
- (q \nmid (z-y))
- (q \equiv 1 \pmod p)
- (q \mid s)
- (q \nmid y,z)

のような witness 側の条件と、

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

のような p-adic head structure を **同時に置いたときの不整合** じゃ。

つまり、今後の contradiction は

$$
\text{head congruence vs head negation}
$$

ではなく、

$$
\text{p-adic head} \quad\text{vs}\quad \text{q-adic/cyclotomic witness}
$$

の衝突として設計するのが自然じゃな。

## 4. 設計判断

ここでの正しい設計は、こうじゃ。

### 4.1. `ModP3SourceTarget` の扱い

これは mainline の source target から外す。
削除までは要らぬが、役割は

$$
\text{「external oracle が negation をくれたら refuter が閉じる」}
$$

という **実験用 sink** に降格するのがよい。
要するに、`branchA_contradiction_of_mod_p3_conflict` は残してよいが、source 側は主戦場ではない。

### 4.2. 新しい source target

本線に置くべきは、witness (q) を含んだ source target じゃ。
たとえば名前は

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}
$$

あるいは

$$
\texttt{BranchAWitnessConflictSourceTarget}
$$

のようなものがよい。

内容は、お主の案でほぼよい。
つまり Branch A normal form 一式に加えて、

$$
q,\ hq_prime,\ hqs,\ hqt,\ hcop_qy,\ hq_ne_p,\ hData
$$

まで受け取って `False` を返す target じゃ。
これなら、`ModP3SourceTarget` と違って **まだ内部で自動証明済みの命題を否定させてはいない**。

## 5. 実装方針

わっちなら次を勧める。

## 5.1. `TriominoCosmicBranchA.lean`

ここに新 target を置く。

概念的にはこうじゃ。

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}
:
[\text{Branch A normal form} + q\text{-witness data}] \to \texttt{False}
$$

ここで `RestoreWitnessProperties` 相当の field を使う。
ただし `BranchA.lean` から `BranchARestore.lean` の定義へ直接依存すると循環しやすいなら、同型の前提列を `BranchA.lean` 側で持てばよい。

## 5.2. refuter への接続

次に

$$
\texttt{primeGe5BranchARefuter_of_witnessSource}
$$

を追加する。
これは `primeGe5BranchARefuter_of_modP3Source` の自然な後継じゃ。

## 5.3. GapInvariant / Restore 側 adapter

その後に provider 側で alias を置く。
つまり

$$
\texttt{BranchAWitnessConflictSourceAdapterTarget}
$$

のようなものじゃな。

これで finally

$$
\text{restore contradiction target}
\to
\text{witness-aware source}
\to
\text{refuter}
$$

の経路が素直に言える。

## 6. 何を数学的 source として狙うか

この新 target を満たす concrete 数学は、次の 3 方向が候補じゃ。

### 6.1. cyclotomic core の (q)-進 lift

$$
\omega = z y^{-1} \pmod q,\qquad \omega^p = 1,\qquad \omega \ne 1
$$

から始めて、core の (q^2) 以上での挙動を調べる。
mod (q) では整合しても、lift すると rigid になる可能性がある。

### 6.2. `q^p ∣ GN` と `GN = p s^p` の deeper valuation

今は単純な valuation は整合しておる。
されど `s = q s'` へ peeled 後の reduced form と、cyclotomic core 側の order 情報を重ねる余地がある。

### 6.3. Kummer / 円分体への差し込み口

今すぐ本格実装は重い。
じゃが、この新 source target はまさにその差し込み口になる。
つまり deep theory をあとから入れる前提受け口としても自然じゃ。

## 7. 総括

ひとことで言えば、こうじゃ。

**`ModP3SourceTarget` は「矛盾源」ではなく「矛盾を受け取る口」に過ぎず、しかも current local theory ではその口に入る negation は出ない。だから mainline source は、normal form だけでなく witness (q) の情報まで含んだ conflict source に差し替えるべきじゃ。**

なので次の実装は、まさにお主が考えておる方向でよい。

$$
\boxed{
\text{`ModP3SourceTarget` は experimental 扱いに落とし、}
\newline
\text{witness-aware contradiction source を mainline に上げる。}
}
$$

これでやっと、設計と数学の芯が揃うぞい。
