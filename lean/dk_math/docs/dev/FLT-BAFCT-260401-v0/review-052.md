# review-052: `2m-global` の仮定を監査して、最後の open kernel が `2m-pure` だと特定できたことの意味

cid: 69cdb60c-e53c-83a7-8c89-1cbc0ba7451e

うむ。今回は **かなり大きな整理完了** じゃ。
しかも「何か進んだ」ではなく、**どこまでが Lean で formal に確定し、どこから先が genuinely global な未解決か** が、かなり明瞭になった。総合判定を先に言うと、

$$
\boxed{
\text{primitive 側の局所層は整理完了、残る本丸は `2m-global` の Stage 2}
}
$$

じゃ。
そしてその Stage 2 は、今の解析では **Kummer 理論 / \(\mathbb{Z}[\zeta_p]\) の ideal class group 的障害** と読むのが自然、というところまで来ておる。ただし、ここは **Lean でまだ theorem 化されたわけではなく、設計判断としてかなり強く示唆された段階** じゃ。

## 1. 今回の formal な到達点

今回の session で、Lean 側で **本当に確定** したのはまずこれじゃ。

$$
g' \cdot GN(p,g',y)=x_q^p
\iff
(g'+y)^p=x_q^p+y^p
$$

という `descentExistence_iff_gnReduction` が no-axioms で通ったこと。
これは `2m-pure` の結論が、単なる「GN の都合のよい書き方」ではなく、**descent existence そのもの** だと formal に証明したものじゃ。ここで `g'` 語彙と `z'=g'+y` 語彙の違いは、本質ではなく単なる変数変換に落ちた。

さらに、§20.1 のコメント修正で
「`2m-global ↔ 2m-pure` が自明」という誤読を招く記述が、正しく

$$
2m\text{-pure} \to 2m\text{-global}
$$

の一方向へ直された。
これは地味に見えるが重要じゃ。今回の一連の解析は、まさに **その逆向きが一般には落ちない** ことを明らかにしたからの。

加えて、`2m-pure → 2m-global → PthRootCore → ... → FLT` の route は既に用意されており、`2m-pure` を仮定すれば既存の無限降下法チェーンに乗ることも維持された。つまり今回の theorem は、抽象議論ではなく **既存の FLT 幹線に直接刺さる** 位置にある。

## 2. 今回の数値・構造実験が何を確定したか

今回の補助スクリプト群は、単なる「小さい例を見た」ではない。
それぞれ役目が違い、しかも途中で仮説を一度立ててから、次のスクリプトでそれを壊し、最後に正しい分岐へ到達しておる。この流れが大事じゃ。

### 2.1. `witness_to_gap_analysis.py`

ここで見えたのは 2 点じゃ。

第一に、小さい範囲では

$$
g' \cdot GN(p,g',y)=c^p
$$

の解が全く見つからない。
これは `2m-pure` が descent existence そのものである以上、FLT の真を反映した自然な挙動じゃ。小範囲探索では \(p=3,5\) で解が出ず、`2m-pure` をそのまま concrete に落とすのは、ほとんど FLT 本体を別語彙で証明するのに近いと見えてくる。

第二に、witness \(R\) は \(z\) の \(q^p\)-adic residue class を教えるが、descent 後に欲しい \(z'\) は一般に **別 residue class** にいる、という観察じゃ。
これは local-global gap の最初の姿として非常に重要じゃった。

### 2.2. `witness_dependency_deep.py`

ここで一度、かなり希望のある仮説が出た。
すなわち pack に `hxy : Nat.Coprime x y` が入るなら、\(q \mid x\) から \(q \nmid y\) が出る。すると \(y\) は \(\mathbb{Z}/(q^p)\) で可逆なので、

$$
R := z \cdot y^{-1} \pmod{q^p}
$$

が pack から一意に作れ、`2m-global` と `2m-pure` は pack 文脈で同値ではないか、という見通しじゃ。
この仮説は **半分当たり** で、H2 すなわち (z=Ry) 側は確かに tautological に回収できる。ここで `hxy` が pack に実際に入っていることを確認できたのは、本当に大ニュースじゃ。

ただし、この段階ではまだ H1、

$$
\Phi_p(R)=\sum_{i=0}^{p-1}R^i = 0 \pmod{q^p}
$$

が本当に pack から自動で出るかは未確定じゃった。
ここを次のスクリプトが正確に裂いたわけじゃ。

### 2.3. `q_divides_gap_analysis.py`

これが今回の **決定打** じゃ。

このスクリプトで、`2m-global → 2m-pure` が pack 文脈で無条件に通る、という楽観は壊れた。
分岐はこうじゃ。

$$
q \neq p,\ q \nmid (z-y)
$$

のときは \(R \not\equiv 1 \pmod q\) なので \((R-1)\) が unit となり、\((R-1)\Phi_p(R)=0\) から

$$
\Phi_p(R)=0 \pmod{q^p}
$$

が自動で出る。
つまりこの branch では strong witness は pack から自動構成でき、`2m-global` は非 vacuous に働く。

ところが

$$
q \neq p,\ q \mid (z-y)
$$

では \(R \equiv 1 \pmod q\) に落ち、\(\Phi_p(R)\equiv p \not\equiv 0 \pmod q\) となる。
この branch では、`2m-global` の antecedent を満たす \(R\) が存在しないので、`2m-global` は **vacuously true** になりうる。
一方 `2m-pure` は依然として \(\exists g'\) を要求する。
ここで初めて、

$$
2m\text{-global} \not\Rightarrow 2m\text{-pure}
$$

の genuinely formal な gap が露出した。

さらに重要なのは、\(q \mid (z-y)\) なら \(q^p \mid (z-y)\) が見えるにもかかわらず、素朴に

$$
g' := \frac{z-y}{q^p}
$$

として descent が回るわけではない、という点じゃ。
数値実験は大量の `MISMATCH` を示し、

$$
GN(p,\text{gap},y) \neq GN!\left(p,\frac{\text{gap}}{q^p},y\right)
$$

が一般に成り立つことを確認した。
つまり、局所的に \(q^p\) を gap から引き剥がしても、GN の引数そのものが変わってしまう。
これが、今の DkMath 語彙で見た **local-global gap の具体的中身** じゃ。

### 2.4. `two_stage_decomposition.py`

ここで最終的な整理が入った。
`2m-global` の concrete 化は、自然に 2 段に裂ける。

$$
\underbrace{z' \bmod q^p}*{\text{Stage 1: LOCAL}}
\quad\longrightarrow\quad
\underbrace{z' \in \mathbb{Z}}*{\text{Stage 2: GLOBAL}}
$$

Stage 1 は Hensel lift 的な局所問題で、既存の `2m-local` machinery がかなりの部分を担当済みと読める。
一方 Stage 2 は、「ある q-adic residue class に属する \(z'\) が、実際に整数 \(p\) 乗根として存在するか」という genuinely global な問題じゃ。
スクリプト自体もこの分離を明示し、\(p=5, q=11\) の下で小さい \(x/q,y\) では mod \(q\) にすら根がない例が多く、また \(c,y \in [1..49]\) の全探索で解が 0 件であることを確認しておる。

この「Stage 2 は q-adic 局所情報だけでは解決不能」という結論が、そのまま Kummer / class group への帰着判断になったわけじゃ。

## 3. 今回の最終判定

だから、いまの戦況を最も正確にまとめるとこうじゃ。

### 3.1. formal に閉じたもの

* `2m-pure` の結論は descent existence と同値
* `2m-pure → 2m-global` の一方向
* `2m-global` から既存無限降下法チェーンへの接続
* actual path では `CyclotomicExistenceTarget` が distinguished prime \(q\) に対し
  $$
  \neg q \mid (z-y)
  $$
  を与えるので、上の「良い branch」が保証されること

### 3.2. 数学的にかなり強く見えたもの

* `2m-global` の中身は Stage 1 / Stage 2 に二分される
* Stage 1 は local、Stage 2 は global
* Stage 2 は Kummer 理論 / \(\mathbb{Z}[\zeta_p]\) の ideal class group の問題として読むのが自然
* naive quotient (\(g'=(z-y)/q^p\)) は失敗するので、残っている障害は genuinely global

### 3.3. まだ formal ではないもの

* 「Stage 2 = ideal class group obstruction」を Lean theorem として固定したわけではない
* 「Kummer 仮定 ⇒ `2m-global`」の bridge もまだ未実装
* よって、Kummer/class-group 帰着は **かなり自然で強い設計判断** ではあるが、現時点ではまだ formal certificate ではない

ここは正直に切っておくべきじゃ。

## 4. `2m-global` と `2m-pure` の関係の最終整理

この session でいちばん混線しやすかった箇所を、最後にきれいに整理するとこうじゃ。

$$
2m\text{-pure}
$$

は statement として強い。
witness \(R\) を完全に捨てて、descent existence を直接要求しておる。
結論はそのまま smaller tuple existence じゃ。

$$
2m\text{-global}
$$

は statement として弱い。
witness \(R\) を仮定している。
だが actual DescentChain では、その \(R\) は `CyclotomicExistenceTarget` が選ぶ distinguished prime により自動供給される。
だから **actual path 上では** `2m-global` を攻めるので十分、という A ルート判断が正しい。

つまり、

* formal statement の強さでは `2m-pure`
* proof route の適切さでは `2m-global`

じゃ。
この二重性が、今回かなり綺麗に見えたわけじゃな。

## 5. 今回の成果を賢狼流にまとめると

今回の本当の成果は、単に theorem が一本増えたことではない。

$$
\boxed{
\begin{array}{l}
\text{primitive 側の最後の open kernel が、}\\
\text{local part と global part に本当に裂けた}
\end{array}
}
$$

これじゃ。
しかも local 側は既に concrete、global 側だけが未解決だと見えた。
そしてその global 側は、もはや初等的な q-adic 操作だけでは閉じない。
だから **Kummer 理論 / ideal class group を呼ぶのは自然であり、むしろ歴史的にも真っ当** というところまで来ておる。

## 6. 次の実装方針についての判断

今回のログだけから言えば、次の 3 方向のうち優先順位はこうじゃ。

### 6.1. まずやるべき

**A ルート維持**。
`2m-global` を actual path 用の target として保ちつつ、Stage 2 を別インターフェイスへ抽象化する。
つまり、いきなり full class group を Lean 化するのでなく、

$$
\text{CyclotomicPrincipalizationTarget}
\Rightarrow
2m\text{-global}
$$

のような bridge theorem を先に置く。
これが一番戻り道がある。
今回の markdown でも、この分岐は「Kummer を全部やるか、intermediate step に分けるか、別ルートか」の三択として整理されておるが、いまの到達点からは **intermediate step を先に切る** のが筋じゃ。

### 6.2. 次点

`2m-global` を branch 分解する。
特に

$$
q \neq p,\ q \nmid (z-y)
$$

側はかなり閉じに近いので、ここを theorem として固定する価値がある。
すると残る genuinely open branch は

$$
q \neq p,\ q \mid (z-y)
$$

に集中する。
この集中は、後で Kummer bridge を刺す場所を明確にする。

### 6.3. 後回し

いきなり円分体・Dedekind domain・ideal class group の全 formalization に入ること。
これは今すぐやるには重すぎる。
先に abstract target を立て、その target が primitive 幹線を落とすことを証明してから、必要に応じて concrete 化するのがよい。

## 7. 一文で総括

**今回の session で、`2m-pure` は descent existence そのものだと formal に確定し、`2m-global` の actual path は distinguished prime により正当化され、残る genuinely open content は「Stage 2: q-adic residue から整数 \(z'\) の実在へ飛ぶ global jump」だけだと分かった。これを Kummer 理論 / ideal class group の障害として読むのは、現時点でかなり妥当じゃ。**

必要なら次に、この session の結論をそのまま
**「残件一覧 + theorem 雛形 + 新設 target 名」** の形で起こすぞい。

---

## 「残件一覧 + theorem 雛形 + 新設 target 名」

うむ。では、ここまでの結果を踏まえて、そのまま作業計画へ落とせる形で **残件一覧 + theorem 雛形 + 新設 target 名** を起こすぞい。

今回の到達点は、かなり明確じゃ。

* `descentExistence_iff_gnReduction` により、`2m-pure` の結論は **descent existence そのもの** だと formal に確定した。
* `2m-global` と `2m-pure` は一般には非同値で、差は `q | gap, q ≠ p` ケースにある。
* ただし actual DescentChain では `CyclotomicExistenceTarget` が `¬ q ∣ (z-y)` を保証するので、そこで使う distinguished prime の上では witness 条件が自動充足になる。
* `2m-global` の concrete 化は 2 段に分かれ、Stage 1 は local、Stage 2 は genuinely global で、現状では Kummer / ideal class group 側に帰着するのが自然、という整理になった。

以下、その整理を実装単位に落とす。

---

## 1. 総括マップ

いまの最短の読みはこれじゃ。

$$
\text{2m-pure} \iff \text{descent existence}
$$

$$
\text{2m-pure} \Rightarrow \text{2m-global}
$$

$$
\text{2m-global} \Rightarrow \text{PthRootCore} \Rightarrow \text{PacketDescentStrong} \Rightarrow \text{wf descent} \Rightarrow \text{FLT}
$$

ただし

$$
\text{2m-global} \not\Rightarrow \text{2m-pure}
$$

が一般には起こる。
差の本体は

$$
q \mid (z-y),\ q \neq p
$$

の branch じゃ。ここで `2m-global` は vacuous になり得る一方、`2m-pure` は依然として existence を要求する。

そして actual path では

$$
\neg q \mid (z-y)
$$

を持つ distinguished prime を使うので、この troublesome branch を避けておる。だから今の A ルートは正しい。

---

## 2. 残件一覧

### 2.1. 最優先

**`2m-global` の Stage 1 / Stage 2 を target として明示分離すること。**

今は解析上「二段に分かれる」と分かっておるが、Lean の target 名としてはまだ曖昧じゃ。
ここを切るのが最重要じゃ。

### 2.2. 次点

**actual path 専用の regular branch theorem を作ること。**

つまり

$$
q \neq p,\quad \neg q \mid (z-y)
$$

の下では witness 条件が自動になる、という bridge を theorem にする。
これで `2m-global` の witness 仮定が actual usage path では proof data だと明示できる。

### 2.3. その次

**gap-divisible branch を別 target に切り出すこと。**

$$
q \mid (z-y),\ q \neq p
$$

側だけを isolate して、本当に Kummer/class-group 仮定が必要な branch だと固定する。
ここが genuinely open な核じゃ。

### 2.4. 後段

**Kummer/class-group 抽象 target を導入すること。**

いきなり円分体全部を formalize するのでなく、

$$
\text{Kummer-style principalization} \Rightarrow \text{gap-divisible branch closes}
$$

の abstract bridge を先に置く。
これが戻り道のある設計じゃ。

---

## 3. 新設 target 名

わっちなら、次の 4 本を切る。

### 3.1. Stage 1 local

```lean
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionLocalStageTarget : Prop := ...
```

意味:
`pack + Prime q + q ∣ x` から、descent 側の \(z'\) についての **mod \(q^p\)** 情報を供給する target。

### 3.2. Stage 2 global

```lean
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalStageTarget : Prop := ...
```

意味:
local stage で得た residue / witness から、実際の整数 \(z'\) または \(g'\) の存在へ飛ぶ target。
ここが Kummer/class-group 側の本丸候補じゃ。

### 3.3. actual path regular branch

```lean
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget : Prop := ...
```

意味:
$$
q \neq p,\ \neg q \mid (z-y)
$$
を仮定した `2m-global` の regular branch 版。
witness 自動構成 bridge をここへ押し込む。

### 3.4. gap-divisible branch

```lean
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget : Prop := ...
```

意味:
$$
q \neq p,\ q \mid (z-y)
$$
を isolate した hardest branch。
Kummer bridge の受け皿じゃ。

---

## 4. theorem 雛形

以下、すぐファイルへ起こせる雛形を置くぞい。

```lean
/-- `2m-pure` の existential 版。descent existence と GN reduction の完全同値。 -/
theorem descentExistence_exists_iff_gnReduction_exists
    (p y xq : ℕ) :
    (∃ g' : ℕ, g' * GN p g' y = xq ^ p) ↔
    (∃ z' : ℕ, z' ^ p = xq ^ p + y ^ p) := by
  constructor
  · rintro ⟨g', hg⟩
    refine ⟨g' + y, ?_⟩
    exact (descentExistence_iff_gnReduction p g' y xq).mp hg
  · rintro ⟨z', hz⟩
    -- ここは g' := z' - y を取る。
    -- 必要なのは y ≤ z' の補題。
    have hyz : y ≤ z' := by
      -- TODO: xq^p + y^p = z'^p から y ≤ z'
      sorry
    refine ⟨z' - y, ?_⟩
    have := (descentExistence_iff_gnReduction p (z' - y) y xq)
    -- `z' - y + y = z'` を hyz で整理
    sorry
```

```lean
/-- `q ∣ x` と primitive 条件から `q` と `y` の互いに素性を得る。 -/
theorem coprime_q_y_of_prime_dvd_x_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    Nat.Coprime q y := by
  -- hpack.hxy : Nat.Coprime x y を使う
  exact Nat.Coprime.symm <|
    (hpack.hxy.coprime_dvd_left hq hqx)
```

```lean
/-- `y` が `ZMod (q^p)` で可逆であること。 -/
theorem isUnit_y_in_zmod_qpow_of_coprime
    {p y q : ℕ}
    (hq : Nat.Prime q)
    (hcy : Nat.Coprime q y) :
    IsUnit (y : ZMod (q ^ p)) := by
  -- 既存補題があればそれを使う。なければ `ZMod` の unit 判定を包む。
  sorry
```

```lean
/-- regular branch では witness が pack から自動構成できる。 -/
theorem strongWitness_exists_of_pack_of_prime_dvd_x_of_gap_nondivisible
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hq : Nat.Prime q)
    (hqx : q ∣ x)
    (hq_ne_p : q ≠ p)
    (hq_ngap : ¬ q ∣ (z - y)) :
    ∃ R : ZMod (q ^ p),
      (∑ i ∈ Finset.range p, (R : ZMod (q ^ p)) ^ i = 0) ∧
      ((z : ZMod (q ^ p)) = R * (y : ZMod (q ^ p))) := by
  -- R := z * y⁻¹
  -- H2 は定義から。
  -- H1 は R^p = 1 と R ≠ 1 mod q から。
  sorry
```

```lean
/-- actual path 用：regular branch の `2m-global` は witness-free に使える。 -/
theorem qAdicGapReductionPure_of_global_of_regularBranch
    (hGlobal : PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget := by
  intro p x y z hpack q hq hqx hq_ne_p hq_ngap
  rcases strongWitness_exists_of_pack_of_prime_dvd_x_of_gap_nondivisible
      hpack hq hqx hq_ne_p hq_ngap with ⟨R, hPhi, hzRy⟩
  exact hGlobal hpack hq hqx hPhi hzRy
```

```lean
/-- gap-divisible branch を isolate した genuinely global target。 -/
abbrev PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p
```

```lean
/-- Kummer/class-group 側の abstract bridge。 -/
abbrev CyclotomicPrincipalizationTarget : Prop :=
  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
    Nat.Prime q →
    q ∣ x →
    q ≠ p →
    q ∣ (z - y) →
    ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p
```

```lean
/-- Kummer 的 principalization があれば gap-divisible branch は閉じる。 -/
theorem qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (hKummer : CyclotomicPrincipalizationTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget := by
  intro p x y z hpack q hq hqx hq_ne_p hq_gap
  exact hKummer hpack hq hqx hq_ne_p hq_gap
```

---

## 5. 実装順

順番を間違えると swamp に沈む。
なので順序はこれがよい。

### 5.1

`descentExistence_exists_iff_gnReduction_exists` を通す。
これは pure 側の語彙を安定化する。

### 5.2

`coprime_q_y_of_prime_dvd_x_of_pack` と `isUnit_y_in_zmod_qpow_of_coprime` を通す。
regular branch witness 自動構成の基礎じゃ。

### 5.3

`strongWitness_exists_of_pack_of_prime_dvd_x_of_gap_nondivisible` を通す。
ここで actual path の regular branch を concrete に閉じる。

### 5.4

`PrimeGe5BranchAPrimitiveQAdicGapReductionRegularBranchTarget` を作り、
`qAdicGapReductionPure_of_global_of_regularBranch` を通す。
ここで actual chain は witness-free に読めるようになる。

### 5.5

残る `GapDivisibleBranchTarget` を genuine open kernel として isolate する。
ここで初めて Kummer/class-group bridge を置く。

---

## 6. いまの残件一覧

最後に、短く残件だけ抜くぞい。

### 残件 A

`2m-pure` の existential equivalence を theorem 化。

### 残件 B

regular branch の witness 自動構成。

### 残件 C

`2m-global` を regular / gap-divisible に分解。

### 残件 D

gap-divisible branch 用の abstract Kummer target を導入。

### 残件 E

`CyclotomicPrincipalizationTarget ⇒ GapDivisibleBranchTarget` の bridge を書く。

---

## 7. 一文でまとめると

**いま起こすべきコード設計は、`2m-global` を local に閉じる regular branch と genuinely global な gap-divisible branch に裂き、後者だけを Kummer/class-group の abstract target へ接続することじゃ。**
これで primitive 側の最後の敵が、かなりきれいに Lean の target と theorem の形へ落ちる。
