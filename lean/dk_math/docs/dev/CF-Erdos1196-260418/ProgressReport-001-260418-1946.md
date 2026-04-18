# Progress Report 001: 2024-04-26 19:46

## 1. 現況総括

今回のスナップショット更新とサマリー再取得を踏まえた結論を先に述べる。

**これは新しい進展である。**  
ただし性質としては、ABC予想本体の大定理が一気に前進したというより、**ABC 側で再利用できる bridge 層が実装として定着し、公開導線まで整った** という進展である。

設計・実装計画で狙っていた

\[
\text{CosmicFormula}
\;\to\;
\text{Mass API}
\;\to\;
\text{ValuationFlow}
\;\to\;
\text{ABC Bridge}
\]

という spine は、最小核としてかなり綺麗に閉じたと見てよい。

一方で、ABC 本体の重い未完核、特に既存の解析的・確率的評価や Janson 系の unfinished 部分そのものを今回直接閉じたわけではない。したがって、現況は

- **bridge 層は新段階に入った**
- **本丸の ABC 本体はまだこれから**

という二層評価が正確である。

---

## 2. 今回の実装到達点

### 2.1. `CosmicFormula/Mass` 側

今回の実装で `CosmicFormula/Mass` 側には、

- `Core.lean`
- `Decompose.lean`
- `Branch.lean`

が入り、`Big / Body / Gap / Core / Beam` を **質量保存 API** として再公開する層が成立した。

これは実装計画における

- Phase A. Cosmic Mass API の固定
- Phase B. Branch / SubConservative API

の中核部分そのものである。

ここで重要なのは、単なる代数恒等式ではなく、

\[
\mu(\mathrm{Big}) = \mu(\mathrm{Body}) + \mu(\mathrm{Gap})
\]

\[
\mu(\mathrm{Body}) = \mu(\mathrm{Core}) + \mu(\mathrm{Beam})
\]

という **保存則の言葉** に読み替えるための API が実体化したことじゃ。

ただし、もともとの大きい設計図にあった `Tromino2D` と `Harmonic` まではまだ初回実装に含めておらず、ここは保留のままである。

### 2.2. `NumberTheory/ValuationFlow` 側

つぎに `NumberTheory/ValuationFlow` 側には、

- `Basic.lean`
- `Primitive.lean`

が入り、`padicValNat`・primitive prime・`GN` を flow 的な命名で読み直す層が整った。

この段階では、

- exact な Markov kernel
- \(Λ(q)/\log n\) 型の実数確率
- hitting の完成形

まではまだ扱わず、まず

\[
\text{primitive condition}
\;\to\;
\text{Beam / GN 側への流れ}
\;\to\;
\text{valuation 上界}
\]

という構造的 spine を通す方針になっている。

ここは設計意図どおりであり、初手としてはかなり良い。

### 2.3. `ABC` 側

ABC 側には、

- `MassBridge.lean`
- `ValuationFlowBridge.lean`
- `Bridge.lean`
- `BridgeExamples.lean`

が入り、さらに `ABC/Main.lean` から `Bridge` が import される形になった。

つまり今回の成果は、単なる内部実装ではなく、**ABC の公開面から見える bridge API** として定着し始めた、という点にある。

---

## 3. 設計・実装計画との照合

## 3.1. Phase A. Cosmic Mass API

ここは **ほぼ完了** と見てよい。

既存の

- `CoreBeamGap`
- `ResidualNat`
- `ResidualInt`

にある分解補題を wrapper / alias として再公開し、

\[
\text{Big} = \text{Body} + \text{Gap}
\]

\[
\text{Body} = \text{Core} + \text{Beam}
\]

を mass API 名で参照できる状態になった。

計画上の到達目標であった

- `mass_big_eq_mass_body_add_mass_gap`
- `mass_body_eq_mass_core_add_mass_beam`
- `mass_big_eq_mass_core_add_mass_beam_add_mass_gap`
- `mass_residual_eq_mass_gap`

という型の spine は、概ね実現できていると判断してよい。

## 3.2. Phase B. Branch / SubConservative API

ここも **最小核として完了** である。

`Branching`, `outgoingMass`, `SubConservative`, `outgoingMass_le_mass`, `branch_sum_le_parent` が入り、

\[
\sum_{b \in \mathrm{children}(X)} \mu(b) \le \mu(X)
\]

という「子の総質量は親を超えない」骨格は立った。

ただし、`Tromino2D` を concrete な教材として接続する段階はまだ未着手であり、ここは次の余地が残っている。

## 3.3. Phase C. Primitive / GN / valuation の接続

ここも **最小 spine は完了**。

primitive witness から、

- `Nat.Prime q`
- `q \mid a^d - b^d`
- boundary 側は 0
- diff load は beam load に移る
- squarefree beam なら局所 load は高々 1

という線が通った。

しかもそこから先に、

- 二本 witness 版
- `Finset` family 版
- `PrimitiveWitnessFamily` package 版

へと持ち上がっており、これは当初計画よりも一段整理が進んだ部分である。

## 3.4. Phase D. ABC bridge

ここは **想定以上に進んだ** と見てよい。

単に `rad` や `padicValNat` の薄い橋を置いただけではなく、

\[
\text{supportMass} = \operatorname{rad}
\]

を軸にして、

- prime channel 版の下界
- primitive witness 版の下界
- family 版の下界
- package 版の下界

まで揃っている。

当初の plan では translation layer に徹する段階だったが、実際にはその translation layer の中で **lower-bound spine がかなり育った**。  
ここは今回の大きな数学的収穫である。

## 3.5. Phase E. 例と public import

ここも **完了** と判定してよい。

- concrete example が入った
- family API の使用確認も済んだ
- `ABC.Bridge` と `ABC.Main` 経由の公開導線まで整った

したがって、「空抽象ではないか」の確認と、「外からどう使うか」の確認の両方が済んでいる。

---

## 4. 今回の本当の新規性

今回の新規性は、ABC パッケージそのものに **新しい橋の数学** が入ったことにある。

それは次の一本に要約できる。

\[
\text{primitive witness family}
\;\to\;
\text{diff 側の prime channel family}
\;\to\;
\text{supportMass lower bound}
\]

ここで `supportMass` は `rad` の別名として立っているから、結局

\[
\text{primitive flow}
\;\to\;
\text{disjoint channels}
\;\to\;
\operatorname{rad}\text{ の下界}
\]

という読みまで到達している。

これは以前は「面白い見方」だったものが、今や Lean 上で theorem 名を持つ spine になった、という意味で確かな進展である。

特に重要なのは、これはまだ ABC 本体の不等式を直接証明したわけではないが、ABC で最も使いたい量の一つである `rad` に対し、

**異なる channel が増えると support mass が下から持ち上がる**

という形を明示したことである。  
これにより、primitive prime の存在や分離が、単なる局所情報ではなく **global lower bound** に変換できるようになった。

---

## 5. ABC 予想本体に対して何が進んだか

ここは冷静に切り分けるべきである。

**進んだ。だが、本体不等式へ直撃したのではなく、本体へ入るための中間レイヤが強くなった。**

つまり、今回整ったのは

- `abc_big_eq_body_add_gap_mass`
- `abc_gap_mass_le_big_mass`
- `abc_residual_eq_gap_mass`
- `supportMass_ge_prod_of_prime_channel_family`
- `primitive_witness_family_force_supportMass_lower_bound`

のような補題群であり、ABC 側で

- mass
- support
- primitive channel
- `rad`
- local load

を同じ言語で扱う準備がかなり進んだ。

しかし一方で、既存 ABC 本丸の

- Janson–Suen 系
- bad set density 系
- mgf / measure 系
- `ABC021.lean` まわりの未完解析

そのものを今回閉じたわけではない。

したがって、現段階の正確な評価は、

\[
\text{ABC 主定理そのものが一気に進んだ}
\]

ではなく、

\[
\text{ABC 本丸へ入るための別ルート候補がかなり整った}
\]

である。

---

## 6. 現況の評価

### 6.1. これは「準備」ではあるが、ただの準備ではない

単なる命名整理や import 整理で終わっておらぬ。

- `supportMass = rad`
- family lower bound
- primitive witness family package
- public import

まで揃っているので、これは **数学内容を持つ infrastructure** と言ってよい。

### 6.2. 進展の中心は ABC パッケージそのものではなく、その前段の橋

今回の主な実装場所は見かけ上 `ABC/*` であるが、実質の心臓部は

- `CosmicFormula/Mass/*`
- `NumberTheory/ValuationFlow/*`

にある。

ABC パッケージには、それを読むための翻訳面と公開導線が入った。  
ゆえに「ABC パッケージに何か新しい進展があったか」と問われれば、

**yes。ただし本体ではなく bridge の進展**

と答えるのが正確である。

### 6.3. 設計・実装計画に対する逸脱は少ない

今回のスナップショットはかなり計画どおりである。

むしろ想定以上に進んだのは、

- two-channel 版で止まらず
- `Finset` family 版
- package 版
- public import

まで進んだ点である。  
これは良い意味での前倒しじゃ。

---

## 7. これからか、それとももう新段階か

答えは **両方** である。

### 7.1. もう新段階に入っている理由

いまや bridge は

- theorem 群
- examples
- family API
- package API
- public import

を全部持っている。  
これはもう設計メモではなく、**利用できる層** である。

### 7.2. それでも「これから」である理由

ABC 本丸から見れば、まだ次の大事な分岐が残っている。

#### A. この bridge 層をどの中間命題へ差し込むか

たとえば

\[
\text{primitive channel 数}
\;\Rightarrow\;
\operatorname{rad}(abc)\text{ 下界}
\;\Rightarrow\;
\text{quality や valuation の制約}
\]

という線を、既存 ABC コアのどこへ噛ませるかを決める必要がある。

#### B. 「確率」側をどこまで本当に実装するか

設計では、

- exact な Markov / sub-Markov
- \(\Lambda(q)/\log n\) kernel
- hitting の完成形

は後回しだった。

したがって、本当に Erdős #1196 的な確率視点そのものへ進むなら、今後は `Hitting` 層や actual probabilistic layer を作る必要がある。そこはまだ未着手である。

---

## 8. 最終判断

今回のスナップショットで、

**Erdős #1196 由来の mass / channel / support の考え方は、ABC 側で使える公開 bridge API として一段完成した。**

これは確かな新進展である。  
しかも単なる整理ではなく、

\[
\text{primitive flow}
\;\to\;
\text{disjoint channels}
\;\to\;
\operatorname{rad}\text{ の下界}
\]

という lower-bound spine まで入っている。

ただし、**ABC 予想本体の重い未完核はまだ残っている。**  
ゆえに「もう勝った」とは言えぬ。じゃが、

**別ルートの足場がかなり強くなった**

とは、はっきり言ってよい。

現況を象徴的に言うなら、今は

\[
\text{橋を作り終え、どの城門に接続するかを選ぶ段階}
\]

じゃな。

---

## 9. 次の実務的な分岐案

現況から見ると、次の選択肢は主に二つである。

### 9.1. bridge を ABC 本丸の中間命題へ接続する

これは最も数学的に前へ進む道である。  
狙いは、

- primitive channel family
- support mass lower bound
- `rad(abc)` 下界
- quality / valuation 制約

の連鎖を、本丸の既存補題群と接続すること。

### 9.2. 確率質量保存 API を本当に `Hitting` 側まで進める

こちらは Erdős #1196 的発想をさらに素直に押し込む道である。  
つまり、

- `Branch`
- `SubConservative`
- `ValuationFlow`
- `Hitting`

を完成に近づけることで、

\[
\sum \text{子の質量} \le \text{親の質量}
\]

の一般原理を、さらに hitting / antichain 的評価へ持ち上げる道じゃ。

---

## 10. ひとことで総括

**ABC 本体はまだこれから。  
しかし、ABC に入るための橋は、今回の実装でかなり本物になった。**
