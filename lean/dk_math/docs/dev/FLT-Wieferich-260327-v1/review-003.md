# Branch A witness local kernel についての考察

うむ、これは **前進** じゃ。
工学としては、とてもよい切り分けになっておる。`PrimeGe5BranchAWieferichLocalKernelTarget` を置き、`primeGe5BranchAWieferichRefuter_of_localKernel` と gap-invariant 側の adapter まで通したことで、欠けた一点が **local kernel 1 本** に見えるようになった。これは確かに設計上の勝ちじゃ。

じゃが、ここで賢狼としては、少し強く言うぞい。

**最大限の推論で見ると、この local kernel は「見える化」には成功したが、数学的にはまだ本質的に縮んでおらぬ。**

## 1. いちばん大事な観測

今回の local kernel は

$$
hpack,\ hp_dvd_gap,\ hgap,\ hsGN,\ hsx,\ t \perp s,\ t \perp y,\ s \perp y,\ p \nmid s,\ y^{p-1}\equiv 1 \pmod{p^2}
$$

から `False` を返す契約じゃな。

ところが workspace を読むと、Branch A normal form 側には既に

$$
hpack,\ hp_dvd_gap,\ hgap,\ hsGN
$$

だけから

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

を出す定理 `primeGe5BranchANormalForm_y_wieferich_mod_p_sq` がある。
つまり、 **local kernel に入れた witness は、normal form から既に再生成できる** 。

この一点が本質じゃ。

ゆえに新 kernel は、

* 工学的には別 route を作った
* だが数学的には **新情報を 1 ビットも追加していない**

という構図になっておる。

## 2. さらに言うと、ほぼ arithmetic kernel と同値じゃ

workspace には既に

* `primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default`
* `primeGe5BranchANormalForm_coprime_ts_default`
* `primeGe5BranchANormalForm_coprime_t_right`
* `primeGe5BranchANormalForm_coprime_s_right`
* `primeGe5BranchANormalForm_prime_not_dvd_s_default`

がある。
今回の bridge でも後半 4 本は既に使っておるし、`gcd = p` も同様に既定抽出できる。

したがって実質的には、

$$
\texttt{PrimeGe5BranchAWieferichLocalKernelTarget}
$$

は

$$
\texttt{PrimeGe5BranchANormalFormArithmeticKernelTarget}
$$

の **Wieferich 名札付き版** にかなり近い。

わっちの見立てでは、これはほぼ次の二定理で往復できる。

```lean
theorem primeGe5BranchAWieferichLocalKernel_of_arithmeticKernel
    (hK : PrimeGe5BranchANormalFormArithmeticKernelTarget) :
    PrimeGe5BranchAWieferichLocalKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hWieferich
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    (primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default hpack hp_dvd_gap hgap hsGN)
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s
```

```lean
theorem primeGe5BranchANormalFormArithmeticKernel_of_wieferichLocalKernel
    (hK : PrimeGe5BranchAWieferichLocalKernelTarget) :
    PrimeGe5BranchANormalFormArithmeticKernelTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hgcd_eq hcop_ts hcop_ty hcop_sy hp_not_dvd_s
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s
    (primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN)
```

ここで `hgcd_eq` は後者では未使用になる。
つまり、 **いまの local kernel は truly new kernel というより、旧 arithmetic kernel の別表現** なのじゃ。

## 3. なので、残る obstruction はどこか

ここが大事じゃが、残る obstruction は **Branch A witness そのものではない** 。

残っておるのは、もともと comparison route の最深部にいた

$$
\texttt{primeGe5BranchANormalFormNePCoprimeKernel_default}
$$

系統の「`Nat.Coprime t s` まで縮んだ後、どう `False` に落とすか」という核じゃ。
その TODO も、趣旨としては

$$
\text{comparison route の active 情報はここで尽きている}
$$

と言っておる。

だから、今回の変更で **見え方** は良くなった。
だが obstruction の **場所** は、実はあまり動いておらぬ。

## 4. ここで進むべき本当の二択

ここから先は、道は二本じゃ。

### 4.1. 道 A. 「Wieferich route は新情報を生んでいない」と明文化する

これは設計を綺麗にする道じゃ。

まず上の 2 定理を書いて、

$$
\texttt{AWieferichLocalKernel} \simeq \texttt{ArithmeticKernel}
$$

を型で固定する。
すると、「Wieferich route でまだ新しい数学は入っていない」という事実が Lean 上ではっきりする。

これは後で迷わなくて済む。
かなり大事じゃ。

### 4.2. 道 B. 本当に新しい distinguished-prime kernel を作る

こちらが数学を前へ進める道じゃ。

必要なのは、 **normal form から既に出る事実ではない** 入力じゃ。
つまり `y^(p-1) ≡ 1 [MOD p^2]` では弱い。これ自体はもう既に normal form の帰結だからのぅ。

必要なのは例えば、

* (p)-進 valuation の **厳密な深さ**
* Branch A から **より小さい反例 pack** を作る descent
* `p` 自身に対する no-lift / no-Wieferich の distinguished-prime 版

のどれかじゃ。

たとえば contract としては、こんな形のほうが「新しい」。

```lean
abbrev PrimeGe5BranchADistinguishedPrimeDescentTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ∃ x' y' z' : ℕ,
      PrimeGe5CounterexamplePack p x' y' z' ∧ z' < z
```

これは本当に新しい。
なぜなら、これは normal form から自動では出てこぬからじゃ。

## 5. わっちの結論

今回の変更は正しい。
じゃが、その次に言うべきことはこれじゃ。

**Branch A witness local kernel は、工学的 checkpoint としては成功。
しかし数学的には arithmetic kernel とほぼ同値で、まだ obstruction を突破してはいない。**

ゆえに次の一手は、順番として

1. `AWieferichLocalKernel ↔ ArithmeticKernel` を橋で固定する
2. その上で、真に新しい kernel は
   (p)-進深さ か distinguished-prime descent のどちらで行くかを決める

これがよい。

わっちの勘では、次に刺さるのは **Wieferich route の強化** ではなく、
**Branch A distinguished-prime descent** のほうじゃ。
理由は単純で、今の witness は既に normal form の影だからじゃ。影をいくら磨いても、本体の扉は開かぬ。

必要なら次に、その 2 本の同値 bridge をそのまま貼れる Lean 断片で起こすぞい。
