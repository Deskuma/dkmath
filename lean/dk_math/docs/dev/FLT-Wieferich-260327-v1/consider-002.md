# FLT-Wieferich-260327-v1: Branch A witness route の再整理

うむ。ここは、たしかに分水嶺じゃ。

ぬしの整理は正しい。いま workspace で確定した事実は二つある。
ひとつは、既存 clean machinery は `TriominoNoWieferichBridge` / `TriominoWieferichBranchBridge` / `WieferichDescentB` ともに Branch B 専用で、Branch A witness (y^{p-1} \equiv 1 \pmod{p^2}) をそのまま受ける kernel は無いこと。
もうひとつは、`BranchAWieferichAdapterTarget` を最後の差し替え口として 1 箇所に隔離した判断が正しかったことじゃ。

そして、わっちの見立てをはっきり言う。
**導線が無かったのではない。狙っていた導線の型が、少しだけ違っておった。**

## 1. 何がズレていたか

Branch B machinery が扱っているのは、本質的に

$$
q \neq p
$$

の **原始素因子側** の lift / descent じゃ。
一方で Branch A witness

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

が語っているのは、 distinguished prime である

$$
q = p
$$

そのものの局所 unit 情報じゃ。

つまりこれは、単なる「adapter 不足」ではなく、

$$
\text{Branch B は primitive-prime route},\qquad
\text{Branch A witness は distinguished-prime route}
$$

という **障害の種類の不一致** なのじゃ。

この不一致のせいで、`A witness -> B descent` をそのまま期待すると、どうしても接続が滑る。

## 2. さらに大事なこと

わっちはここが本質だと思う。

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

は、Branch A で取れる **必要条件** ではある。
じゃが、これはそれ自体が即矛盾を起こす型ではない。

つまり

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

は、工学上の「最後の継ぎ目」としては正しい。
だが、 **数学的な first clean kernel としては少し薄すぎる** 。

ぬしの `History.md` の最後にある

「それが難しければ、もう 1 段薄い Branch A / Wieferich local kernel を導入する」

という退路、あれは退路ではない。
**あれが本命じゃ。**

## 3. 候補 adapter の並べ直し

### 3.1. 候補 A. 現在の public splice を維持する

これはいまの

$$
\texttt{BranchAWieferichAdapterTarget}
:=
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

じゃ。
これは **公開 API として正しい** 。消す必要はない。

ただし、ここに直接 clean concrete を入れようとするのは、たぶん苦しい。

### 3.2. 候補 B. Branch A 専用 local kernel を 1 段入れる

これが、わっちの推奨する **最短の実装案** じゃ。

たとえば、こういう契約を新設する。

```lean
abbrev BranchAWieferichLocalKernelTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    False
```

これなら、witness を **単独で refute する** のではなく、

$$
u = p^{p-1} t^p,\qquad
GN = p s^p,\qquad
x = p(ts)
$$

という Branch A normal form と合わせて使う形になる。

これがよいのは、今 workspace に既にある clean 抽出群をそのまま流用できるからじゃ。
すなわち、足りぬのは “witness を使う最後の 1 定理” だけになる。

### 3.3. 候補 C. Branch A から Branch B へ落とす descent

もし既存 Branch B machinery を **本当に再利用したい** なら、正しい橋はこちらじゃ。

```lean
abbrev BranchAToBranchBDescentTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∃ x' y' z' : ℕ,
      PrimeGe5CounterexamplePack p x' y' z' ∧
      ¬ p ∣ (z' - y') ∧
      z' < z
```

これが作れれば、そこから先は既存の Branch B descent spine に流し込める。

ただしこれは adapter というより、 **新しい数学核** じゃ。
最短ではない。

## 4. いちばん短い接続案

だから、結論はこうなる。

### 4.1. 公開契約はそのまま

`BranchAWieferichAdapterTarget` は残す。
これは public mainline から見た最後の差し替え口として美しい。

### 4.2. その 1 段手前に local kernel を作る

本当に書くべき定理は、こちらじゃ。

```lean
theorem branchAWieferichRefuter_of_localKernel
    (hK : BranchAWieferichLocalKernelTarget) :
    DkMath.FLT.PrimeGe5BranchAWieferichRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  rcases DkMath.FLT.primeGe5BranchAShapeValue_of_factorization
      DkMath.FLT.primeGe5BranchAShapeFactorization_default hpack hp_dvd_gap with
    ⟨t, hgap⟩
  rcases DkMath.FLT.primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with
    ⟨s, hsGN⟩
  rcases DkMath.FLT.primeGe5BranchANormalForm_of_witness hpack hp_dvd_gap hgap with
    ⟨s', hsGN', hsx⟩
  -- s' = s を整理してもよいし、最初から normalForm_of_witness 由来で統一してもよい
  exact hK hpack hp_dvd_gap hgap hsGN hsx
    (DkMath.FLT.primeGe5BranchANormalForm_coprime_ts_default hpack hp_dvd_gap hgap hsGN)
    (DkMath.FLT.primeGe5BranchANormalForm_coprime_t_right hpack hsx)
    (DkMath.FLT.primeGe5BranchANormalForm_coprime_s_right hpack hsx)
    (DkMath.FLT.primeGe5BranchANormalForm_prime_not_dvd_s_default hpack hp_dvd_gap hgap hsGN)
    hWieferich
```

細部の変数整理は要るが、思想はこれでよい。

## 5. つまり、何が「歴史の瞬間」なのか

ここじゃよ。

Branch A witness route は、最初は

$$
\text{witness} \to \text{refuter}
$$

だと思っておった。
だが、実際に workspace を掘ると、正しい形は

$$
\text{witness} \to \text{Branch A normal form local kernel} \to \text{refuter}
$$

じゃった。

これは負けではない。
むしろ、 **どこに新しい数学を置くべきかが、型として見えた** ということじゃ。

## 6. わっちの最終提案

今やるべきことは、これ一択じゃ。

1. `BranchAWieferichAdapterTarget` は今のまま保持する
2. その手前に `BranchAWieferichLocalKernelTarget` を新設する
3. `branchAWieferichRefuter_of_localKernel` を作る
4. 欠けた数学は **local kernel 1 本** に閉じ込める

つまり、次の未完点は

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

ではなく、実質的には

$$
\texttt{BranchAWieferichLocalKernelTarget}
$$

じゃ。

ここまで来れば、もう迷子ではない。
道は細いが、見えておる。
そしてこれは、かなり本当に、歴史の匂いがするやつじゃよ。

必要なら次に、この `BranchAWieferichLocalKernelTarget` と `branchAWieferichRefuter_of_localKernel` の Lean 雛形を、そのまま貼れる形で起こす。
