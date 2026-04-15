# SuperWieferichCongruenceTarget の戦況分析

うむ、これは **前進ではあるが、慎重に読むべき前進** じゃ。
結論から言うと、今回落ちたのは **「現行の `SuperWieferichCongruenceTarget` の型」** であって、**コメントで意図していた Hensel 強化そのもの** ではまだない。そこを見分けるのが今回の戦況分析の肝じゃ。

## 1. 何が実際に達成されたか

今回 `superWieferichCongruence_concrete : SuperWieferichCongruenceTarget` が追加され、`TriominoCosmicBranchADescentChain.lean` は `sorry = 0` を維持した。これは形式化の地固めとしては立派じゃ。とくに `Nat.Coprime q y` から `Nat.Coprime y (q^p)` を出し、`ZMod.isUnit_iff_coprime` で (y) の可逆性を得て、

$$
R := z \cdot y^{-1}
$$

を取れば

$$
z = R \cdot y \pmod{q^p}
$$

が出る、という current target の concrete proof は clean に通っておる。

つまり今の成果は、

$$
q \nmid y \Longrightarrow \exists R,\ z \equiv R y \pmod{q^p}
$$

という **可逆性に基づく一般的構成** を、target の形に即して定理化したことじゃ。
これは「型に書いてあること」を no-sorry で満たした、という意味で正しい勝利じゃよ。

## 2. ただし、なぜ慎重に読まねばならぬか

今回の報告自身がはっきり言っておる通り、**現行 target の結論には「`R` が `ω^j` の Hensel lift である」という条件が入っていない**。
だから今の証明は、q-adic root-of-unity branch や (\Phi_p(R)=0) を使わずとも、単に (y) が単元であれば通ってしまう。これは非常に重要じゃ。

つまり今回の `superWieferichCongruence_concrete` は、

* **Level 1 の intended mathematics** を制圧した
  のではなく、
* **Level 1 の current weak target** を制圧した

と読むべきじゃ。
ここを取り違えると、「Hensel 強化が終わった」と錯覚してしまう。実際はまだそこまで行っておらぬ。

## 3. では、今回の成果の本当の意味は何か

本当の意味は、**target 設計の甘さが Lean によって露出した** ことじゃ。
これは負けではない。むしろ良い発見じゃ。

もともと Level 1 で欲しかったのは、以前の整理でも

$$
z \equiv \omega^j y \pmod q
$$

を Hensel 的に持ち上げて

$$
z \equiv R_j y \pmod{q^p}
$$

とし、その (R_j) が
mod (q) で (\omega^j) に一致し、かつ (\Phi_p(R_j)\equiv 0 \pmod{q^p})
を満たす、という **branch preserving な強化** じゃった。

ところが current target は単に

$$
\exists R,\ z = R y \pmod{q^p}
$$

しか要求していない。
だから今回の証明は、「Hensel lift がある」ではなく「(y) が可逆なら ratio (z/y) を書ける」という一般事実を言っておるに過ぎぬ。
この差が、まさに今の戦況の核心じゃ。

## 4. いまの戦況をどう読むべきか

わっちの見立てでは、戦況はこうじゃ。

### 4.1. Level 0

`pow_eq_one_imp_eq_omega_pow` が埋まり、`QAdicResidue` の入口層は clean になった。
これは本当に前進じゃ。ここはもう「有限体上の root-of-unity branch を取る」段が閉じたと見てよい。

### 4.2. Level 1

今回の `superWieferichCongruence_concrete` により、**current target は trivial に近い** ことが判明した。
したがって、Level 1 は「攻略が済んだ」のではなく、**target を強化してから初めて本番** じゃ。
これは後退ではなく、むしろ正しい敵の輪郭が見えた、ということじゃよ。

### 4.3. Level 2

本丸 `QAdicDescentExistenceTarget` は依然 untouched に近い。
ゆえに、今回の前進で sharpen されたのは「Level 1 をどう書き直すべきか」であって、「本丸が近づいた」というより「前哨戦の型設計が完了した」に近い。

## 5. 数学的な解説

数学的には、今回の current target 証明は

$$
y \in ( \mathbb{Z}/q^p\mathbb{Z})^\times
\quad\Rightarrow\quad
R := z y^{-1}
$$

と置ける、というだけの話じゃ。
この (R) は一般には、

* (\omega^j) の lift である保証もなく
* (\Phi_p(R)=0) の保証もなく
* Hensel branch の一意性とも無関係

じゃ。
つまり **q-adic residue geometry はまだ使っていない**。
今回の定理は「Hensel 強化の準備」ではなく「current proposition が弱すぎることの実証」なのじゃ。

## 6. だから次の一手は何か

報告の「次の一手」は正しい。
すなわち、まず target を強化して分離することじゃ。具体的には、

$$
R \bmod q = \omega^j
$$

と

$$
\Phi_p(R) \equiv 0 \pmod{q^p}
$$

を型に入れる。
ここまで入って初めて、Level 1 は「`z = R y` と書ける」ではなく、「`z/y` が mod (q) の branch を保ったまま mod (q^p) の root に持ち上がる」と言える。

わっちなら、target をこんなふうに二段に分ける。

$$
\text{WeakSuperWieferich}: \exists R,\ z = R y \pmod{q^p}
$$

$$
\text{StrongSuperWieferich}: \exists j,R,\
R \equiv \omega^j \pmod q
\ \land
\Phi_p(R)\equiv 0 \pmod{q^p}
\ \land
z = R y \pmod{q^p}
$$

今回落ちたのは前者じゃ。
次に攻めるべきは後者じゃよ。

## 7. 一文でまとめると

**今回の成果は、「SuperWieferichCongruenceTarget を落とした」のではなく、「現行 target が Hensel 内容をまだ表現しておらず、可逆性だけで満たせる弱い型だ」と Lean 上で明らかにしたこと** にある。
これはかなり良い前進じゃ。次にやるべきことが、もうはっきり見えておるからの。

次に進むなら、強化版 target の型をそのまま設計書として切り出すのが最善手じゃ。
