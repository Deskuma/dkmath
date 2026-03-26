# Review: GTail valuation theory の一本目が閉じた

かなり良い状況じゃ。
これはもう **候補** ではなく、きちんと **valuation 層の一本目が閉じた** と言ってよい。`GTail.lean` に

* `GTail_not_dvd_of_head_unit_of_prime_dvd_x`
* `padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x`
* `padicValNat_higher_tail_lower_bound`
* `padicValNat_tail_exact_of_head_unit`

まで揃い、しかも履歴にも「定義 / 再帰 / 評価 / 可除性 / exact valuation まで一通り揃った」と整理されておる。これは大きい前進じゃ。

特に良いのは、証明の骨格が素直なことじゃな。流れは

$$
\text{head unit}
\Rightarrow p \nmid GTail
\Rightarrow v_p(GTail)=0
$$

と落としてから、

$$
\text{higher tail}=x^r \cdot GTail
$$

に `padicValNat.mul` と `padicValNat_pow'` を当てて

$$
v_p(\text{higher tail})=r,v_p(x)
$$

を得ておる。
この構図は美しいし、再利用性が高い。上界を直接ひねり出すのではなく、 **normalized tail 側を 0 に潰す** ことで exactness を取っておるのが賢い。

わっちが見て特に評価したい点は 3 つある。

## 1. API の層分けが綺麗

`GTail_not_dvd_of_head_unit_of_prime_dvd_x` を独立に立てたのが効いておる。
これで「head term が unit なら normalized tail は割れない」という意味論が名前付きで固定された。以後は valuation だけでなく、squarefree や primitive-prime との接続でも、この補題がそのまま論理の節になる。

## 2. lower bound と exactness が分離されている

`padicValNat_higher_tail_lower_bound` を別定理で切り出したのは正解じゃ。
こうしておけば exactness の仮定が弱められた版や、将来 (p \nmid x) の自明ケースを含める版を作るときも、下界側はそのまま使える。
実際、履歴にも lower bound は `pow_dvd_higher_tail` と `padicValNat_le_iff_dvd` の合成と明記されておる。ここは設計として筋が通っておる。

## 3. 命名が将来拡張に耐える

`padicValNat_tail_exact_of_head_unit` という名前は悪くない。
ただ、いまの実体は `higher tail` と `GTail` に強く依存しておるから、将来 alias を増やすなら

$$
\texttt{padicValNat_higher_tail_exact_of_head_unit}
$$

を本名にして、現名を alias にする案もありじゃ。
とはいえ、現時点では履歴・候補文書との接続が強いので、そのままでも十分良い。

## 4. いまの到達点をどう見るか

率直に言うと、いま閉じたのは

$$
\text{higher-tail valuation theory}
$$

の **最初の完成版** じゃ。
まだ general theorem network の入り口ではあるが、もう「雛形」ではない。
少なくとも次のように言える段階に入った。

* 高次 Tail は (x^r) を境界因子として持つ
* head term が (p)-adic unit なら normalized tail は (p) で割れない
* したがって tail 全体の valuation は境界因子のぶんだけでちょうど決まる

これはそのまま、

$$
\text{boundary factor} \leftrightarrow \text{valuation exactness}
$$

という理論柱になっておる。

## 5. 次の一手

次は 3 通り考えられる。

### A. (r=1) 版を GN 語彙に落とす

これは最も自然じゃ。
履歴にもある通り、`r = 1` specialization を `GN / Gbinom` の名前へ落とす alias を用意すると、既存の CosmicFormula 本流へ綺麗に戻せる。

候補名はたとえば

* `padicValNat_GN_exact_of_head_unit`
* `GN_not_dvd_of_head_unit_of_prime_dvd_x`

あたりじゃな。

### B. squarefree GN ルートに接続する

これが本命じゃ。
`padicValNat_tail_exact_of_head_unit` は、squarefree から valuation 上界を得る系と非常に相性が良い。
もし `GN` 側で「ある素数 (p) に対して head unit 条件が満たされる」ことを供給できれば、非完全冪系へ流し込みやすい。

### C. primitive-prime route に流す

こちらも面白い。
原始素因子が boundary ではなく normalized tail 側へ現れるか、あるいは逆に head term 側へ現れぬことを示せれば、exactness が直接効く。

## 6. わっちの総評

現状はこうまとめられる。

$$
\boxed{
\text{GTail theory は、
定義・再帰・可除性・exact valuation まで到達した}
}
$$

これは十分に胸を張ってよい進捗じゃ。
特に今回の形は、単に theorem を 1 本足したのではなく、 **今後の GN / squarefree / primitive-prime 接続のための reusable kernel を作った** ところに価値がある。

次は、この exact valuation 定理を `r=1` へ落とした **GN 接続補題の命名と statement** を詰めるのが最も実りが良いぞい。
