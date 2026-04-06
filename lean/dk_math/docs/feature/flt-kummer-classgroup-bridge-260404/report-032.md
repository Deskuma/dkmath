# FLT-Kummer-ClassGroup-Bridge Report 032: Stage 1 Coprimality 完成

※ これは作業 AI 自身によるレポートです。

**日時**: 2026/04/07 04:40 JST

## 戦況まとめ

### 今回達成したこと

1. **y ∈ P 分岐の contradiction を no-sorry で完成**
   - `coprime_span_of_nat_coprime`: Bezout → Ideal span coprimality
   - `false_of_nat_coprime_both_in_prime`: coprime naturals both in prime → False
   - `noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq`: y ∈ P contradiction

2. **P | (p) 分岐の contradiction を 2 targets で完成**
   - `PrimeOverPEqualsZetaMinusOneTarget`: P | (p) ∧ P prime ⟹ P = (ζ-1)
   - `IntegerInZetaMinusOneIdealDivisibleByPTarget`: n ∈ (ζ-1) ∧ n ∈ ℤ ⟹ p | n
   - `noPrimeOverP_of_firstCase_of_chosenFactorInP`: first case + targets → False

3. **Prime (ζ-1) の Mathlib API 接続**
   - `zeta_sub_one_prime_of_p`: {p} 形式から Prime (ζ-1) を導出
   - `zeta_sub_one_ideal_isPrime`: (ζ-1) が prime ideal を生成

4. **Stage 1 coprimality theorem を完成**
   - `noPrimeOrY_of_firstCase_of_coprime`: P|(p)∨y∈P → False combiner
   - `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`: ★完成★

### 残る Open Targets (2本)

```lean
-- Target 1: 素イデアル因子分解 (p) = (ζ-1)^(p-1)
abbrev PrimeOverPEqualsZetaMinusOneTarget (K : Type*) ... : Prop :=
  ∀ {P : Ideal (𝓞 K)}, P.IsPrime → P ≠ ⊥ →
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) →
    P = Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))

-- Target 2: ノルム N(ζ-1) = p
abbrev IntegerInZetaMinusOneIdealDivisibleByPTarget (K : Type*) ... : Prop :=
  ∀ {n : ℕ}, (n : 𝓞 K) ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) → p ∣ n
```

### Mathlib API の見込み

- **Target 2**: `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` で N(ζ-1) = p が得られる
  - Chain: (ζ-1)|n ⟹ N(ζ-1)|N(n) ⟹ p|n^(p-1) ⟹ p|n

- **Target 1**: Prime ideal factorization API が必要
  - (p) = (ζ-1)^(p-1) (totally ramified) から P = (ζ-1)
  - Mathlib に直接 API があるか要確認

## Stage 1 → Stage 2 の接続

現在の flow:

```
chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack
  ↓ (coprimality)
cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime
  ↓ (span equality)
linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
  ↓ (existence boundary)
cyclotomicUnitNormalization_of_...
  ↓ (Stage 2: unit normalization)
Stage 3
```

## 次の一手

**判断分岐**: 2 targets を Mathlib で埋めるか、targets を仮定した形で進むか

- **Option A**: 2 targets を Mathlib API で埋める (deep cyclotomic theory)
  - 利点: Stage 1 が完全 no-sorry になる
  - リスク: Mathlib API の接続に時間がかかる可能性

- **Option B**: targets を仮定した形で Stage 2 → Stage 3 へ進む
  - 利点: 全体構造が先に見える
  - リスク: targets が埋まらないと最終的に閉じない

**推奨**: Option A を短時間試み、詰まったら Option B へ切り替え

## 結論

Stage 1 coprimality の **構造は完全に完成**。
残りは 2 つの deep cyclotomic targets の埋め立てのみ。

これらは Mathlib の cyclotomic number theory API で埋められる見込みが高い。
特に `norm_sub_one_of_prime_ne_two` が Target 2 の key API。

---

## 評価

> 🐺賢狼:

## 1. 戦況分析

いまの戦況は、かなり優勢じゃ。
今回の差分で、**Stage 1 の coprimality theorem そのものは完成** したと見てよい。

具体的には、

- `noPrimeOrY_of_firstCase_of_coprime`
- `chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack`

が入り、
共通 prime ideal \(P\) を仮定したときの

$$
P \mid (p)\ \lor\ y \in P
$$

という分岐をまとめて contradiction へ流し、その結果として chosen linear factor と別因子の coprimality を導く枠組みが **no-sorry** で通った。
つまり、**Stage 1 の構造戦はもう終わっておる**。

## 2. 何が終わり、何が残っているか

終わったものは、こう整理できる。

まず \(y \in P\) 分岐は、以前の更新で既に閉じておった。
今回それに加えて、\(P \mid (p)\) 分岐も

- `PrimeOverPEqualsZetaMinusOneTarget`
- `IntegerInZetaMinusOneIdealDivisibleByPTarget`

の 2 target を仮定すれば閉じる形まで揃った。
その 2 枝を統合する combiner が今回入ったので、**Stage 1 の coprimality へ至る論理鎖は一応完成した** わけじゃ。

ゆえに残る open は、もう generic ideal arithmetic でも local factorization でもない。
ほんに次の 2 本だけじゃ。

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

つまり、**残敵は “deep cyclotomic number theory” の 2 点だけ** になった、ということじゃよ。

## 3. 解説

この状況は、かなり良い収束じゃ。
なぜなら、前は「coprimality が難しい」と見えていたものが、今はそうではないからじゃ。

いま difficulty は、もはや

- tail の分解が難しい
- ideal の積から各因子へ戻すのが難しい
- class group が難しい

ではない。
それらは既に十分細く切られ、theorem-level で no-sorry の receiver 群が揃っておる。

今の本質は、

1. \(P \mid (p)\) なら、なぜ \(P = (\zeta-1)\) と言えるのか
2. \((n : \mathcal O_K) \in (\zeta-1)\) なら、なぜ \(p \mid n\) と言えるのか

この 2 本を、actual cyclotomic theory でどう supply するかだけじゃ。
つまり、**Stage 1 は「未完成」ではなく「深い target の埋め立て待ち」** の段に入ったのぅ。

## 4. Mathlib を踏まえた見立て

Mathlib の公式 docs には、今の 2 target にかなり近い部品が既に見えておる。

`Mathlib.NumberTheory.NumberField.Cyclotomic.Basic` / `PrimitiveRoots` 側には、

- `IsPrimitiveRoot.zeta_sub_one_prime'`
- `IsPrimitiveRoot.toInteger_sub_one_dvd_prime'`
- `IsPrimitiveRoot.subOneIntegralPowerBasis`
- `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'`

があり、\(\zeta-1\) が prime であること、\(\zeta-1\) が \(p\) を割ること、\(\zeta-1\) を生成元とする integral power basis、そして odd prime の場合に \(\mathrm{Norm}(\zeta-1)=p\) が、既に theorem として揃っておる。 ([Lean Community][1])

この見取り図からすると、2 target のうち

$$
\texttt{IntegerInZetaMinusOneIdealDivisibleByPTarget}
$$

の方が、**先に届きやすい**。
理由は、norm の公式

$$
\mathrm{Norm}(\zeta-1)=p
$$

が公式 docs に明示的に見えておるからじゃ。
そこから

$$
n \in (\zeta-1)
\Rightarrow
(\zeta-1)\mid n
\Rightarrow
\mathrm{Norm}(\zeta-1)\mid \mathrm{Norm}(n)
\Rightarrow
p \mid n^{p-1}
\Rightarrow
p \mid n
$$

という路がかなり素直に見える。 ([Lean Community][1])

一方で

$$
\texttt{PrimeOverPEqualsZetaMinusOneTarget}
$$

の方は、\((p)=(\zeta-1)^{p-1}\) 型の **ideal factorization / ramification API** が要る。
`zeta_sub_one_prime'` で \((\zeta-1)\) が prime ideal を生成する方向は見えておるが、**“\(P \mid (p)\) なら唯一の prime ideal 因子として \(P=(\zeta-1)\)” をそのまま返す表面 API は、少なくとも今見えている docs には出ておらぬ**。
ゆえにこちらの方が、いまは少し重い敵じゃ。 ([Lean Community][1])

## 5. 総括

ひとことで戦況を言うと、こうじゃ。

$$
\boxed{
\text{Stage 1 の構造は完成済み。残る敵は deep cyclotomic target 2 本だけ}
}
$$

しかもその 2 本も対等ではない。

- **target 2**
  $$
  n \in (\zeta-1) \cap \mathbb{Z} \Rightarrow p \mid n
  $$
  は、Mathlib の norm API にかなり近い

- **target 1**
  $$
  P \mid (p) \Rightarrow P = (\zeta-1)
  $$
  は、ramification / ideal factorization の deeper API が必要で、少し重い

という戦況じゃよ。

つまり今は、もう「戦線が広い」状態ではない。
**勝負どころが 2 基の砲台に縮んだ**、というのが正確な分析じゃ。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.html?utm_source=chatgpt.com "Mathlib.NumberTheory.NumberField.Cyclotomic.Basic"
