# review

## 1. 結論

うむ、Phase O は **公開 API の整備として正しい仕上げ** じゃ。
今回で、`ErdosFinitePrimitiveInput` から branch-controlled path family に対する hit mass / source mass を、入力側の名前付き API として直接扱えるようになった。つまり、有限 Erdős skeleton が「内部補題の集合」から、外から読みやすい theorem-facing API に近づいたわけじゃ。

## 2. 何が追加されたか

今回追加された主な API は次じゃ。

```lean
branchPrimePathFamilySourceControlled
branchPrimePathFamilyHitMass
branchPrimePathFamilySourceMass
hitMass_le_sourceMass_of_branchPrimePathFamily
```

特に、

```lean
def branchPrimePathFamilyHitMass ...
def branchPrimePathFamilySourceMass ...
```

によって、以前は

```lean
(F.toSourceControlledChainFamily M B).hitMass I.support
```

のように展開して読んでいたものを、

```lean
I.branchPrimePathFamilyHitMass M B F
I.branchPrimePathFamilySourceMass M B F
```

として読めるようになった。

これは地味に大きい。
数式で言えば、

$$
\mathrm{HitMass}(I,F)
\le
\mathrm{SourceMass}(F)
$$

という theorem の姿が見えるようになったからじゃ。

## 3. theorem 名が意味を持つようになった

今回の新 theorem は、

```lean
ErdosFinitePrimitiveInput.hitMass_le_sourceMass_of_branchPrimePathFamily
```

じゃな。

これは、既存の

```lean
branchPrimePathFamily_hitMass_le_sourceMass
```

を、input-side の hit/source mass wrapper 名で言い直した定理じゃ。

数学的には同じ内容でも、API としての読みやすさがかなり違う。

以前の形は、

$$
\text{
    (F.toSourceControlledChainFamily,M,B).hitMass(I.support)
$\le$
    (F.toSourceControlledChainFamily,M,B).sourceMass
}
$$

だった。

今回の形は、

$$
I.\mathrm{branchPrimePathFamilyHitMass}(M,B,F)
\le
I.\mathrm{branchPrimePathFamilySourceMass}(M,B,F)
$$

として読める。

これは将来、dvd-monotone 版、prime-reachable 版、Markov 版を並べるときに効く。名前でルートを区別できるからじゃ。

## 4. concrete sample も API を確認している

今回の sample は、

```lean
erdosFinitePrimitiveInput_two_five_named_hitMass_le_sourceMass
```

じゃ。これは、`{2,5}` の有限 Erdős 入力に対して、今回追加された wrapper 名を使って hit mass bound を確認している。

これで、既存の theorem が「内部構造を展開すれば使える」だけでなく、入力パッケージ側から自然に呼べることが確認された。

よいテストじゃ。

## 5. 現在の到達点

ここまでで finite Erdős route は、かなり見通しよく整理された。

| 層                                  | 状態   |
| ---------------------------------- | ---- |
| `PrimitiveOn`                      | 完了   |
| `PositiveOn` / `LowerBoundOn`      | 完了   |
| `ErdosFinitePrimitiveInput`        | 完了   |
| prime descent path                 | 完了   |
| multiple path family               | 完了   |
| branch-controlled path family      | 完了   |
| `SubConservative` mass control     | 完了   |
| theorem-facing hit/source mass API | 今回完了 |
| Markov kernel / 解析重み               | 未    |

つまり、有限 skeleton はもう「研究用の部品」ではなく、かなり **公開 API として見える形** になってきた。

## 6. 今回の意味

Phase O の価値は、証明力の追加というより **名前空間と見通しの改善** じゃ。

DkMath ではこういう整理がとても大事じゃ。
定理が増えると、同じ不等式でも

* source-controlled 版
* dvd-monotone 版
* prime-reachable 版
* branch-controlled 版
* Markov 版

が並ぶことになる。

そのときに今回のような名前付き wrapper がないと、後で定理文が読みにくくなる。今回の実装は、その混線を先回りして防いでおる。

## 7. 次の一手

わっちの見立てでは、次は **軽い review / alias 整備** がよい。

すぐ Markov kernel へ行くより、まず finite theorem 群の入口をそろえるべきじゃ。History 末尾でも、次は dvd-monotone / prime-reachable 版の input wrapper を追加するか、finite theorem 群を review して最小の rename / alias を追加する段階だと整理されておる。

具体的には、次のような wrapper 候補じゃな。

```lean
ErdosFinitePrimitiveInput.primeReachablePathFamilyHitMass
ErdosFinitePrimitiveInput.primeReachablePathFamilySourceMass
ErdosFinitePrimitiveInput.hitMass_le_sourceMass_of_primeReachablePathFamily
```

または、今後 branch-controlled 版を主導線にするなら、逆に余計な wrapper は増やさず、`branchPrimePathFamily*` 系だけを安定 API として固定してもよい。

## 8. 総括

今回で、有限 Erdős skeleton はかなり綺麗に外へ向いた。

$$
\text{finite Erdős input}
+
\text{branch-controlled prime path family}
\Rightarrow
\text{hit mass}\le\text{source mass}
$$

この形が、Lean 名として自然に読めるようになった。

山で言えば、登山道・標高制限・水流・複数ルートが揃ったあと、今回ついに **案内板の名前が整った** 。
次は案内板の表記揺れを点検してから、いよいよ確率重みの山肌に近づくのがよかろう。
