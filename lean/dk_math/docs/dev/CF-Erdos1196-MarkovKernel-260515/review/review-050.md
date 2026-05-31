# review

## 1. 総括結論

うむ。DKMK-009 は **一区切りとして閉じてよい** 。

今回の E/F で `report-DKMK-009.md` が新規作成され、`DkMath_Markov_kernel-to-ck.md` に DKMK-009 節が追加され、`roadmap-DKMK-009.md` に completion summary が追記された。Lean コード変更はなく、docs/report 整理のみで、`git diff --check` は通過しておる。

到達点は、この一本じゃ。

```text
PrimePowerWitnessProvider
  → globalLogCapacityKernel
  → CapacityKernel generic bridge
  → primePowerQuotientPathFamily
  → weightedHitMass bound
```

これは DKMK-009 の最初の目的、すなわち

```text
capacity kernel の normalized shadow が、
primitive hitting route の正式な入力である
```

を Lean API と docs の両方で固定した、という意味になる。

## 2. DKMK-009 で閉じたもの

DKMK-009B-D の実装成果は、段階ごとにかなり綺麗に役割分担されておる。

| Phase | 閉じた内容                                                    | 主 theorem                                                                                                          |
| ----- | -------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| 009B  | 任意の `CapacityKernel` から hitting bound へ行く generic bridge | `CapacityKernel.weightedHitMass_le_const_applyAtToSourceControlled`                                                |
| 009C  | `globalLogCapacityKernel` への特殊化                          | `PrimePowerWitnessProvider.globalLogCapacityKernel_weightedHitMass_le_const`                                       |
| 009D  | witness-derived quotient path family への接続                | `PrimePowerWitnessProvider.globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound` |

report でも、009B は generic capacity-kernel bridge、009C は selected global log-capacity kernel への特殊化、009D は quotient path family まで含めた本線として整理されておる。

つまり、DKMK-009 は単なる docs 整理ではなく、 **B-D で通した実装 route を、研究章として正式に命名・固定した段階** じゃな。

## 3. 数学的な意味

DKMK-009 の数学的意味は、Markov kernel を直接主役にせず、

```text
CapacityKernel
  ↓ normalized shadow
SubMarkovShadow
  ↓ applyAtToSourceControlled
RealWeightedPathFamily
  ↓ primitive hitting bridge
weightedHitMass bound
```

として読む道を固定したことじゃ。

DkMath の理念である

```text
Markov kernel is a normalized shadow of DkMath capacity kernel.
```

が、ここで単なる思想ではなく、primitive hitting route 上の theorem-facing API になった。

これは大きい。
Erdős #1196 の既存証明的な言葉では Markov / sub-Markov process が前面に出る。しかし DkMath 側では、その手前にある

$$
\sum_{\text{child}} \text{cost} \le \text{capacity}
$$

という capacity 保存・劣保存構造を主語にする。そこから正規化して sub-probability / shadow が出る。
この視点が DKMK-009 で本線化されたわけじゃ。

## 4. DKMK-008 との関係

DKMK-008 は、主に path を作る章だった。

```text
manual path
one-step divisor path
witness-derived multi-step quotient path
```

DKMK-009 は、そのうち witness-derived multi-step quotient path に、capacity kernel の normalized weight を流す章になった。report でも、

```text
DKMK-008:
  path を作る章

DKMK-009:
  capacity kernel の normalized weight を path に流す章
```

という関係として整理されておる。

これは見事な接続じゃ。
008 で道を敷き、009 でその道に log-capacity の流れを通した。まるで水路が開いたようなものじゃな。

## 5. 何がまだ残るか

今回の E/F は docs-only なので、Lean の新規 build は実行していない。これは妥当じゃ。Lean コードは変更しておらず、検証は `git diff --check` と長行 check に留まっている。

残りの選択肢は 2 つ。

第一に、DKMK-010 へ進むこと。

```text
tail / truncation / analytic estimate
```

つまり、いよいよ有限 kernel-hitting spine から、解析的評価へ進む道じゃ。

第二に、必要性が明確な場合だけ、DKMK-009 追補として finite-step / two-step convenience wrapper を追加すること。report でも、convenience wrapper は用途を明確にしてから追加すべき、と整理されておる。

わっちの判断では、今すぐ wrapper を増やすより、まず DKMK-010 の設計に入る方がよい。

## 6. 登頂判定

わっちの判定はこうじゃ。

```text
DKMK-009A: scope 固定
DKMK-009B: generic CapacityKernel bridge
DKMK-009C: global log-capacity specialization
DKMK-009D: quotient path family connection
DKMK-009E/F: docs/report 整理

=> DKMK-009 完了
```

DKMK-009 は、 **finite R/log route の normalized mass を、witness-derived divisor descent path 上の primitive hitting bound へ流す章** として閉じた。

次に見る山は DKMK-010。
そこでは、おそらく

$$
1+O!\left(\frac{1}{\log x}\right)
$$

へ近づくための tail / truncation / source mass estimate が本題になる。

## 7. 賢狼の最終評

よい総括じゃ、ぬしよ。
DKMK-009 は派手な新定理を積み増した章ではない。だが、 **既に作った道具を正しい順序に束ね直し、今後の解析層へ接続できる形にした章** じゃ。

これは研究ライブラリでは極めて大事な段階じゃ。
道具があるだけでは山は登れぬ。道具がどの順に繋がり、どこへ向かうのかが見えて、初めて次の登山が可能になる。

DKMK-009 はその意味で、 **kernel-hitting spine の完成章** と呼んでよい。
