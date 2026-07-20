# FLT next implementation note — 2026-07-21

## 1. 目的

2026-07-21 に実施した `leanprover-community/flt-regular` の調査結果を、今後の DkMath FLT 実装判断のために記録する。

本調査の目的は、参考実装を最新の DkMath 独自ルートへ流用することではない。次の二点を明確に分離するための事前調査である。

1. 最新の `DkMath.FLT.Five` を、外部の Kummer・円分体ルートから独立した DkMath-native な証明路線として維持する。
2. 過去の `DkMath.FLT` に存在した FLT5 偽命題ルートおよび旧 Kummer route を、正しい古典 Kummer ルートによる対照・制御実装として修復できるか確認する。

## 2. 調査対象

- Repository:
  - https://github.com/leanprover-community/flt-regular
- Main source tree:
  - https://github.com/leanprover-community/flt-regular/tree/master/FltRegular
- 調査時点:
  - 2026-07-21 04:15 JST 頃
- 調査時に確認した `master` の先頭コミット:
  - `a859475b163864437e430f8442da7ac29a4bf109`
  - https://github.com/leanprover-community/flt-regular/commit/a859475b163864437e430f8442da7ac29a4bf109
- 上記コミット日時:
  - 2026-07-10 00:02 JST 頃
- License:
  - Apache License 2.0

参考リポジトリの目的は、任意の素数指数に対する FLT 全体ではなく、**正則素数 `p` に対する Fermat's Last Theorem** の Lean 形式化である。

## 3. 調査結果の要約

### 3.1 参考実装は単なる円分多項式分解ではない

証明の核心は、次の古典 Kummer ルートである。

```text
FLT equation over ℤ
→ cyclotomic field ℚ(ζ_p)
→ ring of integers 𝓞(ℚ(ζ_p))
→ factorization into cyclotomic linear factors
→ ideal factorization in a Dedekind domain
→ p-th power ideal extraction
→ class-group p-torsion annihilation by regularity
→ principalization
→ unit normalization / Kummer lemma
→ Case I contradiction or Case II infinite descent
```

トップ定理は概ね次の形である。

```lean
theorem flt_regular {p : ℕ} [Fact p.Prime]
    (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p
```

正則性は、円分体の整数環の類群について、`p` と類群の位数が互いに素であることとして実装されている。

### 3.2 Case I / Case II

互いに素な整数解候補へ還元した後、`p ∣ a * b * c` の真偽で分岐する。

- Case I: `¬ p ∣ a * b * c`
- Case II: `p ∣ a * b * c`

Case I では、円分一次因子が生成する ideals の積を `p` 乗 ideal として読み、pairwise coprime 性から各因子 ideal が `p` 乗であることを抽出する。その root ideal の class が `p`-torsion となり、正則性により class が trivial、したがって root ideal が principal になる。

Case II では `π = ζ_p - 1` を降下核として使い、`π` の冪指数を減少させる無限降下を構成している。

### 3.3 principalization の実装核

特に重要な補題は、概念的に次を実装している。

```text
I^p is principal
∧ gcd(p, |ClassGroup R|) = 1
→ I is principal
```

参考リポジトリでは、これが `isPrincipal_of_isPrincipal_pow_of_coprime` として実装されている。

この事実により、DkMath の旧調査で「円分体へ specialized された class-group → principalization bridge が未確認」としていた空白は、Lean で実装可能であることが確認できた。

### 3.4 unit normalization と Kummer lemma

参考実装は principal ideal equality から単に generator を取るだけではなく、単数の `p` 乗性まで扱う。

概念的には、円分整数環の単数 `u` が整数と mod `p` で合同なら、正則性を用いて `u = v^p` を得る。

その証明は Kummer extension、非分岐巡回拡大、Hilbert 94、類群位数の `p` 可除性を経由し、正則性と矛盾させる。

したがって参考実装は、円分多項式の初等的因数分解だけではなく、Kummer 理論の大域部分を正面から形式化したものである。

## 4. DkMath との関係

### 4.1 最新 `DkMath.FLT.Five` は別ルート

最新の `DkMath.FLT.Five` は、今回調査したルートとは異なる。

最新ルートの中心は、概ね次である。

```text
integer arithmetic
→ signed / residue routing
→ mod 25 obstruction
→ GoldenOrder / golden-field structure where needed
→ GN₅
→ local valuation / finite-prime escape
→ DkMath-native contradiction
```

この最新ルートは、次を証明核としていない。

```text
cyclotomic field
→ ideal class group
→ regular-prime hypothesis
→ Kummer principalization
→ Hilbert 92 / Hilbert 94 descent
```

したがって、最新 `DkMath.FLT.Five` は今回の参考実装から独立した路線として維持する。

### 4.2 旧 `DkMath.FLT` の FLT5 偽命題ルートは改善可能

過去の `DkMath.FLT` では、FLT5 の中間段に偽命題が入り、その後の Kummer / class-group bridge も abstract target や `sorry` を残したまま停止した。

今回の調査により、旧ルートが要求していた次の大域橋は、少なくとも正則素数版では Lean 実装可能と判断できる。

```text
cyclotomic factor ideal product
→ each chosen factor ideal is a p-th power
→ root ideal gives a class-group p-torsion witness
→ regularity kills p-torsion
→ root ideal is principal
→ linear factor = unit × p-th power
```

よって旧ルートは、偽命題を補強して再利用するのではなく、**偽命題を削除し、正しい Kummer principalization と Case I / Case II の降下へ置換する** ことで再生できる可能性が高い。

### 4.3 FLT5 は特に修復しやすい

`p = 5` では円分体 `ℚ(ζ₅)` の整数環が PID、したがって類数 1 であることを利用できる。

そのため一般の正則素数よりも単純に、root ideal の principal 性を回収できる。

旧 FLT5 修復では、まず `p = 5` 固定の control route を閉じ、その後に正則素数一般へ広げる順序がよい。

## 5. DkMath 側の改善実装ヒント

### 5.1 class-group target の型を修正する

現在の旧 Kummer route には、概ね次のような過強な target がある。

```lean
∀ {R} [CommRing R] [IsDomain R],
  ∀ n, ∀ a : ClassGroup R,
    a ^ n = 1 → a = 1
```

これは「任意の整域・任意の指数で全 torsion が消える」と要求しており、正則素数条件より強すぎる。

必要なのは固定した `p` と固定した円分整数環に対する次の内容である。

```lean
∀ a : ClassGroup (𝓞 (CyclotomicField p ℚ)),
  a ^ p = 1 → a = 1
```

または参考実装と同様に、次を直接仮定する。

```lean
p.Coprime
  (Fintype.card
    (ClassGroup (𝓞 (CyclotomicField p ℚ))))
```

この補正により、regular-prime receiver と実際の class-group API が正しい粒度で接続できる。

### 5.2 placeholder `True` target を段階的に実型へ戻す

旧 `CyclotomicPrincipalization.lean` では、責務分離のため多くの target が一時的に `True` となっている。

再実装では一度に全 target を置換せず、次の順序で concrete 化する。

1. cyclotomic linear-factor product equality
2. pairwise coprimality of factor ideals
3. finite-family ideal `p`-th power extraction
4. class-group `p`-torsion witness
5. regularityによる torsion annihilation
6. principal ideal extraction
7. element-level `unit × p-th power`
8. unit normalization
9. Case I contradictionまたは Case II descent

DkMath 側には、generic Dedekind arithmetic と class-group witness の補題が既に相当量あるため、参考実装の theorem statement と Mathlib API を照合し、重複実装を避ける。

### 5.3 現在の `q`-除算 descent target は別問題

旧ルートの最終 open kernel は、しばしば次の特定形を要求する。

```text
∃ z', z'^p = (x / q)^p + y^p
```

参考リポジトリの Case II が直接返すのは、通常この任意の distinguished prime `q` による整数除算 witness ではない。参考実装は `ζ - 1` の冪指数を減らす Kummer descent を行う。

したがって、次を混同しない。

- 正則素数版 FLT を contradiction として閉じること
- DkMath 独自の `q`-除算型 smaller counterexample witness を構成すること

前者は今回の参考ルートで高確率に閉じられる。後者を statement 不変のまま閉じるには追加 bridge が必要である。

実装判断は次の二択となる。

1. **Control route**: 旧 route の conclusion を正しい Kummer contradiction へ付け替える。
2. **DkMath witness route**: principalization / norm から `q`-除算型 witness へ戻す新しい bridge を別途証明する。

最初は 1 を閉じ、2 は独立研究課題として残す方が安全である。

### 5.4 control route と独自 route を明示的に分離する

推奨構成:

```text
DkMath.FLT.Five.*
  = latest independent GN / valuation route

DkMath.FLT.Kummer.*
  = classical regular-prime control route
```

両者を同一 theorem chain に混在させない。

- 最新独自ルートは参考実装の高水準 Kummer 補題に依存しない。
- 旧 Kummer route の修復では参考実装の知見を利用してよい。
- 最終的に同じ FLT5 conclusion を与えても、proof provenance を別に保つ。

### 5.5 Lean / Mathlib version 差に注意する

調査時点で、参考リポジトリは Lean `v4.32.0-rc1` 系、DkMath は Lean `v4.29.0` 系である。

そのため theorem 名や型をそのままコピーせず、DkMath の固定 toolchain における Mathlib API を再確認する。

## 6. 最新 FLT 一般化における禁止実装メモ

この節の「禁止」は、**最新 `DkMath.FLT.Five` から全素数指数へ一般化する独立本線** に対する研究上の制約である。

旧 `DkMath.FLT.Kummer` の control route 修復では使用可能である。

最新独立本線では、次の補題・証明核を import、直接呼出し、または同一構造で再実装しない。

### 6.1 参考リポジトリ側の禁止対象となる重要補題

- `flt_regular`
  - 正則素数版 FLT の完成定理そのもの。
- `isPrincipal_of_isPrincipal_pow_of_coprime`
  - class-group order と `p` の coprimality による principalization。
- `is_principal_aux`
- `is_principal`
- `exists_ideal`
  - cyclotomic factor ideal の `p` 乗性から `unit × p-th power` へ進む Case I の主要鎖。
- `exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`
- `eq_pow_prime_of_unit_of_congruent`
  - Kummer extension、非分岐拡大、class-number divisibility を使う unit の `p` 乗化。
- `caseI_easier`
- `caseI`
  - class-group principalizationを核とする第一場合の矛盾。
- `exists_solution`
- `exists_solution'`
- `not_exists_solution`
- `not_exists_solution'`
- `caseII`
  - `ζ - 1` の指数降下による第二場合。
- Hilbert 94 / unramified cyclic extension から class-group order の `p` 可除性を得る経路。

### 6.2 禁止するのは高水準アーキテクチャである

次のような一般 Mathlib 補題や普遍的代数恒等式まで禁止しない。

- `geom_sum₂_mul`
- `Ideal.span_singleton_pow`
- 一般の gcd / divisibility / valuation API
- 一般の primitive root / cyclotomic polynomial definitions
- 一般の Dedekind domain APIを、独自ルートの補助検査に使うこと

ただし、それらを組み合わせて次の同一 Kummer 経路を再現した場合は、独立本線とは数えない。

```text
cyclotomic ideals
→ class group p-torsion
→ regularity
→ principalization
→ Kummer descent
```

独立性は theorem 名ではなく、証明の依存構造で判定する。

## 7. 参考実装への謝辞と provenance 方針

旧 Kummer / FLT5 control route の改善が完了した場合、参考リポジトリの調査から解決の手掛かりを得たことを、実装コードの module comment と関連ドキュメントに URL 付きで明記する。

推奨コメント例:

```lean
/-!
## Implementation provenance

This regular-prime / Kummer control route was completed after studying:

https://github.com/leanprover-community/flt-regular

Pinned investigation commit:
https://github.com/leanprover-community/flt-regular/commit/a859475b163864437e430f8442da7ac29a4bf109

The implementation in this module is adapted to DkMath's local theorem APIs.
It is a classical Kummer control route and is not part of the independent
`DkMath.FLT.Five` GN / valuation proof route.
-/
```

より直接的に特定補題の構造を参考にした場合は、関連する source file と theorem 名も記す。

### 7.1 ライセンス上の注意

参考リポジトリは Apache License 2.0 である。

- 原則としてコードを逐語的にコピーせず、数学的アイデアと theorem boundary を理解した上で DkMath API に合わせて再実装する。
- コードを直接移植する場合は、Apache-2.0 の notice / attribution 要件を別途確認し、必要な表示を保持する。
- URL 付き謝辞は、ライセンス対応とは別に研究 provenance として必ず残す。

## 8. 実装計画案

### Phase 0: 現状固定

- 最新 `DkMath.FLT.Five` の依存グラフを保存する。
- Kummer / class-group import が独立本線へ混入していないことを確認する。
- 旧偽命題 route の theorem 名、使用箇所、`sorryAx` 伝播を一覧化する。

### Phase 1: `p = 5` control route

- `ℚ(ζ₅)` の ring of integers / PID / class number one APIを確認する。
- old FLT5 の偽命題を削除する。
- correct cyclotomic ideal factorization と principalization を構成する。
- Case I / Case II のどちらで閉じるかを明示する。
- `#print axioms` により `sorryAx` がないことを確認する。

### Phase 2: regular-prime generalization

- class-group target を固定 `p` / 固定 cyclotomic ring に修正する。
- `p.Coprime (Fintype.card (ClassGroup ...))` から torsion annihilation を構成する。
- generic Dedekind bridge と cyclotomic specialization を接続する。

### Phase 3: DkMath独自 descent bridge の再評価

- `q`-除算 witness target を維持する数学的必然性を再評価する。
- Kummerの `ζ - 1` descent と同値・包含関係があるか調査する。
- 同値でなければ、control route と独自 witness route を別 theorem として残す。

### Phase 4: 検証

- `lake build`
- 対象 module 単体 build
- `#print axioms`
- no-sorry test / sorry test の更新
- 最新 `DkMath.FLT.Five` の依存非混入確認
- provenance comment と本ドキュメントへのリンク確認

## 9. 完了条件

旧 route の改善完了は、単に最終 theorem が `False.elim` で閉じたことではなく、次を満たした時点とする。

1. 旧偽命題が theorem chain から除去されている。
2. 正しい正則素数または `p = 5` の仮定が型に現れている。
3. principalization / unit normalization / descent の責務が明示されている。
4. `sorryAx` がない。
5. 最新 `DkMath.FLT.Five` の独立性が保たれている。
6. 参考リポジトリへの URL 付き謝辞がコードコメントに記載されている。
7. 直接移植を行った場合は Apache-2.0 の要件を満たしている。

## 10. 最終整理

- 最新 `DkMath.FLT.Five` は、今回参考にした Kummer・円分体・class-group ルートとは異なる。
- 最新 FLT 一般化では、参考実装の主要 Kummer 補題と同一アーキテクチャを流用しない。
- 旧 `DkMath.FLT` の FLT5 偽命題ルートは、参考実装で確認できた正しい principalization と Kummer descent により改善できる可能性が高い。
- 旧 route の改善は、DkMath独自証明の置換ではなく、古典 Kummer control route の再生として位置付ける。
- 改善完了時には、参考リポジトリから解決のヒントを得たことを URL 付きで明記する。
