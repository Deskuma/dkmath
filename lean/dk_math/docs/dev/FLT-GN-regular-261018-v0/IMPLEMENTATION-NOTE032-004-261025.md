# NOTE-032-004 — 住所を内部供給した3側の直接hno・既約性

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `d21c835157c6df441b552145285e652b387fca87`、作業ツリーはcleanだった。
本体7定理を追加した。032-003Cの局所終点へ2上の住所の存在を内部供給し、
同じSource・素数p≥5・a≡3 mod8だけを引数に取る直接hno・既約性の入口を構成した。
032-004を完了とする。a≡7 mod8と一般hnoは032-005の研究課題として残る。

## 1. 公開する数学

| 所有モジュール | 追加内容 | 仮定 |
| --- | --- | --- |
| ValuationPrimeExistence | 指定した素数上の付値環の存在 | 任意の標数0の体、素数q |
| FreyModEightIrreducibility | 住所とFrobenius枝交換の同時存在 | 同じSource、素数p≥5、a≡3 mod8 |
| 同上 | 直接hno、既約性、全安定直線の不存在 | 同上。住所・幾何providerなし |
| 同上 | 可約ならa≡7 mod8 | 同じSource、素数p≥5、mod4の向き付け、可約性 |
| 同上 | 整数反例の同じSourceは既約または7側 | 非零整数反例、原始化・符号付き置換の証拠を保持 |

素数性、p≥5、3側の合同条件は取り除いていない。
新しい直接hnoは一般FLTによるSourceの空虚な排除を使わず、
032-001〜003Cで証明した同じ曲線・点群・零成分の算術を合成している。
正則性や類群の仮定を追加していない。

## 2. 有限素点の住所はどこから来るか

[ValuationPrimeExistence.lean](../../../DkMath/Lib/NumberTheory/ValuationPrimeExistence.lean)
に一般定理 `exists_liesOverPrime` を実装し、教科書docstringに `[DkMath.Lib]` を付した。
ここでLは任意の標数0の体でよく、有理数の代数閉包へ限定していない。

```text
O = integralClosure ℤ L
P = (q) ⊆ ℤ
Q ⊆ O, Qは極大、QはP上
A ⊆ L, O⊆A, Qの像⊆A.nonunits
```

qの素数性からPは極大イデアルである。
Oはℤ上整であり、標数0からℤの埋込みは単射なので、Mathlibのlying-over定理
`Ideal.exists_maximal_ideal_liesOver_of_isIntegral` を適用できる。
同じ整数qのQへの所属を `Ideal.mem_of_liesOver` で運ぶ。

次に `Ideal.image_subset_nonunits_valuationSubring` をQへ適用する。
Qが真のイデアルであることから、その像を非単元へ送る付値環Aが存在する。
従って指定した同じqがAの非単元となり、`LiesOverPrime A q` を得る。
値群を実数や整数に同一視せず、離散性・完備性・Lの代数性も使わない。

この証明は付値環の存在だけを供給する。
Frobeniusの構成は有理数の代数閉包上の既存の所有定理へ渡す。
任意の標数0の体でFrobenius元まで存在すると結論を拡張していない。

## 3. 同じSourceの公開終点

[FreyModEightIrreducibility.lean](../../../DkMath/FLT/FreyModEightIrreducibility.lean)
に6定理を実装した。

`residual_exists_dyadic_frobenius_branch_swap_of_a_mod_eight` は
新しい存在定理から2上のAを取り、既存のFrobenius存在定理からσを取る。
003Cへその同じA,σを渡すため、住所・Frobenius所属・全ての外側の同じ点の枝交換が
一つの存在命題にそろう。

```text
P ∉ E₀[p]  →  ρ(σ)P+P ∈ E₀[p]
```

`residual_no_cofixed_line_of_a_mod_eight` は2上のAの存在を内部供給し、
003Cの住所付きhnoへ渡す。公開引数には中心・方向・外側の点・非自明慣性・枝交換・住所が残っていない。
032の排除核の理由は、非自明な慣性変化量がCofixed直線とE₀[p]の共通非零元となることである。
この直線がE₀[p]に含まれると、外側の点の商上ではCofixed性の+1と枝交換の−1が矛盾する。

`residual_isIrreducible_of_a_mod_eight` はこのhnoを031-005の大域分類へ渡す。
b偶数は003Cの正規化算術から供給する。
`residual_no_stable_line_of_a_mod_eight` は既存の同じ次元2の表現の判定基準で
全安定直線の不存在へ言い換える。仮の二次元表現への置き換えは行わない。
E₀[p]とE₁[p]の定義も変更していない。

## 4. 7側に何が残るか

`residual_a_mod_eight_eq_seven_of_not_irreducible` は

```text
4 ∣ a+1, ¬ ResidualIsIrreducible  →  a % 8 = 7
```

を証明する。既存のmod8二択の3側では新しい既約性と矛盾し、7側だけが残る。
これは可約性を仮定した絞込みであり、逆向き「7側なら可約」は証明していない。
7側のSourceが存在することも、この定理からは従わない。

`ofCounterexample_residual_irreducible_or_seven` では、
非零整数反例から既存の `Source.ofCounterexample` が選んだ同じSourceを扱う。
結論にはmod4の向き付けとb偶数に加えて

```text
∃ R : PrimitiveReduction p a b c,
  OrientationTrace R.A R.B R.C S.a S.b S.c
```

を保持する。PrimitiveReductionは元の整数座標と共通因子の等式を記録する。
その同じSourceで「既約、またはa≡7 mod8」を得る。
原始化後の座標を元の反例の座標と同一視せず、符号や置換の証拠も捨てない。

## 5. 境界例と独立スモーク

[独立境界資料](evidence/Note032PrimeExistenceBoundary.lean) は通常テストと同じ本体である。

- 超越拡大ℚ(X)に37上の住所が存在し、その実際の剰余体は標数37となる。
  有限拡大・代数的拡大を要求しない一般性を確認した。
- Frey Sourceなしに、ℚの代数閉包上の2上の住所と実際のFrobeniusを同時に構成した。
- 1は付値環の単元なので住所にならない。自然数を無条件に入力できるとはしていない。
- 2と3を同時に非単元とする付値環は存在しない。住所の選択は素数に依存する。
- 標数2の体ZMod 2では3=1となり、3上の住所が存在しない。
  任意の素数についての存在定理から標数0の仮定を落とせない。

[指数37のスモーク](evidence/Note032ModEightIrreducibilitySmoke.lean) では4定理を確認した。
住所と枝交換元の同時存在、住所なしのhno・既約性・安定直線排除、
可約性からの7側への絞込み、共通因子・向き付けの証拠を持つ整数反例の入口である。
Source37や整数反例の存在を構成したとは主張しない。

## 6. 検証と次の研究境界

対象ビルドが通過した（4046 jobs、警告0）。

```text
lake build DkMath.Lib.NumberTheory.ValuationPrimeExistence \
  DkMath.FLT.FreyModEightIrreducibility
```

境界5定理、指数37のスモーク4定理が通過した。
本体7定理と合わせた16宣言の `#print axioms` は、
`propext`、`Classical.choice`、`Quot.sound` の範囲内だった。
新規コードの禁止構文・マーカー・docstring、Libの依存方向、既存所有者の不変性、
入口登録、文書リンク、差分空白を確認した。
詳細は [検証記録](evidence/validation-note032-004.txt) と [機械可読記録](evidence/note032-004.json)。
通常テストの同一本体を独立資料でLean検証し、集約入口の登録は静的に確認した。
フルビルド・集約ルート・DkMathTest・lake testのビルドはユーザー側の検証分担とした。

今回はMathlibのlying-over・付値環存在の所有定理とDkMathの既存局所証明を組み合わせた。
模範解答の3側hnoとの対応は [003C報告](IMPLEMENTATION-NOTE032-003C-261025.md) と
[001参照記録](evidence/note032-001.json) に残してある。

次は032-005である。a≡7 mod8では003Cの非分裂接錐の剰余式が得られず、
今回のFrobeniusによる枝交換をそのまま適用できない。
一般hnoへ進むには、この条件を実証明された算術へ置き換える別の研究が必要である。
GNの恒等式・向き付け・既存の3側既約性だけで7側を排除したとはしない。
