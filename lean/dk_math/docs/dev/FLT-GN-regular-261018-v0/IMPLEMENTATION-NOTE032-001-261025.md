# NOTE-032-001 — 枝交換によるhno排除の一般核とSource接続

2026-10-25。開始時のbranchは `dev/FLT-GN-regular-261018-v0`、作業ツリーはcleanだった。
`lib/FLT-GN-Completion-261023-v0` がHEADの祖先であることを確認した。
今回追加したのは本体14定理・1定義と、条件付きのFrey入口である。無条件のhnoは未証明である。

## 1. 模範解答をどう読んだか

参照はAnthropicの固定コミット `6e837e75355538c7f80bab5b956861e86c4eacc2`。
全体のコードや独自インフラを取り込まず、次の4証明を読んだ。

| 参考証明 | 確認した役割 |
| --- | --- |
| [frey_no_cofixed_of_a_mod_eight](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_of_a_mod_eight.lean) | 零成分・吸収・非自明慣性・枝交換の最終組立て |
| [not_exists_cofixed_line_of_inertia_and_branch_swap](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap.lean) | 共通変化量と商での+1/−1の矛盾 |
| [frey_exists_inertia_not_fixed_at_two](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_exists_inertia_not_fixed_at_two.lean) | 捩れ点の深さから、有限拡大・分岐と慣性の持上げを経て非自明作用を作る |
| [frey_exists_decomposition_branch_swap_of_a_mod_eight](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean) | 2上の中心・枝・Frobenius作用を合同条件へ接続する |

取得内容のSHA256、git blob、行数は [機械可読記録](evidence/note032-001.json) に保存した。
参考ファイルそのものは検証用の一時資料とし、P2M.Util等をDkMathへimportしていない。
一般核のヘッダには参照由来とApache-2.0の案内を残した。

小指数を既存FLTで排除する経路や、大指数のMazurの最終証明は今回の実装には使っていない。
模範解答にある定理名を新しい仮定のクラスとして置いて、hnoを証明済みに見せる実装にもしていない。

## 2. DkMath流に短縮できた線形代数

[CofixedBranchSwap.lean](../../../DkMath/Lib/RepresentationTheory/CofixedBranchSwap.lean) に7定理を実装した。
入力は同じ表現ρ、局所群I、真部分空間M、非零の2、局所の吸収と非自明変化量、枝交換元である。

Cofixed直線Lを仮定すると、非自明な変化量d=ρ(τ)x−xはL∩Mの非零元になる。
Lの一次元性からL≤Mが従う。ここでL=Mまで証明する必要はない。
従って周囲の次元2、有限体の位数p²、Mの次元や安定性を一般核へ要求しない。
有限次元空間であることと、候補Lの次元1は保持する。

Mの外側の点yを選ぶ。枝交換とCofixedから

```text
ρ(σ)y+y ∈ M
ρ(σ)y−y ∈ L ≤ M
```

となり、差を取って2y∈M。2≠0の体上ではy∈Mとなって矛盾する。
`no_stable_cofixed_line` は既存hnoの型へ接続し、
`inertia_fixed_of_cofixed_and_branch_swap` は逆に、Cofixed直線が残れば局所作用が自明になると結論する。
慣性非自明性の実証明が必要であることを、この条件付き定理でも確認できる。

## 3. 実際の零成分を構成した

[FreyCofixedBranchSwap.lean](../../../DkMath/FLT/FreyCofixedBranchSwap.lean) に1定義・7定理を追加した。
`residualZeroComponent A` は同じSourceのE[p]のうち、同じ整数モデルで滑らかに還元する点の部分加群である。
加法・逆元の閉性は031-004の幾何を再利用し、実点からZMod部分加群へ構成した。

ここで使うE₀[p]は、031-004の `residualReductionKernel` が表すE₁[p]と異なる。
滑らかな零成分上の点を全て無限遠へ還元すると見なしていない。
`residualZeroComponent_ne_top_iff` は、真性に必要な実際の零成分外のp捩れ点を明示する。
その存在を今回の定義だけから得たとは主張しない。

同じ曲線の臨界中心C・接線方向Dがあり、局所慣性が中心を固定するなら、
`EllipticNodalInertia.inertia_difference_smooth` からE₀[p]への吸収を供給した。
これは座標での滑らかな還元と、同じ残余表現上の差を結ぶ実際の接続である。

## 4. hno・既約性へ接続した範囲

`residual_no_cofixed_line_of_inertia_and_branch_swap` は、p≠2の同じSourceについて
Mの真性・吸収・非自明慣性・枝交換を受け取り、hnoを結論する。
`residual_no_cofixed_line_of_zeroComponent_branch_swap` は実際のE₀[p]へ特殊化し、
中心固定からの吸収を内部で供給する。

`residual_isIrreducible_of_inertia_and_branch_swap` はp≥5、Even S.bの下で031-005へ接続する。
有理torsion排除とFixed/Cofixed大域二択は既存証明を使うが、残る幾何入力を取り除いてはいない。
指数37のスモークでも同じSourceとMを保持してこれらの型を確認した。Source37の存在は構成していない。

`a_mod_eight_cases_of_oriented` は4∣S.a+1からa mod8が3または7であることを証明する。
3側を選ぶ根拠や、合同条件から枝交換元が存在する証明は今回供給していない。

## 5. 境界を有限表現で確認した

[境界のLean資料](evidence/Note032BranchSwapBoundary.lean) は、登録した通常テストと同じ検証本体である。
せん断表現ρ(t)(x,y)=(x+ty,y)と、第二射影の核を実際に構成した。

- 標数2では吸収・非自明作用・枝交換・Cofixed直線の存在が全て成立する。2≠0は必須である。
- 標数3ではCofixed直線と非自明な吸収は成立するが、枝交換は成立しない。
  これにより一般のCofixed直線を自動的に否定していないことを確認した。
- M=⊤なら枝交換条件が空虚に成立する。Mの真性は省略できない。
- mod4の合同条件だけではmod8の7側も残る。例は整数の合同条件の反例であり、Frey Sourceの存在例ではない。

## 6. 検証と公開

`DkMath.Lib`、`DkMath.FLT`、通常テスト入口へ登録した。
次の対象ビルドが成功した（4031 jobs、警告0）。

```text
lake build DkMath.Lib.RepresentationTheory.CofixedBranchSwap DkMath.FLT.FreyCofixedBranchSwap
```

[Sourceスモーク](evidence/Note032Smoke.lean) の4定理と境界の14宣言を独立にLeanで確認した。
新しい本体15宣言・境界14宣言・Sourceスモーク4定理、合計33宣言の公理は標準論理公理のみだった。
既存の中心的な9所有者を変更していないこと、元NOTE-032の不変性、マーカー、禁止構文、
Libの依存方向、JSON、文書リンク、`git diff --check` を確認した。
詳細は [機械可読記録](evidence/note032-001.json) と [検証記録](evidence/validation-note032-001.txt)。
フルビルド・集約入口・DkMathTest・lake testのビルドは、ユーザー指定により実施していない。
通常テストの登録は静的確認であり、独立境界ファイルでその本体を検証した。

## 7. 次に供給する算術

[NOTE-032のROADMAP](ROADMAP-NOTE032.md) に分割した。

1. 同じ2上のモデルにおける臨界中心・接線方向と中心の慣性固定。
2. 同じE[p]の零成分外の点の存在。
3. 判別式深さからの非自明慣性作用。`not_exponent_dvd_two_valuation` の算術は既にあるが、その先の分岐の橋が必要。
4. a≡3 mod8から、同じMの外側を商で符号反転させる分解群元の存在。

この四点を供給して初めて3側のhnoを幾何入力なしで閉じられる。
7側と一般のhnoは別の課題であり、既約性の完成も一般FLTの完成とは区別する。
GN-LIB-007の構成は制御集合ごとに座標が変わるため、そのまま既存のFrey Sourceへ代入できるとはしていない。
