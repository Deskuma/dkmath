# NOTE-032-003C — 非分裂接錐のFrobeniusと3側の枝交換

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `5f8435e34037694399ee3358d455548b25c050ea`、作業ツリーはcleanだった。
本体18定理を追加した。003Cの枝交換を供給し、032-004の直接hnoと既約性にも
同じ2上の住所で接続した。Source・素数p≥5・a≡3 mod8・2上の住所を保持する。
中心・方向・外側の点・非自明慣性・枝交換のproviderは新しい終点の引数に残っていない。

## 1. 到達点と境界

| 層 | 証明した内容 | 保持する条件 |
| --- | --- | --- |
| 整数算術 | bⁿ−aⁿ−1≡4 mod8、整数a₂は奇数 | a≡3 mod8、b偶数、奇数n≥3 |
| 剰余二次式 | z²+z=1ならz²−z=1、2乗作用で非固定 | 標数2、与えた根z |
| 付値の輸送 | v(σz−z)=1 | 同じ付値環の実際の2乗Frobenius |
| 接線方向 | σα=β、σβ=α | 同じ中心・方向、剰余a₁=a₂=1、剰余x₀=0 |
| 浅い点の和 | σP+Pは滑らかに還元する | 同じモデル、零成分外の浅い点 |
| 同じFrey Source | 全ての外側のp捩れ点で枝交換 | 素数p≥5、a≡3 mod8、2上の住所 |
| 直接hno・既約性 | 安定Cofixed直線が存在せず、同じ残余表現は既約 | 同じSourceと上記の条件 |

一般hno、a≡7 mod8側、一般FLTの完了は主張しない。
新しい直接hnoは指定した任意の2上の住所で成立するが、その住所自体の存在を
内部供給する公開入口は今回追加していない。032-004ではその包装を次の単位とする。
E₀[p]とE₁[p]の既存の定義は変更していない。

## 2. mod8から接錐へ

[FreyModEight.lean](../../../DkMath/Lib/NumberTheory/FreyModEight.lean) に一般算術2定理を実装した。
ZMod 8では3²=1なので3の奇数乗は3である。偶数bの3乗以上の冪は零となる。
従ってbⁿ−aⁿ−1の剰余は4になる。整数除算の商と余りを保持して

```text
bⁿ−aⁿ−1 = 8k+4
a₂ = (bⁿ−aⁿ−1)/4 = 2k+1
```

を導く。冪和方程式、原始性、素数性はこの一般定理の入力に不要である。
指数37を展開する方式ではなく、奇数乗と冪の加法則を使うので指数に依存した巨大展開を避ける。

[FreyDyadicBranchSwap.lean](../../../DkMath/FLT/FreyDyadicBranchSwap.lean) のSource側では、
正規化の16∣aᵖbᵖとaの奇数性からb偶数を内部供給する。
既存の同じ整数曲線・同じ付値モデルに一般算術を適用し、剰余a₂=1へ運ぶ。

中心の剰余X座標の零性には短い経路が使えた。
a₁=1、a₃=0であるため中心のY偏微分の等式は2y₀+x₀=0となる。
y₀は整で2は非単元なのでx₀も非単元である。
中心を新しく選び直したり、二次式の根を再構成したりする必要はない。

## 3. Frobeniusが方向を交換する理由

[ValuationQuadraticFrobenius.lean](../../../DkMath/Lib/NumberTheory/ValuationQuadraticFrobenius.lean)
の3定理は、標数2の二次式と実際の付値環のFrobeniusを分離した。
z²+z=1なら2z=0よりz²−z=1なので、z²≠zである。
整元zに実際の2乗Frobenius元σを作用させると

```text
res(σz−z) = res(z)²−res(z) = 1
v(σz−z) = 1
```

となる。これは非自明な剰余作用を使う段階であり、慣性による剰余固定とは異なる。
剰余体がF₂そのものであるとは仮定しない。

[EllipticFrobeniusBranchSwap.lean](../../../DkMath/Lib/NumberTheory/EllipticFrobeniusBranchSwap.lean)
に5定理を実装した。接錐の二次式

```text
z²+a₁z−(a₂+3x₀)
```

を同じモデルの剰余へ写すとz²+z−1となる。
003Aによって中心は分解群固定なので、σαもα,βと同じ二次式の根である。
Frobeniusの変化量が単元であるためσα≠αとなる。
同じ二根による因数分解からσα=βを得て、根の和からσβ=αも得る。
剰余上の根の交換から、実際の方向の等号まで供給した。

## 4. 方向の交換から同じ点の和へ

方向が交換されるという結論だけで、点群上の枝交換と同一視していない。
外側の同じp捩れ点P=(x,y)について、既存の実際の倍点軌道の定理から

```text
v(defect(C)) < v(x−x₀)²
```

という厳密な浅さを得る。浅さから中心傾きλ=(y−y₀)/(x−x₀)は整であり、
その接錐二次式の値は非単元となる。従って剰余λもλ²+λ=1を満たし、
v(σλ−λ)=1となる。

中心の分解群固定と付値保存により、PとσPは中心からの深さが同じである。
両点の傾きの差は単元なので、既存の同深さ・異なる枝の加法定理を適用できる。
その結論が、実際の加法でのσP+Pの滑らかな還元である。

`residual_frobenius_branch_swap_of_a_mod_eight` は任意の実際の2乗Frobenius元でこの結論を供給する。
`residual_exists_decomposition_branch_swap_of_a_mod_eight` は既存のFrobenius存在定理で
その元を構成し、分解群所属も保持する。
同じSourceの実際のE[p]と残余表現をそのまま使い、仮の二次元表現へ置き換えていない。

## 5. 直接hnoと既約性

003Bの非自明慣性・零成分外の点の存在と、今回の枝交換を既存の排除核へ渡した。

```text
residual_no_cofixed_line_of_a_mod_eight_at_two
residual_isIrreducible_of_a_mod_eight_at_two
```

が新しい終点である。前者の幾何providerは内部で全て供給される。
後者は031-005の既存の同じSourceの向き付け済み分類へ接続し、b偶数も内部供給する。
一般FLTや既存FLTによるSourceの空虚な排除はこの経路に使用していない。

032-004の局所直接hnoはここで接続できた。
次の公開入口では2上の住所の存在を内部供給してA,hAを除き、合同条件を保った終点を整理する。
3側を終えたことから7側の排除を推測して定理にしていない。

## 6. 模範解答との対応とDkMathでの再構成

参照した模範解答は、固定commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` の
`P2M/Sol/S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean`。
032-001で取得した同じローカル資料を読み、SHA-256とGit blobを照合した。
参照記録は [001 evidence](evidence/note032-001.json) と今回の [evidence](evidence/note032-003c.json) にある。
派生コードの本体4ファイルにはApache-2.0の出典・変更説明を保持した。

模範解答の合同算術→浅い傾き→Frobenius→異なる枝の和という証明を、
DkMathでは一般算術、一般付値体の剰余作用、同じ中心の局所幾何、Source consumerへ分割した。
中心固定は003Aの所有定理を使い、中心X座標の小ささはY偏微分から短く供給した。
Libの公開10定理に `[DkMath.Lib]` を付し、LibはLibの所有モジュールだけをimportする。

## 7. 境界例と検証

[独立境界資料](evidence/Note032FrobeniusBranchSwapBoundary.lean) は、登録した通常テストと同じ本体である。

- 指数37、a=−5、b=2で、一般のmod8算術とa₂奇数性を適用した。
- a=7、b=2、指数3ではa≡3 mod4でもa₂=−84は偶数。mod4から3側を選べない。
- 指数1では分子の剰余は6となり、奇数という条件だけでは不足する。
- 分裂式z²+z=0の根0は2乗作用で固定される。定数項の条件を除けない。
- 実際の曲線y²+xy=x³+x²+2x（Δ=−412,c₄=−71）で中心・方向・Frobeniusを構成し、方向交換を証明した。
  実際の3捩れ9個と滑らかな捩れの上界3から外側の点を構成し、同じ点でσP+Pの滑らかな還元まで確認した。
  Frey Sourceの存在仮定を使わない具体的幾何の例である。

[Sourceスモーク](evidence/Note032FrobeniusBranchSwapSmoke.lean) の4定理では、指数37の同じSourceについて
方向交換、全ての外側の点の枝交換、直接hno、既約性を幾何providerなしで確認した。
Source37の存在は主張しない。

`lake build DkMath.FLT.FreyDyadicBranchSwap` が通過した（4044 jobs、警告0）。
依存する新規Lib3モジュールもこの対象ビルドに含まれる。
独立境界6定理・1定義、Sourceスモーク4定理が通過した。
本体18定理と合わせた29宣言の `#print axioms` は、
`propext`、`Classical.choice`、`Quot.sound` の範囲内だった。
禁止構文、マーカー、Lib依存方向、既存所有者の不変性、登録、文書リンク、差分空白を確認した。
詳細は [検証記録](evidence/validation-note032-003c.txt) と [機械可読記録](evidence/note032-003c.json)。
通常テスト・Lib・FLTの集約入口は静的に登録確認し、テストの同一本体は独立資料としてLeanで検証した。
フルビルド、集約ルート、DkMathTest、lake testのビルドはユーザー側の検証分担とした。
