# History of GN / G / GC Naming and Refactor Plan

## Log

### 日時: 2026/03/26 JST

1. 目的:
   - `GN` / `G` / `Gn` / 将来の `GC` の命名・配置の衝突を、
     現在ワークスペースでどう抱えているかを棚卸しする。
   - `高次 Tail 構造による一般化 GN 多項式` と
     `G 構造から D-加群へ` の未来設計を踏まえ、
     どこから refactor すべきかを明確にする。

2. 調査対象:
   - `[docs/not_implements/高次 Tail 構造による一般化 GN 多項式の定義.md]`
   - `[docs/not_implements/G構造からD-加群へ.md]`
   - `[lean/dk_math/DkMath/CosmicFormula/Defs.lean]`
   - `[lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean]`
   - `[lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean]`
   - `rg` による `GN` / `Gn` / `G` / `Gamma` 系の横断検索

3. 事実確認:
   - `Defs.lean` には
     - `G (R) (x u) d`
     - `Gn (R) (x u) d n`
     - `Big / Body / Gap`（ただし `ℝ` 固定）
     がある。
   - しかし `Defs.lean` の `Body` は `G ℝ x u d` そのものであり、
     後続 mainline の
     `Body = x * GN`
     あるいは
     `Body = x * G`
     とは意味が一致していない。
   - `CosmicFormulaBinom.lean` には
     - `CommRing` 側 `G`
     - `CommSemiring` 側 `GN`
     - `Big / Gap / Body`
     があり、
     downstream 実装は主にこちらを参照している。
   - `NumberTheory/Gcd/GN.lean` や
     FLT / Zsigmondy / PrimitiveBeam 周辺は、
     既に `DkMath.CosmicFormulaBinom.GN` を正規 API として使っている。
   - 文書側では
     - `GN` は差冪 `(x+u)^d - u^d = x * GN`
     - `G` は Body `(x+u)^d - x^d = u * G`
     - `Γ_{d-1}(x,u)` は `G` 構造の別記法
     という 3 層が併存している。
   - `GC` は現状コード未実装で、
     複素版計画書・複素半宇宙式メモなど将来設計にのみ現れる。

4. 調査結論:
   - mainline の事実上の中心は `CosmicFormulaBinom.GN` であり、
     `Defs.lean` の `Gn` は名前が近いのに下流からほぼ使われていない。
   - `Defs.lean` は
     - 型が `ℝ` 固定の定義を持つ
     - `Body` の意味が mainline とずれる
     - `G / Gn` の命名が `CosmicFormulaBinom.G / GN` と競合する
     ため、
     現状では refactor の起点候補になっている。
   - 文書設計としては
     - `GN = standard tail (r = 1)`
     - `GZ <- G`（Body 正規化側）
     - `GC` 新設（複素化）
     という成長図が見えている。
   - したがって refactor の本筋は
     「`Gn` を一般 tail 構造へ昇格させ、
      `GN` / `G` / `GC` を同じ family の specializations として並べ直す」
     方向になる。

5. 現時点の見立て:
   - まず canonical family を 1 つ決める必要がある。
   - 最有力は
     `GNtail d r x u` あるいは `GNGen d r x u`
     のような一般 tail 定義を本体にして、
     - `GN d x u := GNtail d 1 x u`
     - `Big d x u := GNtail d 0 x u`
     - `tailTop d x u := GNtail d d x u = 1`
     を派生化する構成。
   - その上で
     `G` 側は変数役割の swap / Body 正規化 specialization として再定義し、
     `Γ` は notation / doc alias に留めるのが自然に見える。
   - `Defs.lean` は最終的に
     旧名 alias 層へ縮退するか、
     役割を失う可能性が高い。

6. refactor 候補の優先順位:
   - 第1段:
     `CosmicFormulaBinom` に一般 tail family を新設し、
     `GN` をその `r = 1` specialized notation に落とす。
   - 第2段:
     `Defs.lean` の `Gn` と `Body` を、
     mainline と整合する alias / wrapper へ置き換えるか、
     旧実験層として隔離する。
   - 第3段:
     `G` 構造文書で言う `G_{d-1}` / `Γ_{d-1}` を、
     Lean 上では
     `Body`-normalization family として formalize する。
   - 第4段:
     複素版 `GC` を、
     既存 `GN` / `G` family の scalar extension として設計する。

7. 当面の実装方針:
   - いきなり全体 rename はしない。
   - 先に tool 定理補題として
     一般 tail family の定義・基本恒等式・special cases
     を下層へ実装し、
     そのあと `GN` / `G` / `Defs.Gn` の接続を整理する。
   - 理由:
     下流（FLT / NumberTheory / Zsigmondy）が既に `CosmicFormulaBinom.GN`
     を多数参照しているため、
     先に refactor だけ進めると破壊範囲が大きい。

8. 次の課題:
   - `GN` family の canonical placement を
     `CosmicFormulaBinom` に置くか、
     `CosmicFormula/Defs` を整理して移すかを決める。
   - 一般 tail family の仮名
     `GNtail` / `GNGen` / `GSeries`
     を比較し、命名を確定する。
   - `Defs.lean` の `Gn` を、
     実際に残すべき alias なのか
     置換対象なのかを次段で判断する。
