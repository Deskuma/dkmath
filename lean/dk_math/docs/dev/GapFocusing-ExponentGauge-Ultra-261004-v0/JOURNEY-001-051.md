# 旅の記録 — Gap Focusing / Exponent Gauge Ultra (001–051)

研究期間：2026-10-04 〜 2026-10-08  
Branch: research/GapFocusing-ExponentGauge-Ultra-261004-v0  
統合先：develop

> 証明できたものを Core に残す。成立しなかった橋を Gap として残す。
> この PR は未解決予想の解決宣言ではなく、Lean が検証した道と引き返した道の合流記録じゃ。

## 序章 — 冪の差に「幅」を戻す

出発時の問いは、一般の冪差を a=x+u, b=u と焦点化し、

    (x+u)^d - u^d = x * GN_d(x,u)

とするとき、単なる置換を超える構造が見えるか、であった。
既存 FLT3/5/7 の residual unit gauge を、GN・円分因子・素因子住所という
さらに原始的な層から理解しようとした。

[001](report-001.md) は、固定基点での商と定数 defect の一意性、
GN の非自明位相積、整数・有理係数における
「GN kernel が既約 iff 次数が素数」を証明した。
[002](report-002.md) は指数 successor と unit gauge が異なる層であることを確認。
[003](report-003.md) は斉次円分層の素数住所を乗法位数と素数冪次数で分類した。
ただし GN support と FLT の単数冪剰余類の間の算術写像は未構成。

## 第一幕 — 平方殻に素数の席を探す（004–024）

問題はルジャンドル予想の平方殻へ移った。有限座席、素数 support、
被覆、衝突、未被覆を厳密な集合として持ち運ぶ旅である。

[004](report-004.md)–[007](report-007.md) では周期と fresh incidence cost、
候補の奇偶による 2q 周期、finite block の独立容量上界を証明した。
shell 21 に関する素数の有限結果も得た。一方、fresh cost を
二重課金して矛盾とする筋道は止められた。

[008](report-008.md)–[012](report-012.md) は二素数の inclusion–exclusion、
局所 certificate、混合 CRT、quotient-root fiber と head/tail cancellation。
shell 29、41、91、さらに複数のアンカーで有限素数の存在を確認したが、
固定 prime basis が全 n の需要を満たすとは証明できなかった。
重複 witness の素朴な足し算も正しくないと判明した。

[013](report-013.md)–[016](report-016.md) は sqrt-rough support の
pair/triple moments、zero/singleton/double/triple census、
quotient owner routing と square-anchor counterexample packet へ。
必要な rejection correction を省略した保存則は誤りであり、
補正付きの正確な保存則へ修正した。n=1031 の有限 endpoint も形式化。

[017](report-017.md)–[024](report-024.md) は centered quadratic fold、
隣接殻の gcd、primorial town、full-period column、packing と deletion
conservation、symmetric retained direction、terminal prime products。
正確な支持容量があっても、最後の未被覆席を全 n で強制するとは限らない。
保存則自身が、一部の strictness 主張を不可能と判定した。

獲得物は有限集合・CRT・prime ownership・support collision の
形式化 calculus。未獲得物はルジャンドル予想の一様な証明。

## 第二幕 — Pascal、von Mangoldt、平方グノモン（025–042）

[025](report-025.md) は Pascal prebirth alternation と二項係数の
共通可除性を正の素数冪へ分類。[026](report-026.md)–[027](report-027.md)
は shell の von Mangoldt mass と高次素数冪 correction の独立 budget。
[028](report-028.md) は除数 incidence と階乗積から exact log ledger
を作った。近似や PNT/RH で補ったわけではない。

    log(squareCell) = oldBudget + birthMass
    oldBudget = Q + C_ns

Q は old-large singleton prime carry、C_ns はその他の correction。
[029](report-029.md) は同一素数底の指数 fiber を連続区間として分類。
[030](report-030.md)–[035](report-035.md) は cofactor window、finite wheel、
least factor、semiprime、prime triple、sqrt roughness を試した。
補完因子を完全に分類すると Q の正確な再計算へ帰着し、
独立な一様上界にはならないという境界が見えた。

[036](report-036.md)–[037](report-037.md) は C_ns の独立 budget を改善。
[038](report-038.md)–[039](report-039.md) は central-binomial compensation
を追い、canonical pooled-threshold 原理が n=27 で偽と証明した。
これは元の central-binomial 不等式の反例ではない。

[040](report-040.md) は first-power gate によって repeated-large mass の
独立上界を真に改善。[041](report-041.md) は prime-base aggregate と
quotient endpoint による簡潔だが緩い上界を与えた。
[042](report-042.md) は Q の prime-only floor-pulse 等式と
cofactor-to-shell-target 単射を証明した。同時に whole-shell target
capacity は全 n>=3 で必要な strict condition に届かないと証明。
Legendre laboratory はここで凍結した。

## 第三幕 — FLT7 の深さ4から27へ（043–051）

既存 ramified fusion には、内部 carrier depth 4 と外側 depth 5、
したがって algebraic な strict drop が存在した。しかし新しい
正の primitive Fermat counterexample は構成されていない。

[043](report-043.md) は missing reconstruction を有限 Fermat chart と同値化。
新しい away root の深さは3であり、既存 inner root を再利用できない。
ideal と第七冪から全 root 座標を一般に復元する decoder も
mu_7 位相のために不可能と形式化した。

[044](report-044.md)–[045](report-045.md) は二枝を nested 49乗形へ：

    c = 7^4*M^7, M = r*s, D = 7^27*r^49
    GN branch: GN_7(D,u) = 7*s^49
    RHS branch: alternatingCyclotomicSeven(u,D-u) = 7*s^49

[046](report-046.md) は threshold 7^161*r^343 の左右で枝を厳密に分離し、
再構成には M>343 が必要と証明、源側の M*N=V*C も固定した。
[047](report-047.md)–[048](report-048.md) は s=1 (mod 7)、
端点六乗 modulo 343、s の modulo r^49 六乗剰余性を証明し、
従来通った実際の有限配分例をさらに排除した。

[049](report-049.md) は旅の合流点だった。両枝を

    P_D(q) = 7*q^6+35*D^2*q^4+21*D^4*q^2+D^6
    P_D(q) = 448*s^49

という一つの中心化六次方程式に統一。狭義単調性、
canonical center/endpoint の一意性、偶奇と primitive 条件を
保持する双方向の逆復元を kernel-check した。

[050](report-050.md) は隣接六乗グノモン差による整数値域排除を証明。
s=t^6, t>=9*r^2 という無限の条件付き族では中心座標が存在しない。
以前の算術フィルターを通る r=1,t=9,M=531441 も除外した。
ただし source から s=t^6 や大小条件は導けていない。

[051](report-051.md) は停止監査。source-only な coprime 配分と既存の
signed center は得られるが、source 側の式は

    P_H(q0)=448*|e|,   H=7^4*|g|

であり、再構成に必要なのは

    P_D(q)=448*s^49,   D=7^27*r^49

である。gap は深さ4対27、標的は e 対 s^49。
ideal/norm/phase/routing にこの二つを結ぶ自然数の
additive seventh-power theorem は見つからなかった。
051 は Outcome C、Lean 追加なしの監査のみで停止。

## 混同してはならない結論

- 有限アンカーの素数存在、carry と budget の正確な等式、
  条件付き無限族の整数値域排除は証明された成果である。
- ルジャンドル予想全体も FLT7 全体も、この PR では解決していない。
- receiver 非存在は元の FLT7 source 非存在を意味しない。
  source が新しい centered witness を必然的に生む橋が未証明である。
- 4<5 は既存の algebraic carrier depth drop であり、
  actual new counterexample への遷移や recursive descent ではない。
- 051 は新しい Lean ビルドなし。050 の4ビルド成功と標準公理の
  保存ログを再確認した。root/facade には従来の研究ファイル由来の
  sorry warnings が残り、リポジトリ全体が sorry-free ではない。

## develop へ持ち帰るもの

完成した定理と、誤っていた容量・補償・再構成の道筋を
反例／no-go／停止境界として併せて保存することが今回の統合目的。

再開は、元の FLT7 source から具体的な正の primitive endpoint と
P_(7^27*r^49)(q)=448*s^49 を source-only に導けるとき、
または source の直接矛盾が得られたとき。その橋がない間は
receiver や新しい番号を増やさぬ。

記録の入口：
[Overview](README.md) /
[001](report-001.md) /
[042](report-042.md) /
[049](report-049.md) /
[050](report-050.md) /
[051](report-051.md) /
[051 audit](evidence/MANIFEST.md#log-7edcc68aab7391dc)。

> この旅は未解決を隠して終わるのではない。
> **未解決の位置を Lean が読める座標に固定して持ち帰る。**
