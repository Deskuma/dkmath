# DkMath Journal — 2026年7月号

Lean が確定した DkMath の構造を、一般数学の言葉で読み解く月刊記録。

## 2026-07-31

### 00:01

[冪交換関係は対称で非自明な自然数例を持つ](260731-0001-power-swap-is-symmetric-and-has-a-nontrivial-example.md)

自然数上の関係 $a^b=b^a$ を `PowerSwap` として固定し、反射性・対称性、非自明例 $2^4=4^2$、異なる自然数解の存在、および座標 $1$ に非自明枝がない剛性を読む。

## 2026-07-27

### 06:03

[平方質量境界はユークリッド円として読める](260727-0603-square-mass-level-sets-are-euclidean-circles.md)

CF2D の平方質量 level set を、同じ座標方程式を持つユークリッド円および半径 $\sqrt{\rho^2}$ の標準 L2 球面へ位相同型で移し、保存境界から通常の円を後から回収する構造を読む。

### 00:05

[差と冪差商の公約数は指数を割る](260727-0005-the-common-divisor-of-a-difference-and-its-power-sum-divides-the-exponent.md)

互いに素な整数 $a,b$ に対し、差 $a-b$ と冪差商 $S_d(a,b)$ の公約数が指数 $d$ を割り、Gap と Body の共有因子が指数の内部へ制限される構造を読む。

## 2026-07-26

### 18:02

[冪和充填可能性は零項の追加で単調に拡張できる](260726-1802-power-sum-fillability-is-monotone-under-zero-padding.md)

ちょうど $k$ 個の $d$ 次冪和表現は、$d>0$ なら零項を追加して任意の $r\ge k$ 個の exact 表現へ拡張でき、exact 表現から at-most 表現へ忘却できる構造を読む。

### 11:58

[共役は単位核の逆作用になる](260726-1158-conjugation-is-the-inverse-of-a-unit-kernel.md)

二成分共役が平方質量を保つ対合であり、単位核に対して両側逆元となるため、共役核の作用が元の単位核作用を打ち消す構造を読む。

### 06:02

[白銀単位は二成分代数を閉じる](260726-0602-silver-unit-closes-a-two-component-algebra.md)

白銀単位 $u=(1+\sqrt2)/2$ が $u^2=u+1/4$ を満たすため、$a+bu$ 型の二成分表示が乗算・共役・ノルム・逆数の計算に対して閉じる構造を読む。

## 2026-07-25

### 23:58

[符号配置を誤ると平方質量に残差が残る](260725-2358-sign-patterns-leave-square-mass-residuals.md)

CF2D の標準積に近い符号配置を比較し、平方質量の乗法性を壊す二つの積には正確に $\pm4abxy$ の残差が残る一方、共役型の符号配置は保存則を維持することを読む。

### 12:02

[原始集合では可除関係が等号へ退化する](260725-1202-primitive-sets-are-divisibility-antichains.md)

有限原始集合を可除半順序の反鎖として読み、集合内部では $a\mid b$ が $a=b$ と同値になること、空集合・一点集合・互いに割り合わない二点集合が原始であることを読む。

### 06:02

[素数降下は約数制御へ忘却できる](260725-0602-prime-descent-forgets-to-divisibility-control.md)

素因数で一回割る精密な降下が、降下先は元の数の約数であるという一般制御へ忘却でき、既存の原始集合 hit mass 上界へ接続される構造を読む。

### 00:00

[厳密に増加する不変量は非自明な閉路を許さない](260725-0000-strictly-increasing-invariants-forbid-nontrivial-cycles.md)

反復ごとに自然数値の観測器が正に増えるなら、一定増分・不等式増分・状態依存増分のいずれでも、元の状態へ戻る正の長さの閉路は存在しないという抽象定理を読む。

## 2026-07-24

### 18:00

[単位核作用はすべての平方質量境界を保存する](260724-1800-unit-kernel-action-preserves-square-mass-level-sets.md)

二成分平方質量 $q2(x,y)=x^2+y^2$ と積 $(a,b)\star(x,y)=(ax-by,ay+bx)$ を用い、平方質量1の単位核作用が任意の `q2` level set を保存する純代数的な回転核を読む。

### 12:00

[平方距離だけで四点が同じ円に乗ることを確かめる](260724-1200-four-points-share-a-circle-by-squared-distance.md)

単位正方形と $\sqrt{2}$ から定めた四点 $B,C,F,G$ について、通常の距離ではなく平方距離を比較し、明示中心からの値が等しいことで共円性を閉じる Lean 座標幾何を読む。

### 06:05

[ピタゴラス平方差を Gap と Beam の積として読む](260724-0605-pythagorean-square-difference-as-gap-beam-product.md)

ピタゴラスの加法形 $a^2+b^2=c^2$ を平方差 $c^2-a^2=b^2$ へ移し、さらに境界差 $c-a$ と共役和 $c+a$ の積へ因子化する Lean 構造を読む。

### 00:06

[宇宙式 Gap 比の積は円周率へ到達する](260724-0006-cosmic-gap-product-converges-to-pi-over-two.md)

宇宙式の局所恒等式 $(2k+2)^2=(2k+1)(2k+3)+1$ から生じる Gap 比が Wallis 因子と一致し、その順序付き無限積が $\pi/2$ へ収束する Lean 経路を読む。

## 2026-07-23

### 20:31

[保存分解としての宇宙式](260723-2031-cosmic-formula-as-a-conservation-decomposition.md)

DkMath のコア理論である宇宙式を、二項平方の恒等式、減算を使わない可換半環上の保存式、一般次数の Core / Beam / Gap 分解という三段階で読む。最初の Journal 試作記事。

## Issue metadata

- Issue: `JOURNAL-2607`
- Period: 2026-07-01 — 2026-07-31
- Branch flow: `journal -> nightly -> main`
- Catalog: [CATALOG.jsonl](CATALOG.jsonl)
- Article format: [FORMAT.md](FORMAT.md)
