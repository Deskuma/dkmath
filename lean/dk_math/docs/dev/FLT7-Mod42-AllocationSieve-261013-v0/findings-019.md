# findings-019 — scalar ledger と actual source の分離

2026-10-14。Outcome B。M 単独の新しい制約は得られなかった。補根については source 固有の N>1 を test-only theorem として検証した。

## スカラーモデル

M=29²=841、N=1、V=M、C=1 の正値、M*N=V*C、Coprime M N、Coprime V C、7∤M、7∤N を Lean decide で確認した。任意 prime ℓ∣841 は、素数の冪整除と prime29 の整除分類からℓ=29になる。Nat.Coprime 7 (29−1) は不成立なので、この M には gate016 の prime/support 条件を全て満たす素因子が存在しない。

これは提示された scalar ledger だけから usable prime を強制できないことの例である。gate016/018 の反例、actual packet、source norm identities のモデル、exact receiver、FLT7 counterexample ではない。

## source 固有の分離結果

actual K と A=K.quadratic.innerRoot.fst、B=K.quadratic.innerRoot.snd に対し、source は A≠0、B≠0、A+B≠0 を供給する。complementary root は |seventhPowerSndCore(A,B)|=N^7 を満たす。

N=1 とすると cubic factorization より |leftCubic(A,B)|=|rightCubic(A,B)|=1。それぞれの整数値は±1となる。その差は0または±2だが、既存 polynomial identity は差=7*A*B*(A+B) を与えるので7の倍数でもある。従って差=0、A*B*(A+B)=0となり source の非零性に矛盾する。

これを `sourceComplement_ne_one` と、実際の p から witness を抽出する `actualSourceComplement_gt_one` に形式化した。追加の hrec や arbitrary endpoint を使わない。前者の hN は actual complementary theorem の結論であり、後者では p のデータから取得している。

指定モデルの N=1 は、この source cubic-coordinate relation を実現できない。従って scalar ledger が全 source を記述するとは言えない。ただし M=841 自体の排除は証明していない。他の N,V,C や座標を伴う source が存在するとも主張しない。

N>1 と source ledger/positivity から相対的に M<V*C とは推論できる。しかし V*C の独立した上限はなく、M の許される数値・素因子・cofactor を分類しない。これは source tuple を区別する狭い結果であり、M 単独の新しい restriction として Outcome A に数えていない。

## 独立 source 条件の棚卸し

二次 norm A²+A*B+2B²=residualNormRoot、IsCoprime A B、signed B=7^4*m^7（M=|m|）、三次 norm の signed seventh powers、signedRootGap の整数式、ramified/normalized axis difference と exact theta depth13 を確認した。これらは scalar ledger に入っていない実際の座標・ring 条件である。

root/axis factorization は同じ m を含むが、既存の coprime splitting と associated powers から M の prime種類、valuation parity、cofactor≤343 を与える宣言は今回の targeted audit で確認できなかった。oriented carrier valuation は主に Q=quotientRoot の prime support/valuation と degree-six ideals を扱う。Q≠M の混同は避け、source normalizedEquation の連結が存在することも確認したが、Q=M という同定や係数上限は得ていない。

[ source-constraint-frontier-019.md ](source-constraint-frontier-019.md) に必要仮定と対象を分けた matrix を記録した。全 source が数論的に不十分だという独立性の定理は主張していない。

## 結論と検証

既存 source の正値と7-unit以外から、gate016 に必要な actual M=c*ℓ^n、c≤343、usable prime条件を導けていない。単なる素数付値保存の言い換えを追加せず、production は変更していない。

DkMathTest calibration 初回と第2回は inexistence of Nat.mul_eq_one_iff / Nat.mul_eq_one により各 exit 1。実際の global mul_eq_one に修正して exit 0。最終 test module の focused Lake build は exit 0、9088 jobs、警告なし。5 named theorem の公理は scalar decide が propext のみ、他4つは propext、Classical.choice、Quot.sound。sorryAx なし。

ここで戦略を一旦区切り、source の同時 Diophantine 条件から M を制約する独立した elimination/inequality が得られる経路かを再評価することを提案する。さらに弱い sieve gate を自動追加することは提案しない。020 には進まない。
