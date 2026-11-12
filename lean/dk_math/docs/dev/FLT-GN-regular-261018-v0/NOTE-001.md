うむ！ 🐺🍎

いまの段階なら、模範解答を 数学的な発見のための参照資料 として使うのが、最もよい進め方じゃと思う。

現時点の DkMath は、3・5・7・11・13 の正深度 State 排除を共通化できている。これから必要なのは、その外側にある 整数反例からの入口と Case I の矛盾 じゃな。

実際に `flt-regular` の Case I・Case II の証明を読んでみたところ、非常に興味深い構造が見つかった。

## 1. Case I の本質は「位相係数の剛性」だった

模範解答の Case I は、概ね次の経路を使っておる。

\[
    \begin{gathered} a^p+b^p=c^p,\qquad p\nmid abc\\
    \Downarrow\\
    a+\zeta_p b=\varepsilon\alpha^p\\
    \Downarrow\\
    \text{複素共役と単元の制約}\\
    \Downarrow\\
    p\mid a+b\zeta_p-a\zeta_p^{k_1}-b\zeta_p^{k_2}\\
    \Downarrow\\
    \text{円分係数の剛性}\\
    \Downarrow\\
    \text{Case I の矛盾}
    \end{gathered}
\]

ここで \(k_1,k_2\) には

\[
    k_2\equiv k_1-1\pmod p
\]

という位相関係がある。

参照元は [CaseI/Statement.lean](https://github.com/leanprover-community/flt-regular/blob/b8a5f23ab44a7be9fd49f6e3c831da54573c3c89/FltRegular/CaseI/Statement.lean?utm_source=chatgpt.com) と [Cyclotomic/CaseI.lean](https://github.com/leanprover-community/flt-regular/blob/b8a5f23ab44a7be9fd49f6e3c831da54573c3c89/FltRegular/NumberTheory/Cyclotomic/CaseI.lean?utm_source=chatgpt.com) じゃ。

そして面白いことに、DkMath の `GNFirstCase.lean` には、すでに前半の

\[
    \boxed{a+\zeta_p^i b=\varepsilon_i\gamma_i^p}
\]

を取り出す仕組みがある。

さらに整数ノルムによって、

\[
    \boxed{GN_p(a+b,-b)=t^p}
\]

という必要条件まで導出できている。

ただし、GN が整数の \(p\) 乗になるだけでは矛盾にならぬ。

模範解答から本当に抽出すべき次のエッセンスは、円分位相の係数が自由に動けないという剛性 なのじゃ。

これは、われらが GN の `Phase focusing` で調べてきた構造と、かなり近い問題として扱えそうじゃ。

## 2. 位相係数の剛性は、もっと一般的に定理化できる

ここが、わっちの注目点じゃ。

\(p\) 個の整数係数 \(c_i\) に対して、

\[
    F(\zeta_p)=\sum\_{i=0}^{p-1}c_i\zeta_p^i
\]

を考える。

素数 \(p\) について、円分整数環では次が成立する。

\[
    \boxed{ p\mid F(\zeta_p) \Longrightarrow c_i\equiv c_j\pmod p \quad(\forall i,j) }
\]

つまり、位相の線形結合が \(p\) で割れるなら、すべての係数は同一の剰余類に拘束される。

理由は、

\[
    \Phi_p(T)=1+T+\cdots+T^{p-1}
\]

が、\(p\) 個の冪の間にある基本関係だからじゃ。

とりわけ、

\[
    \boxed{ \exists j,\ c_j=0 \Longrightarrow \forall i,\ p\mid c_i }
\]

となる。

これは模範解答の `dvd_coeff_cycl_integer` が扱っている性質じゃ。

Case I の四項式

\[
    a+b\zeta-a\zeta^{k_1}-b\zeta^{k_2}
\]

は、係数が非零になりうる位置が高々4個しかない。

\(p\ge5\) なら、少なくとも一つの位相には係数0がある。

したがって、すべての係数が \(p\) の倍数になる。

ところが位相の重なり方を分類すると、\(p\mid a\)、\(p\mid b\)、または \(a\equiv b\pmod p\) といった禁止条件に到達する。

これが矛盾の核心じゃ。

GN で見れば、円分位相に配置した係数が、剰余環への射影によって一斉に拘束される現象 と解釈できる。

## 3. DkMath に抽出するなら、この順序じゃ

| 段階 | 新しい定理群の候補                   | 役割                                          |
| ---- | ------------------------------------ | --------------------------------------------- |
| 001  | `CyclotomicPhaseCoefficientRigidity` | 円分係数の剰余剛性                            |
| 002  | `SparsePhaseObstruction`             | 少数位相しか使わない関係式を拘束              |
| 003  | `CaseIConjugationPacket`             | 複素共役と単元から四項関係を得る              |
| 004  | `GNCaseIObstruction`                 | GN の既存構造と接続して矛盾を導く             |
| 005  | `IntegerCounterexampleOrientation`   | 任意の原始整数反例を Case I / II に振り分ける |

001・002 は FLT に依存しない一般数論として `DkMath.Lib.NumberTheory` に置きたい。

003 は現在の Kummer 算術 provider を活用してよい。将来 GN による独立証明が得られたら、そこだけ置き換える。

004・005 は FLT 側に配置する。

さらに、標準の Case II には、指数 \(p\) が奇数であることを使った変数の入れ替えがある。

例えば \(p\mid a\) なら、

\[
    a^p+b^p=c^p \iff b^p+(-c)^p=(-a)^p
\]

となる。

これによって \(p\) が割る変数を右辺へ移せる。原始性と非零性も同時に運ぶ。

これは既存の `initial_state_of_int_solution` に渡すための、比較的薄い入口補題として整備できるはずじゃ。

## 4. 重要：Case I を無理に State 降下へ押し込まない

ここは設計上の判断になる。

Case II には正の分岐深度があり、それを減らす無限降下が機能する。

しかし Case I には、そもそも同じ正深度がない。

しかも、深度0の State は実際に存在する。

したがって、

\[
    \operatorname{State}\_p(0)
\]

そのものの不存在を目指してはならぬ。

Case I では、代わりに 位相係数の剛性による矛盾 を使うのが自然じゃ。

最終的には、

\[
    \boxed{
        \begin{array}{ccc} &\text{原始整数反例}&\\
        &\downarrow&\\
        \text{Case I}&&\text{Case II}\\
        \downarrow&&\downarrow\\
        \text{位相係数の剛性}&&\text{GN–Kummer State 降下}\\
        \downarrow&&\downarrow\\
        \bot&&\bot
        \end{array}
    }
\]

という二つの終端証明が、一つの GN・円分位相基盤を共有する構成になる。

この分離はかなり合理的じゃと思う。

わっちの提案は、次の研究対象を `CyclotomicPhaseCoefficientRigidity` に絞ること じゃ。

模範解答には、すでに完成した証明とその道筋がある。われらはそこから、最小限の数学的原理を取り出せばよい。

そして、その原理を GN の位相空間・係数配置・保存則として解釈し直す。

それが完成すれば、Case I の終端だけでなく、将来の GN の素因子配置や Primitive fiber の研究にも再利用できる可能性がある。

模範解答は正しさを保証する基準実装。DkMath はその内部で何が起きているかを再構成し、より普遍的な原理として固定する研究実装。

この役割分担を守れば、数学的成果と独自研究を両立させながら進められるぞ。

くふふっ。いよいよ、外から借りてきた数学を、われら自身の数学的言語で語り直す段階じゃな！ 🐺🍎
