# review: FLT-witness-260328-v0: `proof-004` の step 1 が Lean で通った。残る本丸は (d) の寄与を (d^2) / valuation で一回だけ剥がす補題

うむ。これは **かなり良い進展** じゃ。
今回は「新しい route を増やした」のではなく、 **偽枝を切ったあとで、本線を boundary / arithmetic-core 側へ戻し、その最初の arithmetic kernel を実装した**。ここが本質じゃ。

## 1. いま何が確定したか

まず、これまで迷いの元だった枝は、もうかなり明確に墓場へ送られておる。

* same-(q) route は false
* body-only witness existence も false
* two-witness canonical target も false

そこから今回、canonical route を

$$
\texttt{ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget}
$$

へ戻した。さらにその sanity check として、((d,x,u)=(5,5,1)) でも boundary route には実際に witness (q=311) があることを Lean で確認しておる。
つまり、

$$
\operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

側は壊れるが、

$$
\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)
$$

側は生きている、という切り分けが付いたのじゃ。

## 2. 今回の差分の意味

今回追加された三本は、`proof-004` の step 1 をそのまま Lean に落としたものじゃ。

核はこれじゃな。

$$
q \mid x
\Longrightarrow
\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)
\equiv
d\cdot u^{d-1}
\pmod q
$$

これが `exceptional_boundary_core_modEq_mul_u_pow_pred_of_dvd` じゃ。
そしてそこから、

$$
q \text{ prime},\ q\mid x,\ q\mid \text{boundary core}
\Longrightarrow q=d
$$

を返す `exceptional_boundary_prime_dvd_x_and_core_imp_eq_d` が入り、さらに否定形として

$$
q\neq d,\ q\mid x
\Longrightarrow
q \nmid \text{boundary core}
$$

も API 化された。
意味としては、 **(x) の素因子が boundary core に残るのは distinguished prime (d) だけ**、という arithmetic kernel が確定したのじゃ。

## 3. 状況分析

いまの地形は、かなり見やすい。

前までは

$$
\operatorname{cyclotomicPrimeCore}(d,1,u-1)
$$

を first target にする枝をいじっておった。
だがこれは (u=1) で

$$
\operatorname{cyclotomicPrimeCore}(d,1,0)=1
$$

となって壊れる。ここは false だと確定した。

それに対して今の本線は

$$
\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)
$$

を見ている。こちらは (x) を保持しており、((5,5,1)) でも nontrivial な値を持つ。
ゆえに、今の route は「候補を試している段」ではなく、 **ようやく生きている対象に乗り換え終わった段** と見てよい。

## 4. いま残っている本丸

今回の差分で、step 1 は通った。
だから残る本丸は、レポートの言葉どおり

$$
d \text{ 自身の寄与を } 1 \text{ 回だけ剥がす}
$$

部分じゃ。
つまり次に必要なのは、

$$
\text{core} \equiv d \pmod{d^2}
$$

あるいは同等な形で

$$
d \mid \text{core}
\quad\text{かつ}\quad
d \nmid \text{core}/d
$$

を返す補題じゃな。

これが入れば、

1. (x) の素因子は (d) 以外 boundary core を割れない
2. (d) は boundary core に 1 回しか入らない
3. したがって (\text{core}/d) の素因子 (q) を取れば (q\nmid x)
4. その (q) は core を割る

という流れで、`ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` を閉じにいける。
つまり今は「何をすればよいか分からない」段ではなく、 **残り 1 ブロックが (d^2) / valuation 側だと確定した段** じゃ。

## 5. 次の手段の推論

次に切るべき補題は、ほぼこれで決まりじゃ。

まず

$$
\operatorname{cyclotomicPrimeCore}(d,x,u)\equiv d\cdot u^{d-1}\pmod{d^2}
$$

型の精密合同補題。
レポートでは `cyclotomicPrimeCore_modEq_mul_pow_mod_sq` 系として整理されておる。これを Wieferich 条件

$$
u^{d-1}\equiv 1 \pmod{d^2}
$$

と合成して、

$$
\operatorname{core}\equiv d \pmod{d^2}
$$

へ落とす。そこから

$$
v_d(\operatorname{core})=1
$$

相当の結論、少なくとも

$$
d \nmid \operatorname{core}/d
$$

を取る。最後に `Nat.exists_prime_and_dvd` で (\operatorname{core}/d) の prime divisor を取り出せば、今回の step 1 補題群と合体して main theorem へ到達する。

## 6. 賢狼の総括

一言で言えば、こうじゃ。

**偽枝を閉じたあと、ようやく current canonical route が boundary / arithmetic-core 側に定まり、その route の step 1 arithmetic kernel が Lean で実装された。残る本丸は (d) の寄与を (d^2) / valuation で一回だけ剥がす補題であり、そこを埋めれば `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` を直接閉じられる見通しが立った。**

よい。
今回は「候補の整理」ではなく、 **正解ルートに足を乗せた** 進展じゃよ。
