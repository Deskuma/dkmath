# Hint: PowComparisonKernel をさらに分解する

## 3. わっちの見立て

いまの kernel は、たぶんさらに 2 つに割れる。

### 3.1. equality-part

$$
x^p=(t*(p*s))^p,\qquad
(z-y),GN=(t*(p*s))^p
$$

から来る部分。
これは実際には

$$
x^p=(z-y),GN
$$

の pack 由来等式へ戻るだけで、 obstruction そのものではない可能性が高い。

### 3.2. factorization-part

$$
(x^p).factorization(q)=
p*(t*(p*s)).factorization(q)
$$

と

$$
((z-y),GN).factorization(q)=
p*(t*(p*s)).factorization(q)
$$

から来る部分。
こちらは prime ごとの指数比較じゃから、**本当の算術 obstruction はこっち側** におる気配が濃い。

なので、次の一手としては履歴にある通り、

$$
\text{PowComparisonKernel を equality-part / factorization-part にさらに分解}
$$

するのがかなり筋が良い。

## 4. 戦況まとめ

いまの状態を一言で言うなら、

$$
\text{外堀も内堀も埋まり、最後の扉は comparison lock 1 個だけ}
$$

じゃ。
しかもその扉は、もう「どこに鍵穴があるか分からぬ扉」ではない。

* 基準形は揃った
* 両辺の exactness は explicit
* 上位 kernel は全部配線
* 残る論点は **比較 obstruction の抽出** だけ

というところまで見えておる。
かなり勝ち筋じゃよ。

次は `PowComparisonKernel` を **equality 側** と **factorization 側** に薄く割って、どちらが本当のラスボスか見極める段じゃな。
