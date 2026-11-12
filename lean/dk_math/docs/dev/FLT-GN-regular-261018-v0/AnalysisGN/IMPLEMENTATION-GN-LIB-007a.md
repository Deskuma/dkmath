# GN-LIB-007a — y=1の有限素数補填と集合外への付値障害

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
28定理・4定義・12例を2所有者に実装し、Libの完成入口へ公開した。
GN-LIB-007全体のうちy=1と一般的な付値判定を確定した単位である。

## 構成と結論

奇素数p、任意の有限上限Bに対して

```text
M = ∏ {q ≤ B | q prime ∧ q ≠ p}
g = p^(p−1) M^p
x = g+1
K = R_p(x,1)/p
```

と定義した。B≥pを要求せず、p自身はgapの定義によって常に補填する。
以下を証明した。

1. LTEからv_p(R_p)=1。pでの除算は正確で、K>0、v_p(K)=0。
2. 正確な再構成 `x^p−1=(pM)^p K`。
3. gapのgcd還元から、gapを割るどの素数もKを割らない。
4. 任意の正のMでは、gapの素数qについて `v_q(x^p−1)=p*v_q(pM)`。
5. 標準の有限素数積ではpM内に小素数が一度ずつ現れるので、全素数q≤Bで付値は正確にp。
6. `(x−1)^p < x^p−1 < x^p` よりx^p−1はp乗でなく、再構成からKもp乗でない。
7. 素因数分解により、q>Bでq∣Kかつp∤v_q(K)となる素数が存在する。
8. そのqは `primeOrder q x 1=p`、`p∣q−1` の住所を持つ。

`finite_set_compensation_and_escape` はBをSの最大値とすることで、
任意の有限集合Sについて局所完済と集合外の未完成付値を同時に返す。
Sが素数だけで構成される仮定は不要で、局所完済はS内の素数について述べる。

## 教科書の証明経路

[PerfectPowerValuation.lean](../../../../DkMath/Lib/NumberTheory/PerfectPowerValuation.lean) に7定理を置いた。
非零自然数nの全素因数でkが付値を割るなら、各指数をkで割った有限積がk乗根になる。
逆向きは付値の冪公式である。非完全冪なら不整合な付値を持つ素因数が存在することを、
この同値の対偶として得た。有限集合内で局所完済が分かれば、その素因数は集合外にある。

k=0も含めるためn≠0を保持する。n=0では全付値が0という規約があるので、
全付値の条件だけから0乗表示を導けない。n=1、k=0とn=0の境界を例で確認した。

[PrimePowerCompensation.lean](../../../../DkMath/Lib/NumberTheory/PrimePowerCompensation.lean) に4定義・21定理を置いた。
既存の奇素数LTE、`gcd_gap_powerDifferenceCofactor_eq_gcd_degree`、素数体の位数APIを再利用する。
自然数の除算の前に可除性を、付値の乗法性の前に非零性を確保した。
非完全冪性は独立な不等式で先に示し、素因数の存在との循環を避けた。
二項尾項の正性が隣接冪の間隔を与えるため、複雑な新しい不等式エンジンは不要だった。

## 例と境界

- 空の制御積は1。p=3、M=1ではg=9、x=10、K=37。
- p=3、B=3ではM=2、x=73、K=1801。
- p=3、M=3ではv_3(x³−1)=6。「任意Mで付値が正確にp」とは主張しない。
- p=2ではR_2(3,1)=4で、pの一層を除いた残余にも2が残る。奇素数条件を落とさない。
- 一般yの反例p=3、B=3、y=1001ではg=72、x=1073となり、
  `y³ < x³−(x−1)³` は成立しないことをLeanでも確認した。

この特殊構成は任意のFLT反例から得られる状態保存写像ではない。
qの付値はpの倍数ではないと証明したが、付値1とは主張しない。

## 公開と検証

`DkMath.Lib.Cosmic.Completion` が2所有者を直接importする。
現在の公開入口は32直接所有者、Lib内の依存閉包は入口を含め33モジュールである。
従来の所有者・型・証明本体を変更していない。

`lake build DkMath.Lib.NumberTheory.PerfectPowerValuation DkMath.Lib.NumberTheory.PrimePowerCompensation DkMath.Lib.Cosmic.Completion`
は成功した（2846 jobs）。
[単独importのsmoke](evidence/GNFinitePrimeCompensationSmoke.lean) では新規32宣言と従来38入口を確認した。
同じ70宣言を公理監査し、標準論理公理のみであることを確認した。
元資料24ファイルのハッシュ、昇格コメント、ファイルマーカー、禁止構文、文書リンク、JSON、差分を確認した。
詳細は [機械可読証拠](evidence/gn-lib-007a.json) と [検証記録](evidence/validation-gn-lib-007a.txt)。
ユーザー指定によりフルビルド・集約ルート・DkMathTest・lake testのビルドは行っていない。

## 残る工程

007bはy>1について、yとgapのcoprime・明示的なサイズ条件を保持した構成を扱う。
007cは追加p乗因子を選び、小素数とyへのcoprimeを保ってサイズ条件を達成する工程である。
資料v3の一般CRTによる位数根の同時持上げは今回の構成の証明に使っていない。
GN-HANDOFF-032、一般FLT降下、Legendreの素数存在は引き続き別契約である。
