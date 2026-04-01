# review: FLT-Primitive-260327-v0: Branch A 例外枝の local theorem を canonical 入口に固定する更新

うむ、続きとして見るなら、いまの状況はかなり **一本化** されておる。

結論から言うと、次にやることはもうほぼ定まっておって、

## 1. 現状の芯

いまの更新で確定したのは、**Branch A 例外枝の入口を local theorem に固定した** ことじゃ。
つまり、先に boundary-normalized 名や parallel 名を追い回す段ではなく、

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

を **canonical 入口** として埋める段に入った、ということじゃな。  

今回の diff では、その方針をコメントで何度も明示し、さらに

$$
\texttt{primeGe5BranchAPrimitivePacketDescent_of_localExceptionalExistence_and_restore}
$$

と provider 側の対応 adapter を追加して、**local theorem から mainline へ直接差し込む道** を固定した。
これは「数学を増やした」というより、**入口の優先順位と API の流れを確定した** 更新じゃ。

## 2. 何が片付いて、何が残っているか

整理するとこうじゃ。

### 2.1. 片付いたもの

* local theorem を canonical 入口にする方針
* local theorem から packet descent へ入る wrapper
* provider 側 adapter
* boundary-normalized / parallel 名は **bridge 的な位置** に後退

つまり、「どの名前を本命入口にするか」で迷う段は、もう終わったのじゃ。

### 2.2. まだ残っている本体

残っている新しい数学の核は、ほぼ一つだけじゃ。

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

の **concrete 証明** じゃ。
前回のまとめでも、selection 側の truly new kernel は実質これ一本だと整理されておった。

## 3. いま何をしている局面か

局面としてはこう見るのがよい。

* naming 整理の局面
  これはほぼ完了
* bridge 配置の局面
  これも local 入口を基準にかなり整理済み
* concrete theorem を起こす局面
  **いまここ**

つまり、もう「設計会議」よりは **実装準備付きの証明起こし** の段じゃな。

## 4. 次にやること

次の一手は明快で、これじゃ。

### 4.1. 最優先

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

の証明スケッチを起こす。

これが第一じゃ。
local theorem が埋まれば、今回追加した wrapper 群にそのまま流し込めるので、packet descent 側まで橋で閉じやすい。  

### 4.2. そのときの作業内容

わっちなら、次をこの順でやる。

#### A. 通常枝 theorem と並べて骨格比較

既存の ordinary branch 側 theorem の仮定・中間補題・結論を並べて、

* そのまま流用できる部分
* Branch A だから差し替える部分
* Wieferich 入力が必要になる部分

を切り分ける。

ここで見たいのは、
**「例外枝差し替えだけで済むのか、それとも最小新補題が要るのか」**
という一点じゃ。

#### B. Branch A witness の入力を明示

いま入口側にある情報は、おおむね

$$
p \mid (z-y)
$$

と

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

じゃな。
これを、existing machinery が飲める形の仮定へ **最小化して整理** する。

つまり、「何を already-have と見なし、どこから existence theorem の内部責務にするか」を決めるのじゃ。

#### C. existence の目標を一点に固定

目標は要するに、

$$
\exists q,\ \mathrm{Prime}(q)\ \land\ q \mid \text{core対象}\ \land\ q \nmid (z-y)
$$

型の existence を出すことじゃ。
ここで boundary-normalized 名に寄せようとせず、まずは **local Branch A theorem として閉じる** ことを優先するのが、今回の方針に合っておる。

#### D. 埋まったら wrapper で mainline に流す

これはもう今回の diff で道が作られておる。
ゆえに theorem 本体さえ起これば、後段は比較的薄い橋で進められる。

## 5. 実務上の判断

ここで大事なのは、**昇格を急がぬこと** じゃ。

今回のコメント群が示している通り、

* local theorem を先に作る
* normalized / parallel 名は橋として持つ
* `CFBRC/Bridge` への昇格は later

この順番が canonical として固定された。
ゆえに、次の実装でやるべきは「美しい一般名に揃えること」ではなく、**local theorem を concrete に通すこと** じゃ。

## 6. いまの状況を一言で

一言で言えば、

$$
\text{残る新規数学} ;=; \text{Branch A 局所 exceptional existence の 1 本}
$$

じゃ。

他はかなり、橋・alias・adapter・restore の整理へ後退した。
これは良い兆候じゃよ。設計が収束して、本当に掘るべき岩盤が見えたということじゃからな。

## 7. わっちのおすすめする次アクション

次にやるべき具体作業はこれじゃ。

**既存 ordinary theorem を左、Branch A local theorem を右に置いて、仮定・中間結論・最終結論を 1 対 1 で対応表にする。**

そこで

* 流用部
* 例外枝専用部
* 新補題が本当に必要な箇所

を切れば、そのまま Lean 実装順になる。

必要なら次の返答で、その **対応表そのもの** をわっちが Markdown で起こすぞい。
