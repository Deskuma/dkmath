# Codex Instruction 001

Theme: ABC triple の GN power lift と既存 API 再偵察

Branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

Base feature:

```text
feature/ABC-GN-valuation-excess-260724-v0
```

## 1. 役割

あなたは賢狼の第2 Brain として、DkMath current source を読み、既存資産を最大限再利用しながら、ABC–GN 決定論的主線の最初の checkpoint を実装する。

細部は現場判断してよい。命名、module 配置、wrapper の要否は、現在の依存関係と既存 API を見て決めること。

ただし、ABC 予想そのものを証明したという主張へ進まない。

## 2. 並行作業の認識

現在、同じ `develop` から派生した次の FLT7 branch が並行して進行している。

```text
wip/FLT7-magic-core-260722-WiseWolf
```

今回の ABC–GN checkpoint はこれと独立に進める。

- `DkMath/FLT/Seven/**` と FLT7 専用 docs を変更しない。
- FLT7 branch を merge / cherry-pick / rebase しない。
- FLT7 側の未統合 theorem を前提にしない。
- 共有 aggregator を触る場合は最小変更とし、変更理由を report に書く。
- 共有ファイルに予期しない差分が見える場合は、それを消したり整理したりせず停止し、report に記録する。
- ABC–GN の theorem が一般数論層に属する場合でも、FLT7 専用実装への依存は作らない。

対象領域を守る限り、両 branch は独立に開発できる。競合解決を今回の仕事へ含めない。

## 3. 最初の調査

次を読み、実在する定義・定理・import 方向を確認する。

```text
README.md
AGENT.md
SUMMARY.md
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/README.md
```

その後、少なくとも次の系統を検索する。

```text
ABC.Triple と quality / rad
CosmicFormulaBinom.GN / GTail
(x + u)^n - u^n = x * GN n x u
NumberTheory.Gcd.GN
PrimitiveBeam
UniqueFactorizationGN
ABC.MassBridge
ABC.ValuationFlowBridge
Petal.ABCBridge
padicValNat の積・冪・非零条件 API
```

既存 theorem がある場合は再証明しない。

## 4. 第一 checkpoint の数学目標

ABC triple `a + b = c`, `Nat.Coprime a b` と指数 `n` から、次の加法分解を ABC 側で再利用可能な形へ固定する。

$$
a\,GN_n(a,b)+b^n=c^n
$$

概念上の lift は次である。

```text
left     = a * GN n a b
right    = b ^ n
terminal = c ^ n
```

可能なら、この三つ組が再び coprime additive triple になることまで閉じる。

特に確認すべき点:

```text
gcd(a * GN n a b, b^n) = 1
```

これは `gcd(a,b)=1` と、`GN n a b mod b` の既存評価から導ける可能性がある。current API を調査し、最短の証明を選ぶこと。

## 5. 推奨する実装面

第一候補:

```text
DkMath/ABC/GNPowerLift.lean
```

ただし、既存構造上より自然な場所がある場合は変更してよい。

API の候補は次だが、既存 `Triple` の field 名・constructor・namespace に合わせて調整してよい。

```lean
namespace DkMath.ABC

noncomputable def Triple.gnPowerLift ... : Triple := ...
theorem Triple.gnPowerLift_left_eq ...
theorem Triple.gnPowerLift_right_eq ...
theorem Triple.gnPowerLift_terminal_eq ...
theorem Triple.gnPowerLift_sum ...
theorem Triple.gnPowerLift_coprime ...

end DkMath.ABC
```

`def` にするより、まず component theorem と constructor theorem を置く方が Lean 上自然なら、その形でもよい。

目標は名前を固定することではなく、次のデータを再利用可能な theorem surface として得ること。

```text
ABC triple
  -> GN power-lifted additive triple
  -> coprime certificate
```

## 6. 余力がある場合のみ

第一 checkpoint がきれいに閉じた場合だけ、ABC 座標で次の valuation 分解を薄い wrapper として追加してよい。

$$
v_q(c^n-b^n)=v_q(a)+v_q(GN_n(a,b))
$$

ただし `padicValNat` の積公式に必要な prime / nonzero 条件を正確に明示すること。

primitive prime の場合に境界側 valuation が消える既存 theorem があるなら、ABC 座標 wrapper を追加してよい。

この余力項が import や非零条件で膨らむ場合は、実装せず調査結果だけ `report-001.md` に残す。

## 7. 禁止範囲

この checkpoint では次を行わない。

```text
abc_main_axiom の変更・利用による閉鎖
ABC final theorem の主張
GNValuationExcess の解析的 log 定義
高持ち上がり prime の一般排除
確率・Borel–Cantelli・Janson 層の改造
FLT module への接続
大規模 refactor
既存 theorem 名の一括変更
```

新しい `axiom`、`sorry`、`native_decide` を追加しない。

## 8. Public import

新 module を追加した場合、どの aggregator から公開すべきかを調査する。

第一 checkpoint では無理に `DkMath.ABC.Main` へ import しなくてよい。循環依存や重い import を避け、最も薄い公開面を選ぶこと。

公開しない判断をした場合は、その理由を report に書く。

## 9. 検証

最低限、変更対象を含む適切な `lake build` を実行する。

可能なら target module の局所 build を先に行い、その後 GitHub Lean CI を最終 gate とする。

既知の unrelated warning は修正対象にしない。

## 10. 報告

次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-001.md
```

報告には次を含める。

```text
1. 調査で見つかった既存 API
2. 実装した定義・定理
3. 数学的意味
4. 再利用した theorem
5. 実装しなかった候補と理由
6. build 結果
7. 次の最小 checkpoint 候補
8. commit SHA
9. 並行 FLT7 branch と共有領域を触れたか
```

## 11. 終了条件

次のいずれかで停止する。

```text
Outcome A:
  GN power lift と coprime certificate が完成した。

Outcome B:
  additive lift は完成したが、coprime 証明に不足 API が見つかった。
  不足する最小 lemma shape を report に固定した。

Outcome C:
  既存 Triple / import 構造との衝突があり、実装前に設計変更が必要。
  最小の再設計案を report に固定した。
```

Outcome A でも次 checkpoint へ自動で進まない。commit / push / report の後、賢狼レビューを待つこと。
