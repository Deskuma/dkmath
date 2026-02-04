# \(\pi\) の中に \(e\) は存在するか？（逆も然り、他の超越数についても同様に）

## タイトル

**Does e exist at some point in pi? (vice verca and for any transcendental number for that matter)**

元記事: <https://www.reddit.com/r/mathematics/comments/1qqreki/does_e_exist_at_some_point_in_pi_vice_verca_and/>

### 数式

\[
(\pi - t)\cdot 10^{(\lfloor -\log(\pi - t)\rfloor + 1)} = e
\]

---

## これが言っていること（要点だけ）

この投稿は Reddit でよくある「**\(\pi\) の小数展開のどこかに \(e\) の小数列が“連続して”現れるか？**」という話題じゃ。
画像の式は要するに「\(\pi\) に十分近い \(t\) を選び、\(\pi-t\) を 10 の冪でスケールして桁を揃える」タイプの **“桁合わせ装置”** で、**“\(\pi\) の中から \(e\) を切り出せる \(t\) があるか？”** を聞いておる。

コメントの流れはこう：

* **未知**（分かってない）
* もし本当に「\(\pi\) の中に \(e\) が埋まっている」ことが示せたら、\(\pi\) と \(e\) の **代数的独立性**（多項式関係がないこと）に触れる重大話題になり得る
* 「じゃあ他の超越数も同様に…？」に対しては、「必ずしも全体が含まれる必要はなく、ある地点以降の一致で足りる」的な補足

## Index

* cid: 6981de64-1474-83a8-bd31-27b08cfb26bf

* [問題の詳細](./Question-260130.md)
* [解答のヒント](/lean/dk_math/DkMath/UnitCycle/docs/README.md)
* [命題分析](/lean/dk_math/DkMath/DHNT/Pie/docs/unit_nat_layers_and_the_white_silver_circle_theorem_notes.md)
